/**
Checked integer arithmetic operations, functions, and types with improved handling of errors and corner cases compared
to the basic integral types.

Copyright: Copyright Thomas Stuart Bockman 2015
License: $(LINK2 http://www.boost.org/LICENSE_1_0.txt, Boost License 1.0).
Authors: Thomas Stuart Bockman

$(BIG $(B Problems solved by `checkedint`)) $(BR)
As in many other programming languages (C, C++, Java, etc.) D's basic integral types (such as `int` or `ulong`) are
surprisingly difficult to use correctly, due to variuos departures from the behaviour of ideal mathematical integers:
$(UL
    $(LI Overflow silently wraps around: `assert(uint.max + 1 == 0);`)
    $(LI Mixed signed/unsigned comparisons give the wrong result if the signed value is negative: `assert(-1 > 1u);`)
    $(LI Mixed signed/unsigned arithmetic operations also give the wrong result for some inputs.)
    $(LI Integer division by zero crashes the program with a mis-named and uncatchable `Floating Point Exception`
        (FPE).)
    $(LI `int.min / -1` and `int.min % -1` likewise crash with an FPE, even though the latter should simply yield `0`.)
    $(LI If `x` is any integer value, and `y` is any negative integer value, `x ^^ y` will crash with an FPE.)
    $(LI No bounds checking is done when casting from one integer type to another.)
    $(LI The result of the bitshift operations (`<<`, `>>`, `>>>`) is formally undefined if the shift size is less than
        zero or greater than `(8 * N.sizeof) - 1`.)
)
The `checkedint` package offers solutions to all of these issues and more.

$(BIG $(B `SafeInt` versus `SmartInt`)) $(BR)
Two different approaches are available:
$(UL
    $(LI `SafeInt` and `safeOp` strive to match the behaviour of the basic integral types exactly, $(B except) that
        where the behaviour of the basic type is wrong, or very unintuitive, an error is signaled instead.)
    $(LI `SmartInt` and `smartOp` strive to actually give the mathematically correct answer whenever possible, rather
        than just signaling an error.)
)
There is no meaningful performance difference between `SafeInt` and `SmartInt`. For general use, choose `SmartInt` to
simplify your code and maximize the range of inputs it accepts.

`SafeInt` is intended mainly as a debugging tool, to help identify problems in code that must also work correctly with the basic
integral types. The `DebugInt` `template` `alias` makes it simple to use of `SafeInt` in debug builds, and raw basic types in release builds.

$(TABLE
    $(TR $(TD)                $(TH `int` (basic type)) $(TH `SafeInt!int`)          $(TH `SmartInt!int`))
    $(TR $(TH `int.max + 1`)  $(TD `0`)              $(TD `raise(IntFlag.over)`)    $(TD `raise(IntFlag.over)`))
    $(TR $(TH `-1 > 1u`)      $(TD `true`)           $(TD compile-time error)       $(TD `false`))
    $(TR $(TH `-1 - 2u`)      $(TD `4294967293`)     $(TD compile-time error)       $(TD `-3`))
    $(TR $(TH `1 / 0`)        $(TD crash by FPE)     $(TD `raise(IntFlag.div0)`)    $(TD `raise(IntFlag.div0)`))
    $(TR $(TH `int.min % -1`) $(TD crash by FPE)     $(TD `raise(IntFlag.posOver)`) $(TD `0`))
    $(TR $(TH `-1 ^^ -7`)     $(TD crash by FPE)     $(TD `raise(IntFlag.undef)`)   $(TD `-1`))
    $(TR $(TH `cast(uint)-1`) $(TD `4294967295`)     $(TD compile-time error)       $(TD `raise(IntFlag.negOver)`))
    $(TR $(TH `-1 >> 100`)    $(TD undefined) $(TD `raise(IntFlag.undef)`)    $(TD `-1`))
)

$(BIG $(B Error Signaling)) $(BR)
Some types of problem are signaled by a compile-time error, others at runtime. Runtime signaling is done through
$(LINK2 ./flags.html, `checkedint.flags`).
$(UL
    $(LI By default, a `CheckedIntException` is thrown. These are real exceptions; not FPEs. As such, they can be caught
        and include a stack trace.)
    $(LI If necessary, $(LINK2 ./flags.html, `checkedint.flags`) can instead be configured to set a thread-local flag when an operation fails.
        This allows `checkedint` to be used from `nothrow`, or even `@nogc` code.)
)
In normal code, there is no performance penalty for allowing `checkedint` to `throw`. Doing so is highly recommended
because this makes it easier to use correctly, and yields more precise error messages when something goes wrong.

$(BIG $(B Performance)) $(BR)
Replacing all basic integer types with `SmartInt` or `SafeInt` will slow down exectuion somewhat. How much depends on
many factors, but for most code following a few simple rules should keep the penalty low:
$(OL
    $(LI Build with $(B $(RED `--inline`)) and $(B `-O`) (DMD) or $(B `-O3`) (GDC and LDC). This by itself can improve
        the performance of `checkedint` by about around $(B 1,000%).)
    $(LI With GDC or LDC, the performance hit will probably be between 30% and 100%. With DMD it is likely to be 100% to
        200%.)
    $(LI `checkedint` can't slow down code where it's not used! If you really need more speed, try switching to
        `DebugInt` for the hottest code in your program (like inner loops) before giving up on `checkedint` entirely.)
)
The above guidelines should be more than sufficient for most programs. But, here are some micro-optimization tips as
well, if you need them:
$(UL
    $(LI Always use `mulPow2()`, `divPow2()`, and `modPow2()` whenever they can naturally express your intent - they're
        faster than a regular `/`, `%`, or `pow()`.)
    $(LI Unsigned types are a little bit faster than signed types, assuming negative values aren't needed.)
    $(LI Although they are perfectly safe with `checkedint`, mixed signed/unsigned operations are a little bit slower
        than same-signedness ones.)
    $(LI The assignment operators (`++` or `+=`, for example) should never be slower than the equivalent two operation
        sequence, and are sometimes a little bit faster.)
)
*/

module checkedint;
import checkedint.flags;

import std.algorithm, std.format, future.traits;
static import std.math;

@safe:

// traits
enum isSafeInt(T)    = isInstanceOf!(SafeInt, T);
enum isSmartInt(T)   = isInstanceOf!(SmartInt, T);
enum isCheckedInt(T) = isSafeInt!T || isSmartInt!T;

template hasBitOps(T) {
    static if(isCheckedInt!T)
        enum hasBitOps = TemplateArgsOf!T[1];
    else
        enum hasBitOps = isFixedPoint!T;
}
template isThrowingCInt(T) {
    static if(isCheckedInt!T)
        enum isThrowingCInt = TemplateArgsOf!T[2];
    else
        enum isThrowingCInt = false;
}

template BasicScalar(T) {
    static if(isScalarType!T)
        alias BasicScalar = Unqual!T;
    else
    static if(isCheckedInt!T)
        alias BasicScalar = TemplateArgsOf!T[0];
    else
        alias BasicScalar = void;
}

// conv
/+pragma(inline, true) {+/
    T to(T, bool throws, S)(const S value)
        if(isScalarType!(BasicScalar!T) && isScalarType!(BasicScalar!S))
    {
        import checkedint.internal : toImpl;
        const T ret = toImpl!(BasicScalar!T, throws)(value.bscal);

        return ret;
    }
    T to(T, S)(S value) {
        static if(isScalarType!(BasicScalar!T) && isScalarType!(BasicScalar!S))
            return to!(T, true, S)(value);
        else {
            import std.conv : stdTo = to;
            return stdTo!T(value);
        }
    }

    @property {
      /+ref N bscal(N)(return ref N num)
            if(isScalarType!N)
        {
            return num;
        }
        ref N bscal(N)(return ref N num)
            if(isCheckedInt!N)
        {
            return num.bscal;
        }+/
        N bscal(N)(const N num)
            if(isScalarType!N)
        {
            return num;
        }
        N bscal(N)(const N num)
            if(isCheckedInt!N)
        {
            return num.bscal;
        }

      /+ref N bits(N)(return ref N num)
            if(isFixedPoint!N)
        {
            return num;
        }
        ref N bits(N)(return ref N num)
            if(isCheckedInt!N)
        {
            return num.bits;
        }+/
        N bits(N)(const N num)
            if(isFixedPoint!N)
        {
            return num;
        }
        N bits(N)(const N num)
            if(isCheckedInt!N)
        {
            return num.bits;
        }

        Select!(isSigned!N, ptrdiff_t, size_t) idx(N)(const N num)
            if(isScalarType!N)
        {
            return cast(typeof(return))num;
        }
        Select!(isSigned!(BasicScalar!N), ptrdiff_t, size_t) idx(N)(const N num)
            if(isCheckedInt!N)
        {
            return num.idx;
        }
    }
/+}+/

// ops
public import safeOp = checkedint.safeop;
public import smartOp = checkedint.smartop;

// checked types
/+pragma(inline, true) {+/
    // TODO: Convert bitops and throws to std.typecons.Flags?

    template SafeInt(N, bool bitOps = true, bool throws = true)
        if(isCheckedInt!N || (isIntegral!N && !isUnqual!N))
    {
        alias SafeInt = SafeInt!(BasicScalar!N, bitOps, throws);
    }
    struct SafeInt(N, bool bitOps = true, bool throws = true)
        if(isIntegral!N && isUnqual!N)
    {
        /+pure+/ nothrow @nogc {
            static if(bitOps) {
                N bscal;
                @property ref typeof(this) bits() {
                    return this; }
                @property ref const(typeof(this)) bits() const {
                    return this; }
            } else {
                @property ref N bscal() {
                    return bits.bscal; }
                @property ref const(N) bscal() const {
                    return bits.bscal; }
                SafeInt!(N, true, throws) bits;
            }

            static if(__VERSION__ >= 2067) {
                version(GNU) { static assert(false); }
                enum min = typeof(this)(N.min);
                enum max = typeof(this)(N.max);
            } else {
                static @property pure nothrow @nogc {
                    auto min() {
                        return typeof(this)(N.min); }
                    auto max() {
                        return typeof(this)(N.max); }
                }
            }

            // Construction, assignment, and casting
            private void checkImplicit(M)()
                if(isScalarType!M || isCheckedInt!M)
            {
                alias MB = BasicScalar!M;
                static assert(isImplicitlyConvertible!(MB, N),
                    "SafeInt does not support implicit conversions from " ~
                    MB.stringof ~ " to " ~ N.stringof ~
                    ", because they are unsafe when unchecked. Use the explicit checkedint.conv.to()."
                );
            }

            this(const N bscal) {
                this.bscal = bscal; }
            ref typeof(this) opAssign(const N bscal) {
                this.bscal = bscal;
                return this;
            }
            this(M)(const M that)
                if(isScalarType!M)
            {
                checkImplicit!M();
                this.bscal = that.bscal;
            }
            ref typeof(this) opAssign(M)(const M that)
                if(isScalarType!M)
            {
                checkImplicit!M();
                this.bscal = that.bscal;
                return this;
            }

            M opCast(M)() const
                if(isFloatingPoint!M)
            {
                return cast(M)bscal;
            }
            M opCast(M)() const
                if(is(M == bool))
            {
                return bscal != 0;
            }
            size_t toHash() const {
                return cast(size_t)bscal; }

            // Comparison
            bool opEquals(M)(const M right) const
                if(isSafeInt!M || isScalarType!M)
            {
                return safeOp.cmp!"=="(this.bscal, right.bscal);
            }
            auto opCmp(M)(const M right) const
                if(isFloatingPoint!M)
            {
                return
                    (left <  right)? -1 :
                    (left >  right)?  1 :
                    (left == right)?  0 : float.nan;
            }
            int opCmp(M)(const M right) const
                if(isSafeInt!M || isFixedPoint!M)
            {
                return safeOp.cmp(this.bscal, right.bscal);
            }

            // Unary
            SafeInt!(int, bitOps, throws) popcnt() const {
                static assert(bitOps, "Bitwise operations are disabled.");

                import future.bitop : stdPC = popcnt;
                return typeof(return)(stdPC(bscal));
            }

            // Binary
            M opBinaryRight(string op, M)(const M left) const
                if(isFloatingPoint!M)
            {
                return mixin("left " ~ op ~ " bscal");
            }
            M opBinary(string op, M)(const M right) const
                if(isFloatingPoint!M)
            {
                return mixin("bscal " ~ op ~ " right");
            }

            auto mulPow2(M)(const M exp) const
                if(isFloatingPoint!M)
            {
                return safeOp.mulPow2(bscal, exp);
            }
            auto divPow2(M)(const M exp) const
                if(isFloatingPoint!M)
            {
                return safeOp.divPow2(bscal, exp);
            }
            auto modPow2(M)(const M exp) const
                if(isFloatingPoint!M)
            {
                return safeOp.modPow2(bscal, exp);
            }

            M pow(M)(const M exp) const
                if(isFloatingPoint!M)
            {
                return std.math.pow(bscal, exp);
            }
        }
        /+might throw or be impure+/ public {
            // Construction, assignment, and casting
            M opCast(M)() const
                if(isCheckedInt!M || isIntegral!M || isSomeChar!M)
            {
                return to!(M, throws)(bscal);
            }
            @property Select!(isSigned!N, ptrdiff_t, size_t) idx() const {
                return to!(typeof(return), throws)(bscal);
            }

            void toString(Writer, Char)(Writer sink, FormatSpec!Char fmt = (FormatSpec!Char).init) const @trusted {
                formatValue(sink, bscal, fmt); }
            string toString() const {
                return to!string(bscal); }

            // Unary
            typeof(this) opUnary(string op)() const
                if(op.among!("-", "+", "~"))
            {
                static assert(bitOps || (op != "~"),
                    "Bitwise operations are disabled.");

                return typeof(return)(safeOp.unary!(op, throws)(bscal));
            }
            ref typeof(this) opUnary(string op)()
                if(op.among!("++", "--"))
            {
                safeOp.unary!(op, throws)(bscal);
                return this;
            }

            typeof(this) abs() const {
                return typeof(return)(safeOp.abs!throws(bscal)); }

            SafeInt!(int, bitOps, throws) bsf() const {
                static assert(bitOps, "Bitwise operations are disabled.");

                return typeof(return)(safeOp.bsf!throws(bscal));
            }
            SafeInt!(int, bitOps, throws) bsr() const {
                static assert(bitOps, "Bitwise operations are disabled.");

                return typeof(return)(safeOp.bsr!throws(bscal));
            }

            SafeInt!(int, bitOps, throws) ilogb() const {
                return typeof(return)(safeOp.ilogb!throws(bscal)); }

            // Binary
            SafeInt!(OpType!(M, op, N), bitOps, throws) opBinaryRight(string op, M)(const M left) const
                if(isFixedPoint!M)
            {
                static assert(bitOps || !op.among!("<<", ">>", ">>>", "&", "|", "^"),
                    "Bitwise operations are disabled.");

                return typeof(return)(safeOp.binary!(op, throws)(left, bscal));
            }
            SafeInt!(OpType!(N, op, BasicScalar!M), bitOps && hasBitOps!M, throws || isThrowingCInt!M) opBinary(string op, M)(const M right) const
                if(isSafeInt!M || isFixedPoint!M)
            {
                static assert((bitOps && hasBitOps!M) || !op.among!("<<", ">>", ">>>", "&", "|", "^"),
                    "Bitwise operations are disabled.");

                return typeof(return)(safeOp.binary!(op, throws || isThrowingCInt!M)(this.bscal, right.bscal));
            }

            ref typeof(this) opOpAssign(string op, M)(const M right)
                if(isSafeInt!M || isFixedPoint!M)
            {
                static assert((bitOps && hasBitOps!M) || !op.among!("<<", ">>", ">>>", "&", "|", "^"),
                    "Bitwise operations are disabled.");
                checkImplicit!(OpType!(N, op, M))();

                safeOp.binary!(op ~ "=", throws || isThrowingCInt!M)(this.bscal, right.bscal);
                return this;
            }

            auto mulPow2(M)(const M exp) const
                if(isFixedPoint!M || isCheckedInt!M)
            {
                const wret = safeOp.mulPow2!throws(this.bscal, exp.bscal);
                return SafeInt!(typeof(wret), bitOps && hasBitOps!M, throws || isThrowingCInt!M)(wret);
            }
            auto divPow2(M)(const M exp) const
                if(isFixedPoint!M || isCheckedInt!M)
            {
                const wret = safeOp.divPow2!throws(this.bscal, exp.bscal);
                return SafeInt!(typeof(wret), bitOps && hasBitOps!M, throws || isThrowingCInt!M)(wret);
            }
            auto modPow2(M)(const M exp) const
                if(isFixedPoint!M || isCheckedInt!M)
            {
                const wret = safeOp.modPow2(this.bscal, exp.bscal);
                return SafeInt!(typeof(wret), bitOps && hasBitOps!M, throws || isThrowingCInt!M)(wret);
            }

            SafeInt!(CallType!(std.math.pow, N, BasicScalar!M), bitOps && hasBitOps!M, throws || isThrowingCInt!M) pow(M)(const M exp) const
                if(isSafeInt!M || isFixedPoint!M)
            {
                return typeof(return)(safeOp.pow!(throws || isThrowingCInt!M)(this.bscal, exp.bscal));
            }
        }
    }

    template SmartInt(N, bool bitOps = true, bool throws = true)
        if(isCheckedInt!N || (isIntegral!N && !isUnqual!N))
    {
        alias SmartInt = SmartInt!(BasicScalar!N, bitOps, throws);
    }
    struct SmartInt(N, bool bitOps = true, bool throws = true)
        if(isIntegral!N && isUnqual!N)
    {
        /+pure+/ nothrow @nogc {
            static if(bitOps) {
                N bscal;
                @property ref typeof(this) bits() {
                    return this; }
                @property ref const(typeof(this)) bits() const {
                    return this; }
            } else {
                @property ref N bscal() {
                    return bits.bscal; }
                @property ref const(N) bscal() const {
                    return bits.bscal; }
                SmartInt!(N, true, throws) bits;
            }

            static if(__VERSION__ >= 2067) {
                version(GNU) { static assert(false); }
                enum min = typeof(this)(N.min);
                enum max = typeof(this)(N.max);
            } else {
                static @property pure nothrow @nogc {
                    auto min() {
                        return typeof(this)(N.min); }
                    auto max() {
                        return typeof(this)(N.max); }
                }
            }

            // Construction, assignment, and casting
            this(const N bscal) {
                this.bscal = bscal; }
            ref typeof(this) opAssign(const N bscal) {
                this.bscal = bscal;
                return this;
            }
            this(M)(const M that)
                if(isScalarType!M || isCheckedInt!M)
            {
                this.bscal = to!(N, throws)(that);
            }
            ref typeof(this) opAssign(M)(const M that)
                if(isScalarType!M || isCheckedInt!M)
            {
                this.bscal = to!(N, throws)(that);
                return this;
            }

            M opCast(M)() const
                if(isFloatingPoint!M)
            {
                return cast(M)bscal;
            }
            M opCast(M)() const
                if(is(M == bool))
            {
                return bscal != 0;
            }
            size_t toHash() const {
                return cast(size_t)bscal; }

            // Comparison
            bool opEquals(M)(const M right) const
                if(isScalarType!M || isCheckedInt!M)
            {
                return smartOp.cmp!"=="(this.bscal, right.bscal);
            }
            auto opCmp(M)(const M right) const
                if(isFloatingPoint!M)
            {
                return
                    (bscal <  right)? -1 :
                    (bscal >  right)?  1 :
                    (bscal == right)?  0 : float.nan;
            }
            int opCmp(M)(const M right) const
                if(isScalarType!M || isCheckedInt!M)
            {
                return smartOp.cmp(this.bscal, right.bscal);
            }

            // Unary
            typeof(this) opUnary(string op)() const
                if(op == "~")
            {
                static assert(bitOps,
                    "Bitwise operations are disabled.");

                return typeof(return)(smartOp.unary!(op, throws)(bscal));
            }

            SmartInt!(Unsigned!N, bitOps, throws) abs() const {
                return typeof(return)(smartOp.abs(bscal));
            }

            SmartInt!(int, bitOps, throws) popcnt() const {
                static assert(bitOps, "Bitwise operations are disabled.");

                import future.bitop : stdPC = popcnt;
                return typeof(return)(stdPC(bscal));
            }

            // Binary
            auto opBinaryRight(string op, M)(const M left) const
                if(isFloatingPoint!M)
            {
                return smartOp.binary!op(left, bscal);
            }
            auto opBinary(string op, M)(const M right) const
                if(isFloatingPoint!M)
            {
                return smartOp.binary!op(bscal, right);
            }

            auto mulPow2(M)(const M exp) const
                if(isFloatingPoint!M)
            {
                return smartOp.mulPow2(bscal, exp);
            }
            auto divPow2(M)(const M exp) const
                if(isFloatingPoint!M)
            {
                return smartOp.divPow2(bscal, exp);
            }
            auto modPow2(M)(const M exp) const
                if(isFloatingPoint!M)
            {
                return smartOp.modPow2(bscal, exp);
            }

            auto pow(M)(const M exp) const
                if(isFloatingPoint!M)
            {
                return std.math.pow(bscal, exp);
            }
        }
        /+might throw or be impure+/ public {
            // Construction, assignment, and casting
            M opCast(M)() const
                if(isCheckedInt!M || isIntegral!M || isSomeChar!M)
            {
                return to!(M, throws)(bscal);
            }
            @property Select!(isSigned!N, ptrdiff_t, size_t) idx() const {
                return to!(typeof(return), throws)(bscal);
            }

            void toString(Writer, Char)(Writer sink, FormatSpec!Char fmt = (FormatSpec!Char).init) const @trusted {
                formatValue(sink, bscal, fmt); }
            string toString() const {
                return to!string(bscal); }

            // Unary
            SmartInt!(Signed!N, bitOps, throws) opUnary(string op)() const
                if(op == "+" || op == "-")
            {
                return typeof(return)(smartOp.unary!(op, throws)(bscal));
            }
            ref typeof(this) opUnary(string op)()
                if(op.among!("++", "--"))
            {
                smartOp.unary!(op, throws)(bscal);
                return this;
            }

            SmartInt!(ubyte, bitOps, throws) bsf() const {
                static assert(bitOps, "Bitwise operations are disabled.");

                return typeof(return)(smartOp.bsf!throws(bscal));
            }
            SmartInt!(ubyte, bitOps, throws) bsr() const {
                static assert(bitOps, "Bitwise operations are disabled.");

                return typeof(return)(smartOp.bsr!throws(bscal));
            }

            SmartInt!(ubyte, bitOps, throws) ilogb() const {
                return typeof(return)(smartOp.ilogb!throws(bscal)); }

            // Binary
            auto opBinaryRight(string op, M)(const M left) const
                if(isFixedPoint!M || isSafeInt!M)
            {
                static assert((bitOps && hasBitOps!M) || !op.among!("<<", ">>", ">>>", "&", "|", "^"),
                    "Bitwise operations are disabled.");

                const wret = smartOp.binary!(op, throws || isThrowingCInt!M)(left.bscal, this.bscal);
                return SmartInt!(typeof(wret), bitOps && hasBitOps!M, throws || isThrowingCInt!M)(wret);
            }
            auto opBinary(string op, M)(const M right) const
                if(isFixedPoint!M || isCheckedInt!M)
            {
                static assert((bitOps && hasBitOps!M) || !op.among!("<<", ">>", ">>>", "&", "|", "^"),
                    "Bitwise operations are disabled.");

                const wret = smartOp.binary!(op, throws || isThrowingCInt!M)(this.bscal, right.bscal);
                return SmartInt!(typeof(wret), bitOps && hasBitOps!M, throws || isThrowingCInt!M)(wret);
            }
            ref typeof(this) opOpAssign(string op, M)(const M right)
                if(isFixedPoint!M || isCheckedInt!M)
            {
                static assert((bitOps && hasBitOps!M) || !op.among!("<<", ">>", ">>>", "&", "|", "^"),
                    "Bitwise operations are disabled.");

                smartOp.binary!(op ~ "=", throws || isThrowingCInt!M)(this.bscal, right.bscal);
                return this;
            }

            auto mulPow2(M)(const M exp) const
                if(isFixedPoint!M || isCheckedInt!M)
            {
                const wret = smartOp.mulPow2!throws(this.bscal, exp.bscal);
                return SmartInt!(typeof(wret), bitOps && hasBitOps!M, throws || isThrowingCInt!M)(wret);
            }
            auto divPow2(M)(const M exp) const
                if(isFixedPoint!M || isCheckedInt!M)
            {
                const wret = smartOp.divPow2!throws(this.bscal, exp.bscal);
                return SmartInt!(typeof(wret), bitOps && hasBitOps!M, throws || isThrowingCInt!M)(wret);
            }
            auto modPow2(M)(const M exp) const
                if(isFixedPoint!M || isCheckedInt!M)
            {
                const wret = smartOp.modPow2(this.bscal, exp.bscal);
                return SmartInt!(typeof(wret), bitOps && hasBitOps!M, throws || isThrowingCInt!M)(wret);
            }

            auto pow(M)(const M exp) const
                if(isFixedPoint!M || isCheckedInt!M)
            {
                const wret = smartOp.pow!throws(this.bscal, exp.bscal);
                return SmartInt!(typeof(wret), bitOps && hasBitOps!M, throws || isThrowingCInt!M)(wret);
            }
        }
    }
/+}+/

template DebugInt(N, bool bitOps = true, bool throws = true)
    if(isIntegral!N || isCheckedInt!N)
{
    version (Debug)
        alias DebugInt = SafeInt!(N, bitOps, throws);
    else
        alias DebugInt = Unqual!N;
}
