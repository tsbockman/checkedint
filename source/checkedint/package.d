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
    $(LI Mixed signed/unsigned comparisons often give the wrong result: `assert(-1 > 1u);`)
    $(LI Mixed signed/unsigned arithmetic operations can also give the wrong result.)
    $(LI Integer division by zero crashes the program with a mis-named and uncatchable `Floating Point Exception`
        (FPE).)
    $(LI `int.min / -1` and `int.min % -1` may also crash with an FPE, even though the latter should simply yield `0`.)
    $(LI If `x` is any integer value, and `y` is any negative integer value, `x ^^ y` will crash with an FPE.)
    $(LI No bounds checking is done when casting from one integer type to another.)
    $(LI The result of the bitshift operations (`<<`, `>>`, `>>>`) is formally undefined if the shift size is less than
        zero or greater than `(8 * N.sizeof) - 1`.)
)
The `checkedint` package offers solutions to all of these issues and more.

$(BIG $(B `SafeInt` versus `SmartInt`)) $(BR)
Two different approaches are available:
$(UL
    $(LI `SmartInt` and `smartOp` strive to actually give the mathematically correct answer whenever possible, rather
        than just signaling an error.)
    $(LI `SafeInt` and `safeOp` strive to match the behaviour of the basic integral types exactly, $(B except) that
        where the behaviour of the basic type is wrong, or very unintuitive, an error is signaled instead.)
)
There is no meaningful performance difference between `SafeInt` and `SmartInt`. For general use, choose `SmartInt` to
simplify your code and maximize the range of inputs it accepts.

`SafeInt` is intended mainly as a debugging tool, to help identify problems in code that must also work correctly with
the basic integral types. The `DebugInt` `template` `alias` makes it simple to use of `SafeInt` in debug builds, and raw
basic types in release builds.

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
    $(LI By default, a `CheckedIntException` is thrown. These are normal exceptions; not FPEs. As such, they can be
        caught and include a stack trace.)
    $(LI If necessary, $(LINK2 ./flags.html, `checkedint.flags`) can instead be configured to set a thread-local flag
        when an operation fails. This allows `checkedint` to be used from `nothrow`, or even `@nogc` code.)
)
In normal code, there is no performance penalty for allowing `checkedint` to `throw`. Doing so is highly recommended
because this makes it easier to use correctly, and yields more precise error messages when something goes wrong.

$(BIG $(B Performance)) $(BR)
Replacing all basic integer types with `SmartInt` or `SafeInt` will slow down exectuion somewhat. How much depends on
many factors, but for most code following a few simple rules should keep the penalty low:
$(OL
    $(LI Build with $(B $(RED `--inline`)) and $(B `-O`) (DMD) or $(B `-O3`) (GDC and LDC). This by itself can improve
        the performance of `checkedint` by around $(B 1,000%).)
    $(LI With GDC or LDC, the performance hit will probably be between 30% and 100%. With DMD, performance varies wildly
        from one frontend version to the next, depending on the whims of the inscrutable and fickle inliner.)
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

import future.bitop, core.checkedint, std.algorithm, std.format, future.traits, std.typecons;
static import std.math;
static if(__VERSION__ >= 2068) {
    version(GNU) { static assert(false); }
    import std.meta;
} else {
    import std.typetuple;
    private alias AliasSeq = TypeTuple;
}

@safe:

/+pragma(inline, true) {+/
// smart /////////////////////////////////////////////////
/**
Wrapper for any basic integral type `N` that uses the checked operations from `smartOp` and bounds checks assignments
with `checkedint.to()`.

$(UL
    $(LI `throws` controls the error signalling policy (see `checkedint.flags`).)
    $(LI `bitOps` may be set to `No.bitOps` if desired, to turn bitwise operations on this type into a compile-time
        error.)
)
*/
    struct SmartInt(N, Flag!"throws" throws, Flag!"bitOps" bitOps = Yes.bitOps)
        if(isIntegral!N && isUnqual!N)
    {
        static if(bitOps) {
/**
The basic integral value of this `SmartInt`. Accessing this directly may be useful for:
$(UL
    $(LI Intentionally doing modular (unchecked) arithmetic, or)
    $(LI Interacting with APIs that are not `checkedint` aware.)
)
*/
            N bscal;
            ///
            unittest {
                import checkedint.throws : SmartInt; // set Yes.throws

                SmartInt!uint n;
                static assert(is(typeof(n.bscal) == uint));

                n = 7;
                assert(n.bscal == 7);

                n.bscal -= 8;
                assert(n == uint.max);
            }

/// Get a view of this `SmartInt` that allows bitwise operations.
            @property ref inout(SmartInt!(N, throws, Yes.bitOps)) bits() inout pure nothrow @nogc {
                return this; }
            ///
            unittest {
                import checkedint.throws : SmartInt; // set Yes.throws

                SmartInt!(int, No.bitOps) n = 1;
                static assert(!__traits(compiles, n << 2));
                assert(n.bits << 2 == 4);
            }
        } else {
            @property ref inout(N) bscal() inout pure nothrow @nogc {
                return bits.bscal; }
            SmartInt!(N, throws, Yes.bitOps) bits;
        }

        static if(__VERSION__ >= 2067) {
            version(GNU) { static assert(false); }

/// The most negative possible value of this `SmartInt` type.
            enum SmartInt!(N, throws, bitOps) min = typeof(this)(trueMin!N);
            ///
            unittest {
                import checkedint.throws : SmartInt; // set Yes.throws

                assert(SmartInt!(int).min == int.min);
                assert(SmartInt!(uint).min == uint.min);
            }

/// The most positive possible value of this `SmartInt` type.
            enum SmartInt!(N, throws, bitOps) max = typeof(this)(trueMax!N);
            ///
            unittest {
                import checkedint.throws : SmartInt; // set Yes.throws;

                assert(SmartInt!(int).max == int.max);
                assert(SmartInt!(uint).max == uint.max);
            }
        } else {
            static @property auto min() pure nothrow @nogc {
                return typeof(this)(trueMin!N); }
            static @property auto max() pure nothrow @nogc {
                return typeof(this)(trueMax!N); }
        }

        // Construction, assignment, and casting /////////////////////////////////////////////////
/**
Assign the value of `that` to this `SmartInt` instance.

`checkedint.to()` is used to verify `that >= N.min && that <= N.max`. If not, an `IntFlag` will be raised.
*/
        this(M)(const M that)
            if(isCheckedInt!M || isScalarType!M)
        {
            this.bscal = to!(N, throws)(that);
        }
/// ditto
        ref typeof(this) opAssign(M)(const M that)
            if(isCheckedInt!M || isScalarType!M)
        {
            this.bscal = to!(N, throws)(that);
            return this;
        }
        ///
        unittest {
            import checkedint.noex : SmartInt; // set No.throws

            // Any basic scalar or checkedint *type* is accepted...
            SmartInt!int n = 0;
            n = cast(ulong)0;
            n = cast(dchar)0;
            n = cast(byte)0;
            n = cast(real)0;
            assert(!IntFlags.local);

            // ...but not any *value*.
            n = uint.max;
            n = long.min;
            n = real.nan;
            assert(IntFlags.local == (IntFlag.posOver | IntFlag.negOver | IntFlag.undef));

            IntFlags.local.clear();
        }

/**
Convert this value to floating-point. This always succeeds, although some loss of precision may
occur if M.sizeof <= N.sizeof.
*/
        M opCast(M)() const pure nothrow @nogc
            if(isFloatingPoint!M)
        {
            return cast(M)bscal;
        }
        ///
        unittest {
            import checkedint.throws : SmartInt; // set Yes.throws

            SmartInt!int n = 92;
            auto f = cast(double)n;
            static assert(is(typeof(f) == double));
            assert(f == 92.0);
        }

/// `this != 0`
        M opCast(M)() const pure nothrow @nogc
            if(is(M == bool))
        {
            return bscal != 0;
        }
        ///
        unittest {
            import checkedint.throws : SmartInt; // set Yes.throws

            SmartInt!int n = -315;
            assert( cast(bool)n);

            n = 0;
            assert(!cast(bool)n);
        }

/**
Convert this value to type `M` using `checkedint.to()` for bounds checking. An `IntFlag` will be raised if `M` cannot
represent the current value of this `SmartInt`.
*/
        M opCast(M)() const
            if(isCheckedInt!M || isIntegral!M || isSomeChar!M)
        {
            return to!(M, throws)(bscal);
        }
        ///
        unittest {
            import checkedint.noex : SmartInt; // set No.throws

            SmartInt!ulong n = 52;
            auto a = cast(int)n;
            static assert(is(typeof(a) == int));
            assert(!IntFlags.local);
            assert(a == 52);

            auto m = SmartInt!long(-1).mulPow2(n);
            auto b = cast(wchar)m;
            static assert(is(typeof(b) == wchar));
            assert(IntFlags.local == IntFlag.negOver);

            IntFlags.local.clear();
        }

/**
Convert this value to a type suitable for indexing an array:
$(UL
    $(LI If `N` is signed, a `ptrdiff_t` is returned.)
    $(LI If `N` is unsigned, a `size_t` is returned.)
)
`checkedint.to()` is used for bounds checking.
*/
        @property Select!(isSigned!N, ptrdiff_t, size_t) idx() const {
            return to!(typeof(return), throws)(bscal); }
        ///
        unittest {
            import checkedint.throws : SmartInt; // set Yes.throws

            char[3] arr = ['a', 'b', 'c'];
            SmartInt!long n = 1;

            // On 32-bit, `long` cannot be used directly for array indexing,
            static if(size_t.sizeof < long.sizeof)
                static assert(!__traits(compiles, arr[n]));
            // but idx can be used to concisely and safely cast to ptrdiff_t:
            assert(arr[n.idx] == 'b');

            // The conversion is bounds checked:
            static if(size_t.sizeof < long.sizeof) {
                n = long.min;
                try {
                    arr[n.idx] = '?';
                } catch(CheckedIntException e) {
                    assert(e.intFlags == IntFlag.negOver);
                }
            }
        }

/// Get a simple hashcode for this value.
        size_t toHash() const pure nothrow @nogc {
            static if(N.sizeof > size_t.sizeof) {
                static assert(N.sizeof == (2 * size_t.sizeof));
                return cast(size_t)bscal ^ cast(size_t)(bscal >>> 32);
            } else
                return cast(size_t)bscal;
        }

/// Get a `string` representation of this value.
        string toString() const {
            return to!(string, No.throws)(bscal); }
/// ditto
        void toString(Writer, Char)(Writer sink, FormatSpec!Char fmt = (FormatSpec!Char).init) const @trusted {
            formatValue(sink, bscal, fmt); }
        ///
        unittest {
            import checkedint.throws : smartInt; // set Yes.throws
            assert(smartInt(-753).toString() == "-753");
        }

        // Comparison /////////////////////////////////////////////////
/// Returns `true` if this value is mathematically precisely equal to `right`.
        bool opEquals(M)(const M right) const pure nothrow @nogc
            if(isCheckedInt!M || isScalarType!M)
        {
            return smartOp!(throws).cmp!"=="(this.bscal, right.bscal);
        }
/**
Perform a mathematically correct comparison to `right`.

Returns: $(UL
    $(LI `-1` if this value is less than `right`.)
    $(LI ` 0` if this value is precisely equal to `right`.)
    $(LI ` 1` if this value is greater than `right`.)
    $(LI `float.nan` if `right` is a floating-point `nan` value.)
)
*/
        auto opCmp(M)(const M right) const pure nothrow @nogc
            if(isFloatingPoint!M)
        {
            return
                (bscal <  right)? -1 :
                (bscal >  right)?  1 :
                (bscal == right)?  0 : float.nan;
        }
/// ditto
        int opCmp(M)(const M right) const pure nothrow @nogc
            if(isCheckedInt!M || isScalarType!M)
        {
            return smartOp!(throws).cmp(this.bscal, right.bscal);
        }

        // Unary /////////////////////////////////////////////////
/// See `smartOp`.
        typeof(this) opUnary(string op)() const pure nothrow @nogc
            if(op == "~")
        {
            static assert(bitOps,
                "Bitwise operations are disabled.");

            return typeof(return)(smartOp!(throws).unary!op(bscal));
        }
/// ditto
        SmartInt!(Signed!N, throws, bitOps) opUnary(string op)() const
            if(op == "+" || op == "-")
        {
            return typeof(return)(smartOp!(throws).unary!op(bscal));
        }
/// ditto
        ref typeof(this) opUnary(string op)()
            if(op.among!("++", "--"))
        {
            smartOp!(throws).unary!op(bscal);
            return this;
        }

/// ditto
        SmartInt!(Unsigned!N, throws, bitOps) abs() const pure nothrow @nogc {
            return typeof(return)(smartOp!(throws).abs(bscal));
        }

/// Count the number of set bits using `core.bitop.popcnt()`.
        SmartInt!(int, throws, bitOps) popcnt()() const pure nothrow @nogc {
            static assert(bitOps, "Bitwise operations are disabled.");

            import future.bitop : stdPC = popcnt;
            return typeof(return)(stdPC(bscal));
        }

/// See `smartOp`.
        SmartInt!(ubyte, throws, bitOps) bsf()() const {
            static assert(bitOps, "Bitwise operations are disabled.");

            return typeof(return)(smartOp!(throws).bsf(bscal));
        }
/// ditto
        SmartInt!(ubyte, throws, bitOps) bsr()() const {
            static assert(bitOps, "Bitwise operations are disabled. Consider using ilogb() instead?");

            return typeof(return)(smartOp!(throws).bsr(bscal));
        }

/// ditto
        SmartInt!(ubyte, throws, bitOps) ilogb() const {
            return typeof(return)(smartOp!(throws).ilogb(bscal)); }

        // Binary /////////////////////////////////////////////////
/// ditto
        auto opBinaryRight(string op, M)(const M left) const pure nothrow @nogc
            if(isFloatingPoint!M)
        {
            return smartOp!(throws).binary!op(left, bscal);
        }
/// ditto
        auto opBinary(string op, M)(const M right) const pure nothrow @nogc
            if(isFloatingPoint!M)
        {
            return smartOp!(throws).binary!op(bscal, right);
        }
/// ditto
        auto opBinaryRight(string op, M)(const M left) const
            if(isSafeInt!M || isFixedPoint!M)
        {
            enum mixThrows = throws || isThrowingCInt!M;
            enum mixBitOps = bitOps && hasBitOps!M;
            static assert(mixBitOps || !op.among!("<<", ">>", ">>>", "&", "|", "^"),
                "Bitwise operations are disabled. Consider using mulPow2(), divPow2(), or modPow2() instead?");

            const wret = smartOp!(mixThrows).binary!op(left.bscal, this.bscal);
            return SmartInt!(typeof(wret), mixThrows, mixBitOps)(wret);
        }
/// ditto
        auto opBinary(string op, M)(const M right) const
            if(isCheckedInt!M || isFixedPoint!M)
        {
            enum mixThrows = throws || isThrowingCInt!M;
            enum mixBitOps = bitOps && hasBitOps!M;
            static assert(mixBitOps || !op.among!("<<", ">>", ">>>", "&", "|", "^"),
                "Bitwise operations are disabled. Consider using mulPow2(), divPow2(), or modPow2() instead?");

            const wret = smartOp!(mixThrows).binary!op(this.bscal, right.bscal);
            return SmartInt!(typeof(wret), mixThrows, mixBitOps)(wret);
        }
/// ditto
        ref typeof(this) opOpAssign(string op, M)(const M right)
            if(isCheckedInt!M || isFixedPoint!M)
        {
            static assert((bitOps && hasBitOps!M) || !op.among!("<<", ">>", ">>>", "&", "|", "^"),
                "Bitwise operations are disabled. Consider using mulPow2(), divPow2(), or modPow2() instead?");

            smartOp!(throws || isThrowingCInt!M).binary!(op ~ "=")(this.bscal, right.bscal);
            return this;
        }

/// ditto
        auto mulPow2(M)(const M exp) const pure nothrow @nogc
            if(isFloatingPoint!M)
        {
            return smartOp!(throws).mulPow2(bscal, exp);
        }
/// ditto
        auto mulPow2(M)(const M exp) const
            if(isCheckedInt!M || isFixedPoint!M)
        {
            enum mixThrows = throws || isThrowingCInt!M;
            const wret = smartOp!(mixThrows).mulPow2(this.bscal, exp.bscal);
            return SmartInt!(typeof(wret), mixThrows, bitOps && hasBitOps!M)(wret);
        }
/// ditto
        auto divPow2(M)(const M exp) const pure nothrow @nogc
            if(isFloatingPoint!M)
        {
            return smartOp!(throws).divPow2(bscal, exp);
        }
/// ditto
        auto divPow2(M)(const M exp) const
            if(isCheckedInt!M || isFixedPoint!M)
        {
            enum mixThrows = throws || isThrowingCInt!M;
            const wret = smartOp!(mixThrows).divPow2(this.bscal, exp.bscal);
            return SmartInt!(typeof(wret), mixThrows, bitOps && hasBitOps!M)(wret);
        }
/// ditto
        auto modPow2(M)(const M exp) const pure nothrow @nogc
            if(isFloatingPoint!M)
        {
            return smartOp!(throws).modPow2(bscal, exp);
        }
/// ditto
        auto modPow2(M)(const M exp) const
            if(isCheckedInt!M || isFixedPoint!M)
        {
            enum mixThrows = throws || isThrowingCInt!M;
            const wret = smartOp!(mixThrows).modPow2(this.bscal, exp.bscal);
            return SmartInt!(typeof(wret), mixThrows, bitOps && hasBitOps!M)(wret);
        }

/// Raise `this` to the `exp` power using `std.math.pow()`.
        auto pow(M)(const M exp) const pure nothrow @nogc
            if(isFloatingPoint!M)
        {
            return std.math.pow(bscal, exp);
        }
/// See `smartOp`.
        auto pow(M)(const M exp) const
            if(isCheckedInt!M || isFixedPoint!M)
        {
            enum mixThrows = throws || isThrowingCInt!M;
            const wret = smartOp!(mixThrows).pow(this.bscal, exp.bscal);
            return SmartInt!(typeof(wret), mixThrows, bitOps && hasBitOps!M)(wret);
        }
    }
/// ditto
    template SmartInt(N, Flag!"throws" throws, Flag!"bitOps" bitOps = Yes.bitOps)
        if((isIntegral!N && !isUnqual!N) || isCheckedInt!N)
    {
        alias SmartInt = SmartInt!(BasicScalar!N, throws, bitOps);
    }
    ///
    unittest {
        // Mixing standard signed and unsigned types is dangerous, but...
        int ba = -1;
        uint bb = 0;
        assert(ba > bb);

        auto bc = ba + bb;
        assert(is(typeof(bc) == uint));
        assert(bc == 4294967295u);

        // ...with SmartInt, mixed signed/unsigned operations "just work":
        import checkedint.throws : SmartInt; // set Yes.throws

        SmartInt!int ma = -1;
        SmartInt!uint mb = 0;
        assert(ma < mb);

        auto mc = ma + mb;
        assert(is(typeof(mc) == SmartInt!int));
        assert(mc != 4294967295u);
        assert(mc == -1);
    }
    ///
    unittest {
        // When Yes.throws is set, failed SmartInt operations will throw a CheckedIntException.
        import checkedint.throws : SmartInt;

        SmartInt!uint ma = 1;
        SmartInt!uint mb = 0;

        bool overflow = false;
        try {
            SmartInt!uint mc = mb - ma;
            assert(false);
        } catch(CheckedIntException e) {
            assert(e.intFlags == IntFlag.negOver);
            overflow = true;
        }
        assert(overflow);

        bool div0 = false;
        try {
            // With standard integers, this would crash the program with an unrecoverable FPE...
            SmartInt!uint mc = ma / mb;
            assert(false);
        } catch(CheckedIntException e) {
            // ...but with SmartInt, it just throws a normal Exception.
            assert(e.intFlags == IntFlag.div0);
            div0 = true;
        }
        assert(div0);
    }
    ///
    unittest {
        // When No.throws is set, failed SmartInt operations set one or more bits in IntFlags.local.
        import checkedint.noex : SmartInt;

        SmartInt!uint ma = 1;
        SmartInt!uint mb = 0;
        SmartInt!uint mc;

        mc = mb - ma;
        assert(IntFlags.local == IntFlag.negOver);

        // With standard integers, this would crash the program with an unrecoverable FPE...
        mc = ma / mb;
        // ...but with SmartInt, it just sets a bit in IntFlags.local.
        assert(IntFlags.local & IntFlag.div0);

        // Each flag will remain set until cleared:
        assert(IntFlags.local == (IntFlag.negOver | IntFlag.div0));
        IntFlags.local.clear();
        assert(!IntFlags.local);
    }

    private template SmartInt(N, bool throws, bool bitOps)
        if(isIntegral!N)
    {
        alias SmartInt = SmartInt!(
            Unqual!N,
            cast(Flag!"throws")throws,
            cast(Flag!"bitOps")bitOps);
    }

/// Get the value of `num` as a `SmartInt!N`. The integral type `N` can be infered from the argument.
    SmartInt!(N, throws, bitOps) smartInt(Flag!"throws" throws, Flag!"bitOps" bitOps = Yes.bitOps, N)(N num)
        if(isIntegral!N || isCheckedInt!N)
    {
        return typeof(return)(num.bscal);
    }
    ///
    unittest {
        import checkedint.throws : smartInt, SmartInt; // set Yes.throws

        auto a = smartInt(55uL);
        static assert(is(typeof(a) == SmartInt!ulong));
        assert(a == 55);
    }

/**
Implements various integer math operations with error checking.

`smartOp` strives to give the mathematically correct result, with integer-style rounding, for all inputs. Only if the
correct result is undefined or not representable by the return type is an error signalled, using `checkedint.flags`.

The error-signalling policy may be selected using the `throws` template parameter.
*/
    template smartOp(Flag!"throws" throws) {
        // NOTE: Condition is inverted because ddoc only scans the first branch of a static if
        static if(!throws) {
            // No need to redundantly instantiate members which don't depend on `throws`.

            private void cmpTypeCheck(N, M)() pure nothrow @nogc {
                static assert(isBoolean!N == isBoolean!M,
                    "The intent of a direct comparison of " ~
                    N.stringof ~ " with " ~ M.stringof ~
                    " is unclear. Add an explicit cast."
                );
            }

/**
Compare `left` and `right` using `op`.
$(UL
    $(LI Unlike the standard integer comparison operator, this function correctly handles negative values in
        signed/unsigned comparisons.)
    $(LI Like the standard operator, comparisons involving any floating-point `nan` value always return `false`.)
) $(BR)
Direct comparisons between boolean values and numeric ones are forbidden. Make your intention explicit:
$(UL
    $(LI `cast(N)boolean == numeric`)
    $(LI `boolean == (numeric != 0)`)
)
*/
            bool cmp(string op, N, M)(const N left, const M right) pure nothrow @nogc
                if(isScalarType!N && isScalarType!M)
            {
                cmpTypeCheck!(N, M)();

                static if(isSigned!N != isSigned!M) {
                    static if(isSigned!N) {
                        if(left < 0)
                            return mixin("-1 " ~ op ~ " 0");
                    } else {
                        if(right < 0)
                            return mixin("0 " ~ op ~ " -1");
                    }
                }

                return mixin("left " ~ op ~ " right");
            }
            ///
            unittest {
                import checkedint.noex : smartOp; // smartOp.cmp() never throws

                assert(-1 == uint.max);
                assert( smartOp.cmp!"!="(uint.max, -1));
                assert(-3156 > 300u);
                assert( smartOp.cmp!"<"(-3156, 300u));

                assert(!smartOp.cmp!"<"(1, real.nan));
                assert(!smartOp.cmp!"<"(real.nan, 1));
            }

/**
Defines a total order on all basic scalar values, using the same rules as `std.math.cmp`.

$(UL
    $(LI Mixed signed/unsigned comparisons return the mathematically correct result.)
    $(LI If neither `left` nor `right` is floating-point, this function is faster than `std.math.cmp`.)
    $(LI If either `left` or `right` $(I is) floating-point, this function forwards to `std.math.cmp`.)
) $(BR)
Direct comparisons between boolean values and numeric ones are forbidden. Make your intention explicit:
$(UL
    $(LI `cast(N)boolean == numeric`)
    $(LI `boolean == (numeric != 0)`)
)
*/
            int cmp(N, M)(const N left, const M right) pure nothrow @nogc
                if(isScalarType!N && isScalarType!M)
            {
                cmpTypeCheck!(N, M)();

                static if(isFloatingPoint!N || isFloatingPoint!M) {
                    import future.math : stdCmp = cmp;
                    return stdCmp(left, right);
                } else {
                    static if(isSigned!N != isSigned!M) {
                        static if(isSigned!N) {
                            if(left < 0)
                                return -1;
                        } else {
                            if(right < 0)
                                return  1;
                        }
                    }

                    return (left < right)? -1 : (right < left);
                }
            }
            ///
            unittest {
                import checkedint.noex : smartOp; // smartOp.cmp() never throws

                assert(smartOp.cmp(325.0, 325u) == 0);
                assert(smartOp.cmp(uint.max, -1) == 1);
                assert(smartOp.cmp(-3156, 300u) == -1);
            }

/// Get the absolute value of `num`. Because the return type is always unsigned, overflow is not possible.
            Unsigned!N abs(N)(const N num) pure nothrow @nogc
                if(isIntegral!N)
            {
                static if(!isSigned!N)
                    return num;
                else
                    return cast(typeof(return))(num < 0?
                        -num : // -num doesn't need to be checked for overflow
                         num);
            }
/// ditto
            IntFromChar!N abs(N)(const N num) pure nothrow @nogc
                if(isSomeChar!N)
            {
                return num;
            }
            ///
            unittest {
                import checkedint.noex : smartOp; // smartOp.abs() never throws

                assert(smartOp.abs(int.min) == std.math.pow(2.0, 31));
                assert(smartOp.abs(-25) == 25u);
                assert(smartOp.abs(745u) == 745u);
            }

            private template Result(N, string op, M)
                if(isNumeric!N && isNumeric!M)
            {
            private:
                enum reqFloat = isFloatingPoint!N || isFloatingPoint!M;
                enum precN = precision!N, precM = precision!M;
                enum precStd = reqFloat? precision!float : precision!uint;
                enum smallSub = (op == "-") && precN < precision!int && precM < precision!int;

                enum reqSign = reqFloat ||
                    (op.among!("+", "-", "*" , "/") && (isSigned!N || isSigned!M || smallSub)) ||
                    (op.among!("%", "^^", "<<", ">>", ">>>") && isSigned!N) ||
                    (op.among!("&", "|", "^") && (isSigned!N && isSigned!M));

                enum reqPrec = reqFloat? max(precStd, precN, precM) :
                    op.among!("+", "-", "*")? max(precStd, precN, precM) - 1 :
                    op == "/"? (isSigned!M? max(precStd, precN) - 1 : precN) :
                    op == "%"? min(precision!N, precision!M) :
                    op == "^^"? max(precStd - 1, precN) :
                    op.among!("<<", ">>", ">>>")? precN :
                  /+op.among!("&", "|", "^")?+/ max(precN, precM);

            public:
                alias Result = Select!(reqFloat,
                    Select!(reqPrec <= double.mant_dig || double.mant_dig >= real.mant_dig,
                        Select!(reqPrec <= float.mant_dig, float, double),
                        real),
                    Select!(reqSign,
                        Select!(reqPrec <= 15,
                            Select!(reqPrec <= 7, byte, short),
                            Select!(reqPrec <= 31, int, long)),
                        Select!(reqPrec <= 16,
                            Select!(reqPrec <= 8, ubyte, ushort),
                            Select!(reqPrec <= 32, uint, ulong))));
            }
            private template Result(N, string op, M)
                if(isScalarType!N && isScalarType!M &&
                    (!isNumeric!N || !isNumeric!M))
            {
                alias Result = Result!(NumFromScal!N, op, NumFromScal!M);
            }
        } else {
            alias cmp = smartOp!(No.throws).cmp;
            alias abs = smartOp!(No.throws).abs;
            private alias Result = smartOp!(No.throws).Result;
        }

/**
Perform the unary (single-argument) integer operation specified by `op`.

Key differences from the standard unary operators:
$(UL
    $(LI `-` and `+` always return a signed value.)
    $(LI `-` is checked for overflow, because `-int.min` is greater than `int.max`.)
    $(LI `++` and `--` are checked for overflow.)
) $(BR)
Note that like the standard operators, `++` and `--` take the operand by `ref` and overwrite its value with the result.
*/
        N unary(string op, N)(const N num) pure nothrow @nogc
            if(isIntegral!N && op == "~")
        {
            return ~num;
        }
/// ditto
        IntFromChar!N unary(string op, N)(const N num) pure nothrow @nogc
            if(isSomeChar!N && op == "~")
        {
            return ~num;
        }
/// ditto
        Signed!(Promoted!N) unary(string op, N)(const N num)
            if(isFixedPoint!N && op.among!("-", "+"))
        {
            alias R = typeof(return);
            alias UR = Unsigned!R;

            static if(op == "-") {
                static if(isSigned!N) {
                    if(num < -trueMax!R)
                        IntFlag.posOver.raise!throws();
                } else {
                    if(num > cast(UR)trueMin!R)
                        IntFlag.negOver.raise!throws();
                }

                return -cast(R)num;
            } else {
                static if(!isSigned!N) {
                    if(num > trueMax!R)
                        IntFlag.posOver.raise!throws();
                }

                return num;
            }
        }
/// ditto
        /+ref+/ N unary(string op, N)(/+return+/ ref N num)
            if(isIntegral!N && op.among!("++", "--"))
        {
            static if(op == "++") {
                if(num >= trueMax!N)
                    IntFlag.posOver.raise!throws();

                return ++num;
            } else static if(op == "--") {
                if(num <= trueMin!N)
                    IntFlag.negOver.raise!throws();

                return --num;
            } else
                static assert(false);
        }
        ///
        unittest {
            import checkedint.noex : smartOp; // set No.throws

            assert(smartOp.unary!"~"(0u) == uint.max);

            auto a = smartOp.unary!"-"(20uL);
            static assert(is(typeof(a) == long));
            assert(a == -20);

            smartOp.unary!"+"(uint.max);
            assert(IntFlags.local == IntFlag.posOver);
            IntFlags.local.clear();

            uint b = 1u;
            assert(smartOp.unary!"--"(b) == 0u);
            assert(b == 0u);
            smartOp.unary!"--"(b);
            assert(IntFlags.local == IntFlag.negOver);
            IntFlags.local.clear();

            int c = 7;
            assert(smartOp.unary!"++"(c) == 8);
            assert(c == 8);
        }

/// `core.bitop.bsf` without the undefined behaviour. `smartOp.bsf(0)` will raise `IntFlag.undef`.
        ubyte bsf(N)(const N num)
            if(isFixedPoint!N)
        {
            return cast(ubyte) bsfImpl!throws(num);
        }
        ///
        unittest {
            import checkedint.noex : smartOp;

            assert(smartOp.bsf(20) == 2);

            smartOp.bsf(0);
            assert(IntFlags.local == IntFlag.undef);

            IntFlags.local.clear();
        }

/// `core.bitop.bsr` without the undefined behaviour. `smartOp.bsr(0)` will raise `IntFlag.undef`.
        ubyte bsr(N)(const N num)
            if(isFixedPoint!N)
        {
            return cast(ubyte) bsrImpl!throws(num);
        }
        ///
        unittest {
            import checkedint.noex : smartOp;

            assert(smartOp.bsr(20) == 4);
            assert(smartOp.bsr(-20) == 31);

            smartOp.bsr(0);
            assert(IntFlags.local == IntFlag.undef);

            IntFlags.local.clear();
        }

/**
Get the base 2 logarithm of `abs(num)`, rounded down to the nearest integer.

`smartOp.ilogb(0)` will raise `IntFlag.undef`.
*/
        ubyte ilogb(N)(const N num)
            if(isFixedPoint!N)
        {
            return cast(ubyte) bsrImpl!throws(abs(num));
        }
        ///
        unittest {
            import checkedint.noex : smartOp;

            assert(smartOp.ilogb(20) == 4);
            assert(smartOp.ilogb(-20) == 4);

            smartOp.ilogb(0);
            assert(IntFlags.local == IntFlag.undef);

            IntFlags.local.clear();
        }

        private auto binaryImpl(string op, N, M)(const N left, const M right)
            if(isIntegral!N && isIntegral!M)
        {
            enum wop = (op[$-1] == '=')? op[0 .. $-1] : op;
            alias
                UN = Unsigned!N,
                UM = Unsigned!M,
                 W = Result!(N, wop, M),
                 R = Select!(wop == op, W, N);

            static if(wop.among!("+", "-", "*")) {
                enum safePrec = (wop == "*")?
                    precision!N + precision!M :
                    max(precision!N, precision!M) + 1;
                enum safeR = precision!R >= safePrec;

                static if(safeR)
                    return mixin("cast(R)left " ~ wop ~ " cast(R)right");
                else {
                    enum safeW = precision!W >= safePrec;
                    enum matched = (isSigned!N == isSigned!M);
                    enum oX = staticIndexOf!(wop, "+", "-", "*") << 1;
                    alias cops = AliasSeq!(addu, adds, subu, subs, mulu, muls);

                    static if(safeW || matched || wop == "*") {
                        bool over;
                        static if(safeW)
                            const wR = mixin("cast(W)left " ~ wop ~ " cast(W)right");
                        else {
                            static if(matched) {
                                alias cop = cops[oX + isSigned!W];
                                const wR = cop(left, right, over);
                            } else {
                                // integer multiplication is commutative
                                static if(isSigned!N)
                                    W sa = left, ub = right;
                                else
                                    W ub = left, sa = right;

                                static if(isSigned!R) {
                                    W wR = muls(sa, ub, over);
                                    if(ub < 0)
                                        over = (sa != 0) && (ub != trueMin!W || sa != -1);
                                } else {
                                    over = (sa < 0) && (ub != 0);
                                    const wR = mulu(sa, ub, over);
                                }
                            }
                        }

                        alias WR = typeof(wR);
                        static if(isSigned!WR && trueMin!WR < trueMin!R) {
                            if(wR < trueMin!R)
                                over = true;
                        }
                        static if(trueMax!WR > trueMax!R) {
                            if(wR > trueMax!R)
                                over = true;
                        }
                    } else {
                        alias UW = Unsigned!W;
                        alias WR = Select!(isSigned!R, W, UW);
                        alias cop = cops[oX];

                        bool hiBit = false;
                        const wR = cast(WR) cop(cast(UW)left, cast(UW)right, hiBit);
                        const bool wSign = (Select!(isSigned!N, left, right) < 0) ^ hiBit;

                        static if(isSigned!WR) {
                            static if(trueMax!WR > trueMax!R) {
                                const over = (wR < 0)?
                                    !wSign || (wR < trueMin!R) :
                                     wSign || (wR > trueMax!R);
                            } else
                                const over = (wR < 0) != wSign;
                        } else {
                            static if(trueMax!WR > trueMax!R)
                                const over = wSign || (wR > trueMax!R);
                            else
                                alias over = wSign;
                        }
                    }

                    if(over)
                        IntFlag.over.raise!throws();
                    return cast(R) wR;
                }
            } else
            static if(wop == "/") {
                static if(!isSigned!N && !isSigned!M) {
                    R ret = void;
                    if(right == 0) {
                        IntFlag.div0.raise!throws();
                        ret = 0;
                    } else
                        ret = cast(R)(left / right);

                    return ret;
                } else {
                    alias P = Select!(precision!N <= 32 && precision!M <= 32, uint, ulong);

                    IntFlag flag;
                    R ret = void;
                    if(right == 0) {
                        flag = IntFlag.div0;
                        ret = 0;
                    } else {
                        static if(isSigned!N && isSigned!M) {
                            if(left == trueMin!R && right == -1) {
                                flag = IntFlag.posOver;
                                ret = 0;
                            } else
                                ret = cast(R)(left / right);
                        } else {
                            alias UR = Unsigned!R;

                            P wL = void;
                            P wG = void;
                            static if(isSigned!N) {
                                const negR = left < 0;
                                alias side = left;
                                alias wS = wL;
                                wG = cast(P)right;
                            } else {
                                const negR = right < 0;
                                wL = cast(P)left;
                                alias side = right;
                                alias wS = wG;
                            }

                            if(negR) {
                                wS = -cast(P)side;
                                const P wR = wL / wG;

                                if(wR > cast(UR)trueMin!R)
                                    flag = IntFlag.negOver;
                                ret = -cast(R)wR;
                            } else {
                                wS =  cast(P)side;
                                const P wR = wL / wG;

                                if(wR > cast(UR)trueMax!R)
                                    flag = IntFlag.posOver;
                                ret =  cast(R)wR;
                            }
                        }
                    }

                    if(!flag.isNull)
                        flag.raise!throws();
                    return ret;
                }
            } else
            static if(wop == "%") {
                R ret = void;
                static if(isSigned!M)
                    const wG = cast(UM)((right < 0)? -right : right);
                else
                    const wG = right;

                if(wG <= trueMax!N) {
                    if(wG)
                        ret = cast(R)(left % cast(N)wG);
                    else {
                        IntFlag.div0.raise!throws();
                        ret = 0;
                    }
                } else {
                    static if(isSigned!N)
                        ret = (wG != cast(UN)trueMin!N || left != trueMin!N)?
                            cast(R)left :
                            cast(R)0;
                    else
                        ret = cast(R)left;
                }

                return ret;
            } else
            static if(wop.among!("<<", ">>", ">>>")) {
                const negG = right < 0;
                const shR = (wop == "<<")?
                     negG :
                    !negG;

                R ret = void;
                static if(wop == ">>>")
                    const wL = cast(UN)left;
                else
                    alias wL = left;
                const absG = negG?
                    -cast(UM)right :
                     cast(UM)right;

                enum maxSh = precision!UN - 1;
                if(absG <= maxSh) {
                    const wG = cast(int)absG;
                    ret = cast(R)(shR?
                        wL >> wG :
                        wL << wG);
                } else {
                    ret = cast(R)((isSigned!N && (wop != ">>>") && shR)?
                        (wL >> maxSh) :
                        0);
                }

                return ret;
            } else
            static if(wop.among!("&", "|", "^"))
                return cast(R)mixin("left " ~ wop ~ " right");
            else
                static assert(false);
        }

/**
Perform the binary (two-argument) integer operation specified by `op`.

Key differences from the standard binary operators:
$(UL
    $(LI `+`, `-`, `*`, `/`, and `%` return a signed type if the result could be negative, unless $(B both) inputs are
        unsigned.)
    $(LI `+`, `-`, `*`, and `/` are checked for overflow.)
    $(LI `/` and `%` are checked for divide-by-zero, and will never generate an FPE.)
    $(LI `<<`, `>>`, and `>>>` are well-defined for all possible values of `right`. Large shifts return the same result
        as shifting by `1` `right` times in a row. (But, much faster because no actual loop is used.))
) $(BR)
Note also:
$(UL
    $(LI The shift operators are $(B $(RED not)) checked for overflow and should not be used for multiplication,
        division, or exponentiation. Instead, use `mulPow2()` and `divPow2()`, which internally use the bitshifts for speed,
        but check for overflow and correctly handle negative values.)
    $(LI Likewise, `modPow2()` should be used for remainders instead of `&`.)
    $(LI `^^` and `^^=` will remain disabled in favour of `pow` until DMD issues 15288 and 15412 are fixed.)
) $(BR)
Like the standard equiavlents, the assignment operators (`+=`, `-=`, `*=`, etc.) take `left` by `ref` and will overwrite
it with the result of the operation.
*/
        auto binary(string op, N, M)(const N left, const M right)
            if(isFixedPoint!N && isFixedPoint!M && op.among!("+", "-", "*", "/", "%", "^^", "<<", ">>", ">>>", "&", "|", "^"))
        {
            static assert(op != "^^",
                "pow() should be used instead of operator ^^ because of issue 15288.");

            return binaryImpl!(op, NumFromScal!N, NumFromScal!M)(left, right);
        }
/// ditto
        /+ref+/ N binary(string op, N, M)(/+return+/ ref N left, const M right)
            if(isIntegral!N && isFixedPoint!M && (op[$ - 1] == '='))
        {
            static assert(op != "^^=",
                "pow() should be used instead of operator ^^= because of issue 15412.");

            left = binaryImpl!(op, NumFromScal!N, NumFromScal!M)(left, right);
            return left;
        }
        ///
        unittest {
            import checkedint.noex : smartOp; // set No.throws

            ulong a = 18_446_744_073_709_551_615uL;
            long b =      -6_744_073_709_551_615L;
            auto c = smartOp.binary!"+"(a, b);
            static assert(is(typeof(c) == long));
            assert(IntFlags.local == IntFlag.posOver);
            IntFlags.local.clear();

            smartOp.binary!"+="(a, b);
            assert(a == 18_440_000_000_000_000_000uL);

            uint d = 25;
            int e = 32;
            auto f = smartOp.binary!"-"(d, e);
            static assert(is(typeof(f) == int));
            assert(f == -7);

            smartOp.binary!"-="(d, e);
            assert(IntFlags.local == IntFlag.negOver);
            IntFlags.local.clear();

            uint g = 1u << 31;
            int h = -1;
            auto i = smartOp.binary!"*"(g, h);
            static assert(is(typeof(i) == int));
            assert(i == int.min);

            smartOp.binary!"*="(g, h);
            assert(IntFlags.local == IntFlag.negOver);
            IntFlags.local.clear();

            long j = long.min;
            ulong k = 1uL << 63;
            auto m = smartOp.binary!"/"(j, k);
            static assert(is(typeof(m) == long));
            assert(m == -1);

            smartOp.binary!"/="(j, -1);
            assert(IntFlags.local == IntFlag.posOver);
            IntFlags.local.clear();

            ushort n = 20u;
            ulong p = ulong.max;
            auto q = smartOp.binary!"%"(n, p);
            static assert(is(typeof(q) == ushort));
            assert(q == 20u);

            smartOp.binary!"%="(n, 0);
            assert(IntFlags.local == IntFlag.div0);
            IntFlags.local.clear();
        }
        ///
        unittest {
            import checkedint.noex : smartOp; // set No.throws

            assert(smartOp.binary!"<<"(-0x80, -2) == -0x20);
            ubyte a = 0x3u;
            long b = long.max;
            auto c = smartOp.binary!"<<"(a, b);
            static assert(is(typeof(c) == ubyte));
            assert(c == 0u);

            smartOp.binary!"<<="(a, 7);
            assert(a == 0x80u);

            short d = -0xC;
            ubyte e = 5u;
            auto f = smartOp.binary!">>"(d, e);
            static assert(is(typeof(f) == short));
            assert(f == -0x1);

            smartOp.binary!">>="(d, -8);
            assert(d == -0xC00);

            int g = -0x80;
            ulong h = 2u;
            auto i = smartOp.binary!">>>"(g, h);
            static assert(is(typeof(i) == int));
            assert(i == 0x3FFFFFE0);

            smartOp.binary!">>>="(g, 32);
            assert(g == 0);

            ubyte j = 0x6Fu;
            short k = 0x4076;
            auto m = smartOp.binary!"&"(j, k);
            static assert(is(typeof(m) == ushort));
            assert(m == 0x66u);

            smartOp.binary!"&="(j, k);
            assert(j == 0x66u);

            byte n = 0x6F;
            ushort p = 0x4076u;
            auto q = smartOp.binary!"|"(n, p);
            static assert(is(typeof(q) == ushort));
            assert(q == 0x407Fu);

            smartOp.binary!"|="(n, p);
            assert(n == 0x7F);

            int r = 0x6F;
            int s = 0x4076;
            auto t = smartOp.binary!"^"(r, s);
            static assert(is(typeof(t) == int));
            assert(t == 0x4019);

            smartOp.binary!"^="(r, s);
            assert(r == 0x4019);

            assert(!IntFlags.local);
        }

/**
Equivalent to `left * pow(2, exp)`, but faster and works with a wider range of inputs. This is a safer alternative to
`left << exp` that is still very fast.

Note that (conceptually) rounding occurs $(I after) the `*`, meaning that `mulPow2(left, -exp)` is equivalent to
`divPow2(left, exp)`.
*/
        auto mulPow2(N, M)(const N left, const M exp) pure nothrow @nogc
            if((isFloatingPoint!N && isScalarType!M) || (isScalarType!N && isFloatingPoint!M))
        {
            return byPow2Impl!("*", NumFromScal!N, NumFromScal!M)(left, exp);
        }
/// ditto
        auto mulPow2(N, M)(const N left, const M exp)
            if(isFixedPoint!N && isFixedPoint!M)
        {
            return byPow2Impl!("*", throws, NumFromScal!N, NumFromScal!M)(left, exp);
        }
        ///
        unittest {
            import checkedint.noex : smartOp; // set No.throws

            assert(smartOp.mulPow2(-23, 5) == -736);
            smartOp.mulPow2(10_000_000, 10);
            assert(IntFlags.local == IntFlag.posOver);

            assert(smartOp.mulPow2(65536, -8) == 256);
            assert(smartOp.mulPow2(-100, -100) == 0);

            IntFlags.local.clear();
        }

/**
Equivalent to `left / pow(2, exp)`, but faster and works with a wider range of inputs. This is a safer alternative to
`left >> exp` that is still very fast.

Note that (conceptually) rounding occurs $(I after) the `/`, meaning that `divPow2(left, -exp)` is equivalent to
`mulPow2(left, exp)`.
*/
        auto divPow2(N, M)(const N left, const M exp) pure nothrow @nogc
            if((isFloatingPoint!N && isScalarType!M) || (isScalarType!N && isFloatingPoint!M))
        {
            return byPow2Impl!("/", NumFromScal!N, NumFromScal!M)(left, exp);
        }
/// ditto
        auto divPow2(N, M)(const N left, const M exp)
            if(isFixedPoint!N && isFixedPoint!M)
        {
            return byPow2Impl!("/", throws, NumFromScal!N, NumFromScal!M)(left, exp);
        }
        ///
        unittest {
            import checkedint.noex : smartOp; // set No.throws

            assert(smartOp.divPow2(65536, 8) == 256);
            assert(smartOp.divPow2(-100, 100) == 0);
            assert(smartOp.divPow2(-23, -5) == -736);

            smartOp.divPow2(10_000_000, -10);
            assert(IntFlags.local == IntFlag.posOver);

            IntFlags.local.clear();
        }

/**
Equivalent to `left % pow(2, exp)`, but faster and works with a wider range of inputs. This is a safer alternative to
`left & ((1 << exp) - 1)` that is still very fast.
*/
        auto modPow2(N, M)(const N left, const M exp) pure nothrow @nogc
            if((isFloatingPoint!N && isScalarType!M) || (isScalarType!N && isFloatingPoint!M))
        {
            return byPow2Impl!("%", NumFromScal!N, NumFromScal!M)(left, exp);
        }
/// ditto
        auto modPow2(N, M)(const N left, const M exp) pure nothrow @nogc
            if(isFixedPoint!N && isFixedPoint!M)
        {
            return byPow2Impl!("%", No.throws, NumFromScal!N, NumFromScal!M)(left, exp);
        }
        ///
        unittest {
            import checkedint.noex : smartOp; // set No.throws

            assert(smartOp.modPow2( 101,  1) ==  1);
            assert(smartOp.modPow2( 101,  3) ==  5);
            assert(smartOp.modPow2(-101,  3) == -5);

            assert(smartOp.modPow2(101, -2) ==  0);
            assert(smartOp.modPow2(101, 1_000) == 101);
        }

/**
Raise `base` to the `exp` power.

Errors that may be signalled if neither input is floating-point:
$(UL
    $(LI `IntFlag.posOver` or `IntFlag.negOver` if the absolute value of the result is too large to
        represent with the return type.)
    $(LI `IntFlag.div0` if `base == 0` and `exp < 0`.)
)
*/
        auto pow(N, M)(const N base, const M exp) pure nothrow @nogc
            if((isFloatingPoint!N && isScalarType!M) || (isScalarType!N && isFloatingPoint!M))
        {
            alias R = Result!(N, "^^", M);
            static assert(is(typeof(return) == R));
            return std.math.pow(cast(R)base, exp);
        }
/// ditto
        auto pow(N, M)(const N base, const M exp)
            if(isFixedPoint!N && isFixedPoint!M)
        {
            alias R = Result!(N, "^^", M);

            const po = powImpl!(R, Select!(isSigned!M, long, ulong))(base, exp);
            static assert(is(typeof(po.num) == const(R)));

            if(!po.flag.isNull)
                po.flag.raise!throws();
            return po.num;
        }
        ///
        unittest {
            import checkedint.noex : smartOp; // set No.throws

            assert(smartOp.pow(-10, 3) == -1_000);
            assert(smartOp.pow(16L, 4u) == 65536L);
            assert(smartOp.pow(2, -1) == 0);

            smartOp.pow(-3, 27);
            smartOp.pow(0, -5);
            assert(IntFlags.local == (IntFlag.negOver | IntFlag.div0));

            IntFlags.local.clear();
        }
    }
    private alias smartOp(bool throws) = smartOp!(cast(Flag!"throws")throws);

// debug /////////////////////////////////////////////////
/**
`template` `alias` that evaluates to `SafeInt!(N, throws, bitOps)` in debug mode, and `N` in release mode. This way, you
can use `SafeInt!N` to debug your integer logic in testing, but switch to basic `N` in release mode for maximum speed
and the smallest binaries.

While this may be very helpful for debuggin your algorithms, note that `DebugInt` is $(B $(RED not)) a substitute for
input validation in release mode. Unrecoverable FPEs or silent data-corrupting overflow can still occur in release
mode if you get your algorithm wrong, or fail to add manual bounds checks in the right places.

If performance is your only motivation for using `DebugInt` rather than `SmartInt`, consider limiting `DebugInt` to
only the hotest code paths - inner loops and the like. For most programs, this should provide nearly the same
performance boost as using it everywhere, with far less loss of safety.
*/
    template DebugInt(N, Flag!"throws" throws, Flag!"bitOps" bitOps = Yes.bitOps)
        if(isIntegral!N || isCheckedInt!N)
    {
        version (Debug)
            alias DebugInt = SafeInt!(N, throws, bitOps);
        else
            alias DebugInt = Unqual!N;
    }

// safe /////////////////////////////////////////////////
/**
Wrapper for any basic integral type `N` that uses the checked operations from `safeOp` and rejects attempts to directly
assign values that cannot be proven to be within the range representable by `N`. (`checkedint.to()` can be used to safely
assign values of incompatible types, with runtime bounds checking.)

`SafeInt` is designed to be as interchangeable with `N` as possible, without compromising safety. The `DebugInt`
`template` allows a variable to use `SafeInt` in debug mode to find bugs, and `N` directly in release mode for greater
speed and a smaller binary.

If you're not trying to write generic code that works with both `SafeInt!N` and `N`, you should probably be using
`SmartInt` instead. It generates far fewer error messages; mostly it "just works".

$(UL
    $(LI `throws` controls the error signalling policy (see `checkedint.flags`).)
    $(LI `bitOps` may be set to `No.bitOps` if desired, to turn bitwise operations on this type into a compile-time
        error.)
)
*/
    struct SafeInt(N, Flag!"throws" throws, Flag!"bitOps" bitOps = Yes.bitOps)
        if(isIntegral!N && isUnqual!N)
    {
        static if(bitOps) {
/**
The basic integral value of this `SafeInt`. Accessing this directly may be useful for:
$(UL
    $(LI Intentionally doing modular (unchecked) arithmetic, or)
    $(LI Interacting with APIs that are not `checkedint` aware.)
)
*/
            N bscal;
            ///
            unittest {
                import checkedint.throws : SafeInt; // set Yes.throws

                SafeInt!uint n;
                static assert(is(typeof(n.bscal) == uint));

                n = 7u;
                assert(n.bscal == 7u);

                n.bscal -= 8u;
                assert(n == uint.max);
            }

/// Get a view of this `SafeInt` that allows bitwise operations.
            @property ref inout(SafeInt!(N, throws, Yes.bitOps)) bits() inout pure nothrow @nogc {
                return this; }
            ///
            unittest {
                import checkedint.throws : SafeInt; // set Yes.throws

                SafeInt!(int, No.bitOps) n = 1;
                static assert(!__traits(compiles, n << 2));
                assert(n.bits << 2 == 4);
            }
        } else {
            @property ref inout(N) bscal() inout pure nothrow @nogc {
                return bits.bscal; }
            SafeInt!(N, throws, Yes.bitOps) bits;
        }

        static if(__VERSION__ >= 2067) {
            version(GNU) { static assert(false); }

/// The most negative possible value of this `SafeInt` type.
            enum SafeInt!(N, throws, bitOps) min = typeof(this)(trueMin!N);
            ///
            unittest {
                import checkedint.throws : SafeInt; // set Yes.throws

                assert(SafeInt!(int).min == int.min);
                assert(SafeInt!(uint).min == uint.min);
            }

/// The most positive possible value of this `SafeInt` type.
            enum SafeInt!(N, throws, bitOps) max = typeof(this)(trueMax!N);
            ///
            unittest {
                import checkedint.throws : SafeInt; // set Yes.throws;

                assert(SafeInt!(int).max == int.max);
                assert(SafeInt!(uint).max == uint.max);
            }
        } else {
            static @property auto min() pure nothrow @nogc {
                return typeof(this)(trueMin!N); }
            static @property auto max() pure nothrow @nogc {
                return typeof(this)(trueMax!N); }
        }

        // Construction, assignment, and casting /////////////////////////////////////////////////
        private void checkImplicit(M)() const
            if(isCheckedInt!M || isScalarType!M)
        {
            alias MB = BasicScalar!M;
            static assert(trueMin!MB >= cast(real)N.min && MB.max <= cast(real)N.max,
                "SafeInt does not support implicit conversions from " ~
                MB.stringof ~ " to " ~ N.stringof ~
                ", because they are unsafe when unchecked. Use the explicit checkedint.to()."
            );
        }

/**
Assign the value of `that` to this `SafeInt` instance.

Trying to assign a value that cannot be proven at compile time to be representable by `N` is an error. Use
`checkedint.to()` to safely convert `that` with runtime bounds checking, instead.
*/
        this(M)(const M that) pure nothrow @nogc
            if(isCheckedInt!M || isScalarType!M)
        {
            checkImplicit!M();
            this.bscal = that.bscal;
        }
/// ditto
        ref typeof(this) opAssign(M)(const M that) pure nothrow @nogc
            if(isCheckedInt!M || isScalarType!M)
        {
            checkImplicit!M();
            this.bscal = that.bscal;
            return this;
        }
        ///
        unittest {
            import checkedint.noex : SafeInt, to; // set No.throws

            // Only types that for which N can represent all values are accepted directly:
            SafeInt!int n = int.max;
            n = byte.max;
            n = wchar.max;

            // Values of a type that could be `< N.min` or `> N.max` are rejected at compile time:
            static assert(!__traits(compiles, n = long.max));
            static assert(!__traits(compiles, n = uint.max));
            static assert(!__traits(compiles, n = real.max));

            // Instead, use checkedint.to(), which does runtime bounds checking:
            n = to!int(315L);
            assert(n == 315);

            n = to!int(long.max);
            assert(IntFlags.local == IntFlag.posOver);

            IntFlags.local.clear();
        }

/**
Convert this value to floating-point. This always succeeds, although some loss of precision may
occur if M.sizeof <= N.sizeof.
*/
        M opCast(M)() const pure nothrow @nogc
            if(isFloatingPoint!M)
        {
            return cast(M)bscal;
        }
        ///
        unittest {
            import checkedint.throws : SafeInt; // set Yes.throws

            SafeInt!int n = 92;
            auto f = cast(double)n;
            static assert(is(typeof(f) == double));
            assert(f == 92.0);
        }

/// `this != 0`
        M opCast(M)() const pure nothrow @nogc
            if(is(M == bool))
        {
            return bscal != 0;
        }
        ///
        unittest {
            import checkedint.throws : SafeInt; // set Yes.throws

            SafeInt!int n = -315;
            assert( cast(bool)n);

            n = 0;
            assert(!cast(bool)n);
        }

/**
Convert this value to type `M` using `checkedint.to()` for bounds checking. An `IntFlag` will be raised if `M` cannot
represent the current value of this `SafeInt`.
*/
        M opCast(M)() const
            if(isCheckedInt!M || isIntegral!M || isSomeChar!M)
        {
            return to!(M, throws)(bscal);
        }
        ///
        unittest {
            import checkedint.noex : SafeInt; // set No.throws

            SafeInt!ulong n = 52uL;
            auto a = cast(int)n;
            static assert(is(typeof(a) == int));
            assert(!IntFlags.local);
            assert(a == 52);

            auto m = SafeInt!long(-1).mulPow2(n);
            auto b = cast(wchar)m;
            static assert(is(typeof(b) == wchar));
            assert(IntFlags.local == IntFlag.negOver);

            IntFlags.local.clear();
        }

/**
Convert this value to a type suitable for indexing an array:
$(UL
    $(LI If `N` is signed, a `ptrdiff_t` is returned.)
    $(LI If `N` is unsigned, a `size_t` is returned.)
)
`checkedint.to()` is used for bounds checking.
*/
        @property Select!(isSigned!N, ptrdiff_t, size_t) idx() const {
            return to!(typeof(return), throws)(bscal);
        }
        ///
        unittest {
            import checkedint.throws : SafeInt; // set Yes.throws

            char[3] arr = ['a', 'b', 'c'];
            SafeInt!long n = 1;

            // On 32-bit, `long` cannot be used directly for array indexing,
            static if(size_t.sizeof < long.sizeof)
                static assert(!__traits(compiles, arr[n]));
            // but idx can be used to concisely and safely cast to ptrdiff_t:
            assert(arr[n.idx] == 'b');

            // The conversion is bounds checked:
            static if(size_t.sizeof < long.sizeof) {
                n = long.min;
                try {
                    arr[n.idx] = '?';
                } catch(CheckedIntException e) {
                    assert(e.intFlags == IntFlag.negOver);
                }
            }
        }

/// Get a simple hashcode for this value.
        size_t toHash() const pure nothrow @nogc {
            static if(N.sizeof > size_t.sizeof) {
                static assert(N.sizeof == (2 * size_t.sizeof));
                return cast(size_t)bscal ^ cast(size_t)(bscal >>> 32);
            } else
                return cast(size_t)bscal;
        }

/// Get a `string` representation of this value.
        void toString(Writer, Char)(Writer sink, FormatSpec!Char fmt = (FormatSpec!Char).init) const @trusted {
            formatValue(sink, bscal, fmt); }
/// ditto
        string toString() const {
            return to!(string, No.throws)(bscal); }
        ///
        unittest {
            import checkedint.throws : safeInt; // set Yes.throws
            assert(safeInt(-753).toString() == "-753");
        }

        // Comparison /////////////////////////////////////////////////
/// See `safeOp`.
        bool opEquals(M)(const M right) const pure nothrow @nogc
            if(isSafeInt!M || isScalarType!M)
        {
            return safeOp!(throws).cmp!"=="(this.bscal, right.bscal);
        }
/**
Perform a floating-point comparison to `right`.

Returns: $(UL
    $(LI `-1` if this value is less than `right`.)
    $(LI ` 0` if this value is equal to `right`.)
    $(LI ` 1` if this value is greater than `right`.)
    $(LI `float.nan` if `right` is a floating-point `nan` value.))
*/
        auto opCmp(M)(const M right) const pure nothrow @nogc
            if(isFloatingPoint!M)
        {
            return
                (left <  right)? -1 :
                (left >  right)?  1 :
                (left == right)?  0 : float.nan;
        }
/// See `safeOp`.
        int opCmp(M)(const M right) const pure nothrow @nogc
            if(isSafeInt!M || isFixedPoint!M)
        {
            return safeOp!(throws).cmp(this.bscal, right.bscal);
        }

        // Unary /////////////////////////////////////////////////
/// ditto
        typeof(this) opUnary(string op)() const
            if(op.among!("-", "+", "~"))
        {
            static assert(bitOps || (op != "~"),
                "Bitwise operations are disabled.");

            return typeof(return)(safeOp!(throws).unary!op(bscal));
        }
/// ditto
        ref typeof(this) opUnary(string op)()
            if(op.among!("++", "--"))
        {
            safeOp!(throws).unary!op(bscal);
            return this;
        }

/// ditto
        typeof(this) abs() const {
            return typeof(return)(safeOp!(throws).abs(bscal)); }

/// Count the number of set bits using `core.bitop.popcnt()`.
        SafeInt!(int, throws, bitOps) popcnt()() const pure nothrow @nogc {
            static assert(bitOps, "Bitwise operations are disabled.");

            import future.bitop : stdPC = popcnt;
            return typeof(return)(stdPC(bscal));
        }

/// See `safeOp`.
        SafeInt!(int, throws, bitOps) bsf()() const {
            static assert(bitOps, "Bitwise operations are disabled.");

            return typeof(return)(safeOp!(throws).bsf(bscal));
        }
/// ditto
        SafeInt!(int, throws, bitOps) bsr()() const {
            static assert(bitOps, "Bitwise operations are disabled. Consider using ilogb() instead?");

            return typeof(return)(safeOp!(throws).bsr(bscal));
        }

/// ditto
        SafeInt!(int, throws, bitOps) ilogb() const {
            return typeof(return)(safeOp!(throws).ilogb(bscal)); }

        // Binary /////////////////////////////////////////////////
/// Perform a floating-point math operation.
        M opBinaryRight(string op, M)(const M left) const pure nothrow @nogc
            if(isFloatingPoint!M)
        {
            return mixin("left " ~ op ~ " bscal");
        }
/// ditto
        M opBinary(string op, M)(const M right) const pure nothrow @nogc
            if(isFloatingPoint!M)
        {
            return mixin("bscal " ~ op ~ " right");
        }
/// See `safeOp`.
        SafeInt!(OpType!(M, op, N), throws, bitOps) opBinaryRight(string op, M)(const M left) const
            if(isFixedPoint!M)
        {
            static assert(bitOps || !op.among!("<<", ">>", ">>>", "&", "|", "^"),
                "Bitwise operations are disabled. Consider using mulPow2(), divPow2(), or modPow2() instead?");

            return typeof(return)(safeOp!(throws).binary!op(left, bscal));
        }
/// ditto
        SafeInt!(OpType!(N, op, BasicScalar!M), throws || isThrowingCInt!M, bitOps && hasBitOps!M) opBinary(string op, M)(const M right) const
            if(isSafeInt!M || isFixedPoint!M)
        {
            static assert(bitOps && hasBitOps!M || !op.among!("<<", ">>", ">>>", "&", "|", "^"),
                "Bitwise operations are disabled. Consider using mulPow2(), divPow2(), or modPow2() instead?");

            return typeof(return)(safeOp!(throws || isThrowingCInt!M).binary!op(this.bscal, right.bscal));
        }
/// ditto
        ref typeof(this) opOpAssign(string op, M)(const M right)
            if(isCheckedInt!M || isFixedPoint!M)
        {
            static assert((bitOps && hasBitOps!M) || !op.among!("<<", ">>", ">>>", "&", "|", "^"),
                "Bitwise operations are disabled. Consider using mulPow2(), divPow2(), or modPow2() instead?");
            checkImplicit!(OpType!(N, op, BasicScalar!M))();

            safeOp!(throws || isThrowingCInt!M).binary!(op ~ "=")(this.bscal, right.bscal);
            return this;
        }

/// ditto
        auto mulPow2(M)(const M exp) const pure nothrow @nogc
            if(isFloatingPoint!M)
        {
            return safeOp!(throws).mulPow2(bscal, exp);
        }
/// ditto
        auto mulPow2(M)(const M exp) const
            if(isCheckedInt!M || isFixedPoint!M)
        {
            enum mixThrows = throws || isThrowingCInt!M;
            const wret = safeOp!(mixThrows).mulPow2(this.bscal, exp.bscal);
            return SafeInt!(typeof(wret), mixThrows, bitOps && hasBitOps!M)(wret);
        }
/// ditto
        auto divPow2(M)(const M exp) const pure nothrow @nogc
            if(isFloatingPoint!M)
        {
            return safeOp!(throws).divPow2(bscal, exp);
        }
/// ditto
        auto divPow2(M)(const M exp) const
            if(isCheckedInt!M || isFixedPoint!M)
        {
            enum mixThrows = throws || isThrowingCInt!M;
            const wret = safeOp!(mixThrows).divPow2(this.bscal, exp.bscal);
            return SafeInt!(typeof(wret), mixThrows, bitOps && hasBitOps!M)(wret);
        }
/// ditto
        auto modPow2(M)(const M exp) const pure nothrow @nogc
            if(isFloatingPoint!M)
        {
            return safeOp!(throws).modPow2(bscal, exp);
        }
/// ditto
        auto modPow2(M)(const M exp) const
            if(isCheckedInt!M || isFixedPoint!M)
        {
            enum mixThrows = throws || isThrowingCInt!M;
            const wret = safeOp!(mixThrows).modPow2(this.bscal, exp.bscal);
            return SafeInt!(typeof(wret), mixThrows, bitOps && hasBitOps!M)(wret);
        }

/// Raise `this` to the `exp` power using `std.math.pow()`.
        M pow(M)(const M exp) const pure nothrow @nogc
            if(isFloatingPoint!M)
        {
            return std.math.pow(bscal, exp);
        }
/// See `safeOp`.
        SafeInt!(CallType!(std.math.pow, N, BasicScalar!M), throws || isThrowingCInt!M, bitOps && hasBitOps!M) pow(M)(const M exp) const
            if(isCheckedInt!M || isFixedPoint!M)
        {
            return typeof(return)(safeOp!(throws || isThrowingCInt!M).pow(this.bscal, exp.bscal));
        }
    }
/// ditto
    template SafeInt(N, Flag!"throws" throws, Flag!"bitOps" bitOps = Yes.bitOps)
        if((isIntegral!N && !isUnqual!N) || isCheckedInt!N)
    {
        alias SafeInt = SafeInt!(BasicScalar!N, throws, bitOps);
    }
    ///
    unittest {
        // Mixing standard signed and unsigned types is dangerous...
        int ba = -1;
        uint bb = 0;
        assert(ba > bb);

        auto bc = ba + bb;
        assert(is(typeof(bc) == uint));
        assert(bc == 4294967295u);

        // ...that's why SafeInt won't let you do it.
        import checkedint.throws : SafeInt, to; // set Yes.throws

        SafeInt!int sa = -1;
        SafeInt!uint sb = 0u;
        assert(!__traits(compiles, sa < sb));
        assert(!__traits(compiles, sa + sb));

        // Instead, use checkedint.to() to safely convert to a common type...
        auto sbi = to!(SafeInt!int)(sb);
        assert(sa < sbi);
        auto sc = sa + sbi;
        assert(sc == -1);
        // (...or just switch to SmartInt.)
    }
    ///
    unittest {
        // When Yes.throws is set, SafeInt operations that fail at runtime will throw a CheckedIntException.
        import checkedint.throws : SafeInt;

        SafeInt!uint sa = 1u;
        SafeInt!uint sb = 0u;

        bool overflow = false;
        try {
            SafeInt!uint sc = sb - sa;
            assert(false);
        } catch(CheckedIntException e) {
            assert(e.intFlags == IntFlag.negOver);
            overflow = true;
        }
        assert(overflow);

        bool div0 = false;
        try {
            // With standard integers, this would crash the program with an unrecoverable FPE...
            SafeInt!uint sc = sa / sb;
            assert(false);
        } catch(CheckedIntException e) {
            // ...but with SafeInt, it just throws a normal Exception.
            assert(e.intFlags == IntFlag.div0);
            div0 = true;
        }
        assert(div0);
    }
    ///
    unittest {
        // When No.throws is set, SafeInt operations that fail at runtime set one or more bits in IntFlags.local.
        import checkedint.noex : SafeInt;

        SafeInt!uint sa = 1u;
        SafeInt!uint sb = 0u;
        SafeInt!uint sc;

        sc = sb - sa;
        assert(IntFlags.local == IntFlag.negOver);

        // With standard integers, this would crash the program with an unrecoverable FPE...
        sc = sa / sb;
        // ...but with SmartInt, it just sets a bit in IntFlags.local.
        assert(IntFlags.local & IntFlag.div0);

        // Each flag will remain set until cleared:
        assert(IntFlags.local == (IntFlag.negOver | IntFlag.div0));
        IntFlags.local.clear();
        assert(!IntFlags.local);

        IntFlags.local.clear();
    }

    private template SafeInt(N, bool throws, bool bitOps)
        if(isIntegral!N)
    {
        alias SafeInt = SafeInt!(
            Unqual!N,
            cast(Flag!"throws")throws,
            cast(Flag!"bitOps")bitOps);
    }

/// Get the value of `num` as a `SafeInt!N`. The integral type `N` can be infered from the argument.
    SafeInt!(N, throws, bitOps) safeInt(Flag!"throws" throws, Flag!"bitOps" bitOps = Yes.bitOps, N)(N num)
        if(isIntegral!N || isCheckedInt!N)
    {
        return typeof(return)(num.bscal);
    }
    ///
    unittest {
        import checkedint.throws : safeInt, SafeInt; // set Yes.throws

        auto a = safeInt(55uL);
        static assert(is(typeof(a) == SafeInt!ulong));
        assert(a == 55u);
    }

/**
Implements various integer math operations with error checking.

`safeOp` strives to mimic the standard integer math operations in every way, except:
$(UL
    $(LI If the operation is generally untrustworthy - for example, signed/unsigned comparisons - a compile-time error
        is generated. The message will usually suggest a workaround.)
    $(LI At runtime, if the result is mathematically incorrect an appropriate `IntFlag` will be raised.)
)
The runtime error-signalling policy may be selected using the `throws` template parameter.
*/
    template safeOp(Flag!"throws" throws) {
        // NOTE: Condition is inverted because ddoc only scans the first branch of a static if
        static if(!throws) {
        // No need to redundantly instantiate members which don't depend on `throws`.

            private void cmpTypeCheck(N, M)() pure nothrow @nogc {
                static assert(isBoolean!N == isBoolean!M,
                    "The intent of a direct comparison of " ~
                    N.stringof ~ " with " ~ M.stringof ~
                    " is unclear. Add an explicit cast."
                );

                alias OT = OpType!(N, "+", M);
                static assert(isFloatingPoint!OT || isSigned!OT || !(isSigned!N || isSigned!M),
                    "The standard signed/unsigned comparisons of " ~ N.stringof ~ " to " ~ M.stringof ~
                    " are unsafe. Use an explicit cast, or switch to smartOp/SmartInt."
                );
            }

/**
Compare `left` and `right` using `op`.

Unsafe signed/unsigned comparisons will trigger a compile-time error. Possible solutions include:
$(UL
    $(LI Should the inputs really have different signedness? Changing the type of one to match the other is the simplest
        solution.)
    $(LI Consider using `smartOp.cmp`, instead, as it can safely do signed/unsigned comparisons.)
    $(LI Alternately, `checkedint.to()` can be used to safely convert the type of one input, with runtime bounds
        checking.)
) $(BR)
Direct comparisons between boolean values and numeric ones are also forbidden. Make your intention explicit:
$(UL
    $(LI `cast(N)boolean == numeric`)
    $(LI `boolean == (numeric != 0)`)
)
*/
            bool cmp(string op, N, M)(const N left, const M right) pure nothrow @nogc
                if(isScalarType!N && isScalarType!M)
            {
                cmpTypeCheck!(N, M)();
                return mixin("left " ~ op ~ " right");
            }

// TODO: Should this even be here? Should it support signed/unsigned comparisons?
            int cmp(N, M)(const N left, const M right) pure nothrow @nogc
                if(isScalarType!N && isScalarType!M)
            {
                cmpTypeCheck!(N, M)();

                static if(isFloatingPoint!N || isFloatingPoint!M) {
                    import future.math : stdCmp = cmp;
                    return stdCmp(left, right);
                } else
                    return (left < right)? -1 : (right < left);
            }
        } else
            alias cmp = safeOp!(No.throws).cmp;

/**
Perform the unary (single-argument) integer operation specified by `op`.

Trying to negate `-` an unsigned value will generate a compile-time error, because mathematically, the result should
always be negative (except for -0), but the unsigned return type cannot represent this.

`++` and `--` are checked for overflow at runtime, and will raise `IntFlag.posOver` or `IntFlag.negOver` if needed.
*/
        N unary(string op, N)(const N num)
            if((isIntegral!N) && op.among!("-", "+", "~"))
        {
            static assert(isSigned!N || op != "-",
                "The standard unary - operation for " ~ N.stringof ~
                " is unsafe. Use an explicit cast to a signed type, or switch to smartOp/SmartInt."
            );

            static if(op == "-") {
                static if(is(N == int) || is(N == long)) {
                    bool over = false;
                    const N ret = negs(num, over);
                } else {
                    const over = (num <= trueMin!N);
                    const N ret = -num;
                }

                if(over)
                    IntFlag.posOver.raise!throws();

                return ret;
            } else
                return mixin(op ~ "num");
        }
/// ditto
        /+ref+/ N unary(string op, N)(/+return+/ ref N num)
            if((isIntegral!N) && op.among!("++", "--"))
        {
            static if(op == "++") {
                if(num >= trueMax!N)
                    IntFlag.posOver.raise!throws();
            } else
            static if(op == "--") {
                if(num <= trueMin!N)
                    IntFlag.negOver.raise!throws();
            }

            return mixin(op ~ "num");
        }

/**
Get the absolute value of `num`.

`IntFlag.posOver` is raised if `N` is signed and `num == N.min`.
*/
        N abs(N)(const N num)
            if(isIntegral!N || isBoolean!N)
        {
            static if(isSigned!N) {
                if(num < 0)
                    return unary!"-"(num);
            }
            return num;
        }

/// `core.bitop.bsf` without the undefined behaviour. `safeOp.bsf(0)` will raise `IntFlag.undef`.
        int bsf(N)(const N num)
            if(isFixedPoint!N)
        {
            return bsfImpl!throws(num);
        }
/// `core.bitop.bsr` without the undefined behaviour. `safeOp.bsr(0)` will raise `IntFlag.undef`.
        int bsr(N)(const N num)
            if(isFixedPoint!N)
        {
            return bsrImpl!throws(num);
        }

/**
Get the base 2 logarithm of `abs(num)`, rounded down to the nearest integer.

`safeOp.ilogb(0)` will raise `IntFlag.undef`.
*/
        int ilogb(N)(const N num)
            if(isFixedPoint!N)
        {
            static if(isSigned!N)
                const absN = cast(Unsigned!N) (num < 0? -num : num);
            else
                alias absN = num;

            return bsrImpl!throws(absN);
        }

        private auto binaryImpl(string op, N, M)(const N left, const M right)
            if(isFixedPoint!N && isFixedPoint!M)
        {
            enum wop = (op[$-1] == '=')? op[0 .. $-1] : op;
            alias P = OpType!(N, wop, M);
            alias R = Select!(wop == op, P, N);

            static if(wop.among!("+", "-", "*")) {
                enum isPromSafe = !(isSigned!N || isSigned!M) || (isSigned!P && isSigned!R);
                enum needCOp = (wop == "*")?
                    (precision!N + precision!M) > precision!P :
                    (max(precision!N, precision!M) + 1) > precision!P;

                bool over = false;
                static if(needCOp) {
                    enum cx = (staticIndexOf!(wop, "+", "-", "*") << 1) + isSigned!P;
                    alias cop = AliasSeq!(addu, adds, subu, subs, mulu, muls)[cx];

                    const pR = cop(cast(P)left, cast(P)right, over);
                } else
                    const pR = mixin("left " ~ wop ~ " right");

                static if(isSigned!P && trueMin!P < trueMin!R) {
                    if(pR < trueMin!R)
                        over = true;
                }
                static if(trueMax!P > trueMax!R) {
                    if(pR > trueMax!R)
                        over = true;
                }

                if(over)
                    IntFlag.over.raise!throws();
                return cast(R)pR;
            } else
            static if(wop.among!("/", "%")) {
                enum isPromSafe = !(isSigned!N || isSigned!M) ||
                    (isSigned!P && (wop == "%"? (isSigned!R || !isSigned!N) : isSigned!R));

                const div0 = (right == 0);
                static if(isSigned!N && isSigned!M)
                    const posOver = (left == trueMin!R) && (right == -1);
                else
                    enum posOver = false;

                R ret = void;
                if(div0 || posOver) {
                    (posOver? IntFlag.posOver : IntFlag.div0).raise!throws();
                    ret = 0; // Prevent unrecoverable FPE
                } else
                    ret = cast(R)mixin("left " ~ wop ~ " right");

                return ret;
            } else
            static if(wop.among!("<<", ">>", ">>>")) {
                enum isPromSafe = !isSigned!N || isSigned!R || (op == ">>>");

                enum invalidSh = ~cast(M)(8 * P.sizeof - 1);
                if(right & invalidSh)
                    IntFlag.undef.raise!throws();

                return cast(R) mixin("cast(P)left " ~ wop ~ " right");
            } else
            static if(wop.among!("&", "|", "^")) {
                enum isPromSafe = true;

                return cast(R)mixin("left " ~ wop ~ " right");
            } else
                static assert(false);

            static assert(isPromSafe,
                "The standard " ~ N.stringof ~ " " ~ op ~ " " ~ M.stringof ~
                " operation is unsafe, due to a signed/unsigned mismatch. " ~
                "Use an explicit cast, or switch to smartOp/SmartInt."
            );
        }

/**
Perform the binary (two-argument) integer operation specified by `op`.
$(UL
    $(LI Unsafe signed/unsigned operations will generate a compile-time error.)
    $(LI `+`, `-`, `*`, `/`, and `%` are checked for overflow at runtime.)
    $(LI `/` and `%` are also checked for divide-by-zero.)
    $(LI `<<`, `>>`, and `>>>` are checked to verify that `right >= 0` and `right < (8 * typeof(left).sizeof)`.
        Otherwise, `IntFlag.undef` is raised.)
) $(BR)
Note also:
$(UL
    $(LI The shift operators are $(B $(RED not)) checked for overflow and should not be used for multiplication,
        division, or exponentiation. Instead, use `mulPow2()` and `divPow2()`, which internally use the bitshifts for speed,
        but check for overflow and correctly handle negative values.)
    $(LI Likewise, `modPow2()` should be used for remainders instead of `&`.)
    $(LI `^^` and `^^=` will remain disabled in favour of `pow` until DMD issues 15288 and 15412 are fixed.)
) $(BR)
Like the standard equiavlents, the assignment operators (`+=`, `-=`, `*=`, etc.) take `left` by `ref` and will overwrite
it with the result of the operation.
*/
        OpType!(N, op, M) binary(string op, N, M)(const N left, const M right)
            if(isFixedPoint!N && isFixedPoint!M &&
                op.among!("+", "-", "*", "/", "%", "^^", "<<", ">>", ">>>", "&", "|", "^"))
        {
            static assert(op != "^^",
                "pow() should be used instead of operator ^^ because of issue 15288.");

            return binaryImpl!op(left, right);
        }
/// ditto
        /+ref+/ N binary(string op, N, M)(/+return+/ ref N left, const M right)
            if(isIntegral!N && isFixedPoint!M && (op[$ - 1] == '='))
        {
            static assert(op != "^^=",
                "pow() should be used instead of operator ^^= because of issue 15412.");

            left = binaryImpl!op(left, right);
            return left;
        }

/**
Equivalent to `left * pow(2, exp)`, but faster and works with a wider range of inputs. This is a safer alternative to
`left << exp` that is still very fast.

Note that (conceptually) rounding occurs $(I after) the `*`, meaning that `mulPow2(left, -exp)` is equivalent to
`divPow2(left, exp)`.
*/
        auto mulPow2(N, M)(const N left, const M exp) pure nothrow @nogc
            if((isFloatingPoint!N && isScalarType!M) || (isScalarType!N && isFloatingPoint!M))
        {
            return byPow2Impl!("*", NumFromScal!N, NumFromScal!M)(left, exp);
        }
/// ditto
        auto mulPow2(N, M)(const N left, const M exp)
            if(isFixedPoint!N && isFixedPoint!M)
        {
            return byPow2Impl!("*", throws, NumFromScal!N, NumFromScal!M)(left, exp);
        }

/**
Equivalent to `left / pow(2, exp)`, but faster and works with a wider range of inputs. This is a safer alternative to
`left >> exp` that is still very fast.

Note that (conceptually) rounding occurs $(I after) the `/`, meaning that `divPow2(left, -exp)` is equivalent to
`mulPow2(left, exp)`.
*/
        auto divPow2(N, M)(const N left, const M exp) pure nothrow @nogc
            if((isFloatingPoint!N && isScalarType!M) || (isScalarType!N && isFloatingPoint!M))
        {
            return byPow2Impl!("/", NumFromScal!N, NumFromScal!M)(left, exp);
        }
/// ditto
        auto divPow2(N, M)(const N left, const M exp)
            if(isFixedPoint!N && isFixedPoint!M)
        {
            return byPow2Impl!("/", throws, NumFromScal!N, NumFromScal!M)(left, exp);
        }

/**
Equivalent to `left % pow(2, exp)`, but faster and works with a wider range of inputs. This is a safer alternative to
`left & ((1 << exp) - 1)` that is still very fast.
*/
        auto modPow2(N, M)(const N left, const M exp) pure nothrow @nogc
            if((isFloatingPoint!N && isScalarType!M) || (isScalarType!N && isFloatingPoint!M))
        {
            return byPow2Impl!("%", NumFromScal!N, NumFromScal!M)(left, exp);
        }
/// ditto
        auto modPow2(N, M)(const N left, const M exp) pure nothrow @nogc
            if(isFixedPoint!N && isFixedPoint!M)
        {
            return byPow2Impl!("%", No.throws, NumFromScal!N, NumFromScal!M)(left, exp);
        }

/**
Raise `base` to the `exp` power.

Errors that may be signalled if neither input is floating-point:
$(UL
    $(LI `IntFlag.posOver` or `IntFlag.negOver` if the absolute value of the result is too large to
        represent with the return type.)
    $(LI `exp < 0`, `IntFlag.undef` is raised because `std.math.pow` would trigger an FPE given the same input.)
)
*/
        CallType!(std.math.pow, N, M) pow(N, M)(const N base, const M exp)
            if(isFixedPoint!N && isFixedPoint!M)
        {
            alias R = typeof(return);
            static assert(!isSigned!N || isSigned!R,
                "std.math.pow(" ~ N.stringof ~ ", " ~ M.stringof ~
                ") is unsafe, due to a signed/unsigned mismatch. Use an explicit cast, or switch to smartOp/SmartInt."
            );

            auto po = powImpl!(R, Select!(isSigned!M, long, ulong))(base, exp);
            static assert(is(typeof(po.num) == R));
            if(exp < 0)
                po.flag = IntFlag.undef;

            if(!po.flag.isNull)
                po.flag.raise!throws();
            return po.num;
        }
    }
    private alias safeOp(bool throws) = safeOp!(cast(Flag!"throws")throws);

// conv /////////////////////////////////////////////////

/**
A wrapper for `std.conv.to` which uses `checkedint.flags` for error signaling when converting between any combination
of basic scalar types and `checkedint` types. This allows `checkedint.to()` to be used for numeric conversions in
`nothrow` code, unlike `std.conv.to`.

Conversions involving any other type are simply forwarded to `std.conv.to`, with no runtime overhead.
*/
    template to(T, Flag!"throws" throws)
    {
        private enum useFlags(S) = (isCheckedInt!T || isScalarType!T) && (isCheckedInt!S || isScalarType!S);

        T to(S)(const S value)
            if(useFlags!S)
        {
            static if(isCheckedInt!T || isCheckedInt!S)
                return T(checkedint.to!(BasicScalar!T, throws)(value.bscal));
            else {
                static if(! isFloatingPoint!T) {
                    static if(isFloatingPoint!S) {
                        if(value >= trueMin!T) {
                            if(value > trueMax!T)
                                IntFlag.posOver.raise!throws();
                        } else
                            (std.math.isNaN(value)? IntFlag.undef : IntFlag.negOver).raise!throws();
                    } else {
                        static if(cast(long)trueMin!S < cast(long)trueMin!T) {
                            if(value < cast(S)trueMin!T)
                                IntFlag.negOver.raise!throws();
                        }
                        static if(cast(ulong)trueMax!S > cast(ulong)trueMax!T) {
                            if(value > cast(S)trueMax!T)
                                IntFlag.posOver.raise!throws();
                        }
                    }
                }
                return cast(T)value;
            }
        }

        import std.conv : impl = to;
        static if(throws) {
            T to(S)(S value)
                if(! useFlags!S)
            {
                return impl!T(value);
            }
        } else {
            T to(S)(S value) nothrow
                if(! useFlags!S)
            {
                 return impl!T(value);
            }
        }
    }
    ///
    unittest {
        // Conversions involving only basic scalars or checkedint types use IntFlags for error signalling.
        import checkedint.noex : smartInt, SmartInt, smartOp, to; // set No.throws

        assert(to!int(smartInt(-421751L)) == -421751);
        assert(to!(SmartInt!ubyte)(100) == 100u);

        assert(is(typeof(to!int(50u)) == int));
        assert(to!int(50u) == 50);
        assert(!IntFlags.local);

        // If No.throws is set, failed conversions return garbage, but...
        assert(smartOp.cmp!"!="(to!int(uint.max), uint.max));
        // ...IntFlags.local can be checked to see if anything went wrong.
        assert(IntFlags.local & IntFlag.posOver);

        IntFlags.local.clear();
    }
    ///
    unittest {
        // Everything else forwards to std.conv.to.
        assert(to!(string, Yes.throws)(55) == "55");
        assert(to!(real, Yes.throws)("3.141519e0") == 3.141519L);

        // Setting No.throws will block std.conv.to, unless the instantiation is nothrow.
        assert(!__traits(compiles, to!(real, No.throws)("3.141519e0")));
    }

    @property {
/**
Get a view or copy of `num` as a basic scalar.

Useful in generic code that handles both basic types, and `checkedint` types.
*/
      /+ref inout(N) bscal(N)(return ref inout(N) num)
            if(isScalarType!N)
        {
            return num;
        }
/// ditto
        ref inout(N) bscal(N)(return ref inout(N) num)
            if(isCheckedInt!N)
        {
            return num.bscal;
        }
/// ditto +/
        N bscal(N)(const N num)
            if(isScalarType!N)
        {
            return num;
        }
/// ditto
        BasicScalar!N bscal(N)(const N num)
            if(isCheckedInt!N)
        {
            return num.bscal;
        }
        ///
        unittest {
            import checkedint.throws : smartInt, SmartInt; // set Yes.throws

            assert(is(typeof(bscal(2u)) == uint));
            assert(is(typeof(bscal(SmartInt!int(2))) == int));

            assert(bscal(-3153) == -3153);
            assert(bscal(smartInt(75_000)) == 75_000);
        }

/**
Get a view or copy of `num` that supports bitwise operations.

Useful in generic code that handles both basic types and `checkedint` types.
*/
      /+ref inout(N) bits(N)(return ref inout(N) num)
            if(isFixedPoint!N)
        {
            return num;
        }
/// ditto
        ref inout(N) bits(N)(return ref inout(N) num)
            if(isCheckedInt!N)
        {
            return num.bits;
        }
/// ditto +/
        N bits(N)(const N num)
            if(isFixedPoint!N)
        {
            return num;
        }
/// ditto
        SmartInt!(BasicScalar!N, isThrowingCInt!N, Yes.bitOps) bits(N)(const N num)
            if(isSmartInt!N)
        {
            return num.bits;
        }
/// ditto
        SafeInt!(BasicScalar!N, isThrowingCInt!N, Yes.bitOps) bits(N)(const N num)
            if(isSafeInt!N)
        {
            return num.bits;
        }
        ///
        unittest {
            import checkedint.throws : SmartInt; // set Yes.throws

            assert(is(typeof(bits(5)) == int));

            SmartInt!(int, No.bitOps) noBits = 5;
            assert(is(typeof(bits(noBits)) == SmartInt!(int, Yes.bitOps)));

            assert(!__traits(compiles, noBits << 2));
            assert((bits(noBits) << 2) == 20);
        }

/**
Cast `num` to a basic type suitable for indexing an array.

For signed types, `ptrdiff_t` is returned. For unsigned types, `size_t` is returned.
*/
        Select!(isSigned!N, ptrdiff_t, size_t) idx(N)(const N num)
            if(isScalarType!N)
        {
            // TODO: use to()
            return cast(typeof(return))(num);
        }
/// ditto
        Select!(isSigned!(BasicScalar!N), ptrdiff_t, size_t) idx(N)(const N num)
            if(isCheckedInt!N)
        {
            return num.idx;
        }
        ///
        unittest {
            import checkedint.throws : SmartInt, safeInt; // set Yes.throws

            assert(is(typeof(idx(cast(long)1)) == ptrdiff_t));
            assert(is(typeof(idx(cast(ubyte)1)) == size_t));
            assert(is(typeof(idx(SmartInt!ulong(1))) == size_t));

            assert(idx(17uL) == 17);
            assert(idx(-3) == -3);
            assert(idx(safeInt(cast(byte)100)) == 100);

            // TODO: Demonstrate how out-of-bounds values are handled.
        }
    }
/+}+/

// traits /////////////////////////////////////////////////

/// Evaluates to `true` if `T` is an instance of `SafeInt`.
enum isSafeInt(T) = isInstanceOf!(SafeInt, T);
///
unittest {
    import checkedint.throws : SmartInt, SafeInt; // set Yes.throws

    assert( isSafeInt!(SafeInt!int));

    assert(!isSafeInt!int);
    assert(!isSafeInt!(SmartInt!int));
}

/// Evaluates to `true` if `T` is an instance of `SmartInt`.
enum isSmartInt(T) = isInstanceOf!(SmartInt, T);
///
unittest {
    import checkedint.throws : SmartInt, SafeInt; // set Yes.throws

    assert( isSmartInt!(SmartInt!int));

    assert(!isSmartInt!int);
    assert(!isSmartInt!(SafeInt!int));
}

/// Evaluates to `true` if `T` is an instance of `SafeInt` or `SmartInt`.
enum isCheckedInt(T) = isSafeInt!T || isSmartInt!T;
///
unittest {
    import checkedint.throws : SafeInt, SmartInt; // set Yes.throws

    assert( isCheckedInt!(SafeInt!int));
    assert( isCheckedInt!(SmartInt!int));

    assert(!isCheckedInt!int);
}

/**
Evaluates to `true` if either:
$(UL
    $(LI `isScalarType!T`, or)
    $(LI `isCheckedInt!T`)
)
$(B And) bitwise operators such as `<<` and `~` are available for `T`.
*/
template hasBitOps(T) {
    static if(isCheckedInt!T)
        enum hasBitOps = TemplateArgsOf!T[2];
    else
        enum hasBitOps = isFixedPoint!T;
}
///
unittest {
    import checkedint.throws : SafeInt, SmartInt; // set Yes.throws

    assert( hasBitOps!(SafeInt!(int, Yes.bitOps)));
    assert( hasBitOps!(SmartInt!(int, Yes.bitOps)));
    assert( hasBitOps!int);
    assert( hasBitOps!bool);
    assert( hasBitOps!dchar);

    assert(!hasBitOps!(SafeInt!(int, No.bitOps)));
    assert(!hasBitOps!(SmartInt!(int, No.bitOps)));
    assert(!hasBitOps!float);
}

/**
Evaluates to `true` if `isCheckedInt!T` and failed operations on `T` will `throw` a
$(LINK2 ./flags.html#CheckedIntException, `CheckedIntException`).
*/
template isThrowingCInt(T) {
    static if(isCheckedInt!T)
        enum isThrowingCInt = TemplateArgsOf!T[1];
    else
        enum isThrowingCInt = false;
}
///
unittest {
    assert( isThrowingCInt!(SafeInt!(int, Yes.throws)));
    assert( isThrowingCInt!(SmartInt!(int, Yes.throws)));

    assert(!isThrowingCInt!(SafeInt!(int, No.throws)));
    assert(!isThrowingCInt!(SmartInt!(int, No.throws)));
    assert(!isThrowingCInt!int);
}

/**
Aliases to the basic scalar type associated with `T`, assuming either:
$(UL
    $(LI `isScalarType!T`, or)
    $(LI `isCheckedInt!T`)
)
Otherwise, `BasicScalar` aliases to `void`.
*/
template BasicScalar(T) {
    static if(isScalarType!T)
        alias BasicScalar = Unqual!T;
    else
    static if(isCheckedInt!T)
        alias BasicScalar = TemplateArgsOf!T[0];
    else
        alias BasicScalar = void;
}
///
unittest {
    import checkedint.throws : SafeInt, SmartInt; // set Yes.throws

    assert(is(BasicScalar!(SafeInt!int) == int));
    assert(is(BasicScalar!(SmartInt!ushort) == ushort));

    assert(is(BasicScalar!int == int));
    assert(is(BasicScalar!(const shared real) == real));
}

// internal /////////////////////////////////////////////////
private {
    enum N trueMin(N) = mostNegative!N;
    template trueMax(N)
        if(isScalarType!N)
    {
        static if(is(Unqual!N == dchar))
            enum N trueMax = ~cast(N)0;
        else
            enum N trueMax = N.max;
    }

    template NumFromScal(N)
        if(isScalarType!N)
    {
        static if(isNumeric!N)
            alias NumFromScal = N;
        else
        static if(isSomeChar!N)
            alias NumFromScal = IntFromChar!N;
        else //if(isBoolean!N)
            alias NumFromScal = ubyte;
    }

    /+pragma(inline, true) {+/
        int bsfImpl(Flag!"throws" throws, N)(const N num)
            if(isFixedPoint!N)
        {
            static if(isSigned!N)
                return bsfImpl!(throws, Unsigned!N)(num);
            else {
                static assert(N.sizeof <= ulong.sizeof);

                int ret = void;
                if(num == 0) {
                    IntFlag.undef.raise!throws();
                    ret = int.min;
                } else
                    ret = bsf(num);

                return ret;
            }
        }
        int bsrImpl(Flag!"throws" throws, N)(const N num)
            if(isFixedPoint!N)
        {
            static if(isSigned!N)
                return bsrImpl!(throws, Unsigned!N)(num);
            else {
                static assert(N.sizeof <= ulong.sizeof);

                int ret = void;
                if(num == 0) {
                    IntFlag.undef.raise!throws();
                    ret = int.min;
                } else
                    ret = bsr(num);

                return ret;
            }
        }

        auto byPow2Impl(string op, N, M)(const N left, const M exp) pure nothrow @nogc
            if(op.among!("*", "/", "%") && ((isFloatingPoint!N && isNumeric!M) || (isNumeric!N && isFloatingPoint!M)))
        {
            import std.math : exp2, isFinite, frexp, ldexp;

            enum wantPrec = max(precision!N, precision!M);
            alias R =
                Select!(wantPrec <= precision!float, float,
                Select!(wantPrec <= precision!double, double, real));

            static if(isFloatingPoint!M) {
                R ret = void;

                static if(op.among!("*", "/")) {
                    if(left == 0 && exp.isFinite)
                        ret = 0;
                    else {
                        R wexp = cast(R)exp;
                        static if(op == "/")
                            wexp = -wexp;

                        ret = cast(R)left * exp2(wexp);
                    }
                } else {
                    const p2 = exp2(cast(R)exp);
                    ret =
                        p2.isFinite? cast(R)left % p2 :
                        (p2 > 0)? cast(R)left :
                        (p2 < 0)? cast(R)0 :
                        R.nan;
                }

                return ret;
            } else {
                static if(op.among!("*", "/")) {
                    int wexp =
                        (exp > int.max)? int.max :
                        (cast(long)exp < -int.max)? -int.max : cast(int)exp;
                    static if(op == "/")
                        wexp = -wexp;

                    return ldexp(cast(R)left, wexp);
                } else {
                    int expL;
                    real mantL = frexp(left, expL);

                    static if(!isSigned!M)
                        const retL = expL <= exp;
                    else
                        const retL = (expL < 0) || (expL <= exp);

                    R ret = void;
                    if(retL)
                        ret = left;
                    else {
                        const expDiff = expL - exp;
                        ret = (expDiff > N.mant_dig)?
                            cast(R)0 :
                            left - ldexp(floor(ldexp(mantissa, expDiff)), expL - expDiff);
                    }

                    return ret;
                }
            }
        }
        auto byPow2Impl(string op, Flag!"throws" throws, N, M)(const N left, const M exp)
            if(op.among!("*", "/", "%") && isIntegral!N && isIntegral!M)
        {
            alias R = Select!(op.among!("*", "/") != 0, Promoted!N, N);
            enum Unsigned!M maxSh = 8 * N.sizeof - 1;

            R ret = void;
            static if(op.among!("*", "/")) {
                const rc = cast(R)left;
                const negE = exp < 0;
                const absE = cast(Unsigned!M)(negE?
                    -exp :
                     exp);
                const bigSh = (absE > maxSh);

                R back = void;
                if((op == "*")? negE : !negE) {
                    if(bigSh)
                        ret = 0;
                    else {
                        // ">>" rounds as floor(), but we want trunc() like "/"
                        ret = (rc < 0)?
                            -(-rc >>> absE) :
                            rc >>> absE;
                    }
                } else {
                    if(bigSh) {
                        ret = 0;
                        back = 0;
                    } else {
                        ret  = rc  << absE;
                        back = ret >> absE;
                    }

                    if(back != rc)
                        IntFlag.over.raise!throws();
                }
            } else {
                if(exp & ~maxSh)
                    ret = (exp < 0)? 0 : left;
                else {
                    const mask = ~(~cast(N)0 << exp);
                    ret = cast(R)(left < 0?
                        -(-left & mask) :
                         left & mask);
                }
            }

            return ret;
        }
    /+}+/

    struct PowOut(B) {
        B num;
        IntFlag flag;
    }

    /+pragma(inline, false)+/ // Minimize template bloat by using a common pow() implementation
    PowOut!B powImpl(B, E)(const B base, const E exp)
        if((is(B == int) || is(B == uint) || is(B == long) || is(B == ulong)) &&
            (is(E == long) || is(E == ulong)))
    {
        PowOut!B ret;

        static if(isSigned!B) {
            alias cmul = muls;
            const smallB = (1 >= base && base >= -1);
        } else {
            alias cmul = mulu;
            const smallB = (base <= 1);
        }

        if(smallB) {
            if(base == 0) {
                static if(isSigned!E) {
                    if(exp < 0)
                        ret.flag = IntFlag.div0;
                }

                ret.num = (exp == 0);
            } else
                ret.num = (exp & 0x1)? base : 1;

            return ret;
        }
        if(exp <= 0) {
            ret.num = (exp == 0);
            return ret;
        }

        ret.num = 1;
        if(exp <= precision!B) {
            B b = base;
            int e = cast(int)exp;
            if(e & 0x1)
                ret.num = b;
            e >>>= 1;

            bool over = false;
            while(e != 0) {
                b = cmul(b, b, over);
                if(e & 0x1)
                    ret.num = cmul(ret.num, b, over);

                e >>>= 1;
            }

            if(!over)
                return ret;
        }

        ret.flag = (base < 0 && (exp & 0x1))?
            IntFlag.negOver :
            IntFlag.posOver;
        return ret;
    }
}
