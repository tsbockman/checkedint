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

// traits /////////////////////////////////////////////////

/// Evaluates to `true` if `T` is an instance of `SafeInt`.
enum isSafeInt(T) = isInstanceOf!(SafeInt, T);
///
unittest {
    assert( isSafeInt!(SafeInt!(int, Yes.throws)));

    assert(!isSafeInt!int);
    assert(!isSafeInt!(SmartInt!(int, Yes.throws)));
}

/// Evaluates to `true` if `T` is an instance of `SmartInt`.
enum isSmartInt(T) = isInstanceOf!(SmartInt, T);
///
unittest {
    assert( isSmartInt!(SmartInt!(int, Yes.throws)));

    assert(!isSmartInt!int);
    assert(!isSmartInt!(SafeInt!(int, Yes.throws)));
}

/// Evaluates to `true` if `T` is an instance of `SafeInt` or `SmartInt`.
enum isCheckedInt(T) = isSafeInt!T || isSmartInt!T;
///
unittest {
    assert( isCheckedInt!(SafeInt!(int, Yes.throws)));
    assert( isCheckedInt!(SmartInt!(int, Yes.throws)));

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
    assert( hasBitOps!(SafeInt!(int, Yes.throws, Yes.bitOps)));
    assert( hasBitOps!(SmartInt!(int, Yes.throws, Yes.bitOps)));
    assert( hasBitOps!int);
    assert( hasBitOps!bool);
    assert( hasBitOps!dchar);

    assert(!hasBitOps!(SafeInt!(int, Yes.throws, No.bitOps)));
    assert(!hasBitOps!(SmartInt!(int, Yes.throws, No.bitOps)));
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
    assert(is(BasicScalar!(SafeInt!(int, Yes.throws)) == int));
    assert(is(BasicScalar!(SmartInt!(int, Yes.throws)) == int));

    assert(is(BasicScalar!int == int));
    assert(is(BasicScalar!(const shared real) == real));
}

// internal /////////////////////////////////////////////////
private {
    enum trueMin(N) = mostNegative!N;
    template trueMax(N)
        if(isScalarType!N)
    {
        static if(is(Unqual!N == dchar))
            enum trueMax = ~cast(N)0;
        else
            enum trueMax = N.max;
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
        int bsrImpl(Flag!"throws" throws, N)(const N num)
            if(isFixedPoint!N)
        {
            if(num == 0)
                IntFlag.undef.raise!throws();
    
            static assert(N.sizeof <= ulong.sizeof);
            alias WN = Select!(N.sizeof > size_t.sizeof, ulong, size_t);
    
            return bsr(cast(WN)num);
        }
        int bsfImpl(Flag!"throws" throws, N)(const N num)
            if(isFixedPoint!N)
        {
            if(num == 0)
                IntFlag.undef.raise!throws();
    
            static assert(N.sizeof <= ulong.sizeof);
            alias WN = Select!(N.sizeof > size_t.sizeof, ulong, size_t);
    
            return bsf(cast(WN)num);
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

/+pragma(inline, true) {+/
// conv /////////////////////////////////////////////////

    // alternative to std.conv.to() using IntFlag
    T to(T, Flag!"throws" throws, S)(const S value)
        if((isCheckedInt!T || isScalarType!T) && (isCheckedInt!S || isScalarType!S))
    {
        static if(isCheckedInt!T || isCheckedInt!S)
            return T(to!(BasicScalar!T, throws)(value.bscal));
        else {
            static if(! isFloatingPoint!T) {
                static if(isFloatingPoint!S) {
                    if(value >= trueMin!T) {
                        if(value > trueMax!T)
                            IntFlag.posOver.raise!throws();
                    } else
                        (value.isNaN? IntFlag.undef : IntFlag.negOver).raise!throws();
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

// smart /////////////////////////////////////////////////
    template smartOp(Flag!"throws" throws) {
        static if(throws) {
            alias cmp = smartOp!(No.throws).cmp;
            alias abs = smartOp!(No.throws).abs;
            private alias Result = smartOp!(No.throws).Result;
        } else {
        // No need to redundantly instantiate members which don't depend on `throws`.
        pure: nothrow: @nogc:

            private void cmpTypeCheck(N, M)() {
                static assert(isBoolean!N == isBoolean!M,
                    "The intent of a direct comparison of " ~
                    N.stringof ~ " with " ~ M.stringof ~
                    " is unclear. Add an explicit cast."
                );
            }

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
            int cmp(N, M)(const N left, const M right) pure nothrow @nogc
                if(isScalarType!N && isScalarType!M)
            {
                cmpTypeCheck!(N, M)();

                static if(isFloatingPoint!N || isFloatingPoint!M)
                    return std.math.cmp(left, right);
                else {
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
            IntFromChar!N abs(N)(const N num) pure nothrow @nogc
                if(isSomeChar!N)
            {
                return num;
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
        }

        N unary(string op, N)(const N num)
            if(isIntegral!N && op == "~")
        {
            return ~num;
        }
        IntFromChar!N unary(string op, N)(const N num)
            if(isSomeChar!N && op == "~")
        {
            return ~num;
        }
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

        ubyte bsf(N)(const N num)
            if(isFixedPoint!N)
        {
            return cast(ubyte) bsfImpl!throws(num);
        }
        ubyte bsr(N)(const N num)
            if(isFixedPoint!N)
        {
            return cast(ubyte) bsrImpl!throws(num);
        }

        ubyte ilogb(N)(const N num)
            if(isFixedPoint!N)
        {
            return cast(ubyte) bsrImpl!throws(abs(num));
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
        auto binary(string op, N, M)(const N left, const M right)
            if(isFixedPoint!N && isFixedPoint!M && op.among!("+", "-", "*", "/", "%", "^^", "<<", ">>", ">>>", "&", "|", "^"))
        {
            static assert(op != "^^",
                "pow() should be used instead of operator ^^ because of issue 15288.");

            return binaryImpl!(op, NumFromScal!N, NumFromScal!M)(left, right);
        }
        /+ref+/ N binary(string op, N, M)(/+return+/ ref N left, const M right)
            if(isIntegral!N && isFixedPoint!M && (op[$ - 1] == '='))
        {
            static assert(op != "^^=",
                "pow() should be used instead of operator ^^= because of issue 15412.");

            left = binaryImpl!(op, NumFromScal!N, NumFromScal!M)(left, right);
            return left;
        }


        auto mulPow2(N, M)(const N left, const M exp) pure nothrow @nogc
            if((isFloatingPoint!N && isScalarType!M) || (isScalarType!N && isFloatingPoint!M))
        {
            return byPow2Impl!("*", NumFromScal!N, NumFromScal!M)(left, exp);
        }
        auto mulPow2(N, M)(const N left, const M exp)
            if(isFixedPoint!N && isFixedPoint!M)
        {
            return byPow2Impl!("*", throws, NumFromScal!N, NumFromScal!M)(left, exp);
        }
        auto divPow2(N, M)(const N left, const M exp) pure nothrow @nogc
            if((isFloatingPoint!N && isScalarType!M) || (isScalarType!N && isFloatingPoint!M))
        {
            return byPow2Impl!("/", NumFromScal!N, NumFromScal!M)(left, exp);
        }
        auto divPow2(N, M)(const N left, const M exp)
            if(isFixedPoint!N && isFixedPoint!M)
        {
            return byPow2Impl!("/", throws, NumFromScal!N, NumFromScal!M)(left, exp);
        }
        auto modPow2(N, M)(const N left, const M exp) pure nothrow @nogc
            if((isFloatingPoint!N && isScalarType!M) || (isScalarType!N && isFloatingPoint!M))
        {
            return byPow2Impl!("%", NumFromScal!N, NumFromScal!M)(left, exp);
        }
        auto modPow2(N, M)(const N left, const M exp) pure nothrow @nogc
            if(isFixedPoint!N && isFixedPoint!M)
        {
            return byPow2Impl!("%", No.throws, NumFromScal!N, NumFromScal!M)(left, exp);
        }

        auto pow(N, M)(const N base, const M exp) pure nothrow @nogc
            if((isFloatingPoint!N && isScalarType!M) || (isScalarType!N && isFloatingPoint!M))
        {
            alias R = Result!(N, "^^", M);
            static assert(is(typeof(return) == R));
            return std.math.pow(cast(R)base, exp);
        }
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
    }
    private alias smartOp(bool throws) = smartOp!(cast(Flag!"throws")throws);

    struct SmartInt(N, Flag!"throws" throws, Flag!"bitOps" bitOps = Yes.bitOps)
        if(isIntegral!N && isUnqual!N)
    {
        pure nothrow @nogc {
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
                SmartInt!(N, throws, Yes.bitOps) bits;
            }

            static if(__VERSION__ >= 2067) {
                version(GNU) { static assert(false); }
                enum min = typeof(this)(trueMin!N);
                enum max = typeof(this)(trueMax!N);
            } else {
                static @property pure nothrow @nogc {
                    auto min() {
                        return typeof(this)(trueMin!N); }
                    auto max() {
                        return typeof(this)(trueMax!N); }
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
                if(isCheckedInt!M || isScalarType!M)
            {
                this.bscal = to!(N, throws)(that);
            }
            ref typeof(this) opAssign(M)(const M that)
                if(isCheckedInt!M || isScalarType!M)
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
                if(isCheckedInt!M || isScalarType!M)
            {
                return smartOp!(throws).cmp!"=="(this.bscal, right.bscal);
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
                if(isCheckedInt!M || isScalarType!M)
            {
                return smartOp!(throws).cmp(this.bscal, right.bscal);
            }

            // Unary
            typeof(this) opUnary(string op)() const
                if(op == "~")
            {
                static assert(bitOps,
                    "Bitwise operations are disabled.");

                return typeof(return)(smartOp!(throws).unary!op(bscal));
            }

            SmartInt!(Unsigned!N, throws, bitOps) abs() const {
                return typeof(return)(smartOp!(throws).abs(bscal));
            }

            SmartInt!(int, throws, bitOps) popcnt()() const {
                static assert(bitOps, "Bitwise operations are disabled.");

                import future.bitop : stdPC = popcnt;
                return typeof(return)(stdPC(bscal));
            }

            // Binary
            auto opBinaryRight(string op, M)(const M left) const
                if(isFloatingPoint!M)
            {
                return smartOp!(throws).binary!op(left, bscal);
            }
            auto opBinary(string op, M)(const M right) const
                if(isFloatingPoint!M)
            {
                return smartOp!(throws).binary!op(bscal, right);
            }

            auto mulPow2(M)(const M exp) const
                if(isFloatingPoint!M)
            {
                return smartOp!(throws).mulPow2(bscal, exp);
            }
            auto divPow2(M)(const M exp) const
                if(isFloatingPoint!M)
            {
                return smartOp!(throws).divPow2(bscal, exp);
            }
            auto modPow2(M)(const M exp) const
                if(isFloatingPoint!M)
            {
                return smartOp!(throws).modPow2(bscal, exp);
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
                import std.conv : impl = to;
                return impl!string(bscal);
            }

            // Unary
            SmartInt!(Signed!N, throws, bitOps) opUnary(string op)() const
                if(op == "+" || op == "-")
            {
                return typeof(return)(smartOp!(throws).unary!op(bscal));
            }
            ref typeof(this) opUnary(string op)()
                if(op.among!("++", "--"))
            {
                smartOp!(throws).unary!op(bscal);
                return this;
            }

            SmartInt!(ubyte, throws, bitOps) bsf()() const {
                static assert(bitOps, "Bitwise operations are disabled.");

                return typeof(return)(smartOp!(throws).bsf(bscal));
            }
            SmartInt!(ubyte, throws, bitOps) bsr()() const {
                static assert(bitOps, "Bitwise operations are disabled.");

                return typeof(return)(smartOp!(throws).bsr(bscal));
            }

            SmartInt!(ubyte, throws, bitOps) ilogb() const {
                return typeof(return)(smartOp!(throws).ilogb(bscal)); }

            // Binary
            auto opBinaryRight(string op, M)(const M left) const
                if(isSafeInt!M || isFixedPoint!M)
            {
                enum mixThrows = throws || isThrowingCInt!M;
                enum mixBitOps = bitOps && hasBitOps!M;
                static assert(mixBitOps || !op.among!("<<", ">>", ">>>", "&", "|", "^"),
                    "Bitwise operations are disabled.");

                const wret = smartOp!(mixThrows).binary!op(left.bscal, this.bscal);
                return SmartInt!(typeof(wret), mixThrows, mixBitOps)(wret);
            }
            auto opBinary(string op, M)(const M right) const
                if(isCheckedInt!M || isFixedPoint!M)
            {
                enum mixThrows = throws || isThrowingCInt!M;
                enum mixBitOps = bitOps && hasBitOps!M;
                static assert(mixBitOps || !op.among!("<<", ">>", ">>>", "&", "|", "^"),
                    "Bitwise operations are disabled.");

                const wret = smartOp!(mixThrows).binary!op(this.bscal, right.bscal);
                return SmartInt!(typeof(wret), mixThrows, mixBitOps)(wret);
            }
            ref typeof(this) opOpAssign(string op, M)(const M right)
                if(isCheckedInt!M || isFixedPoint!M)
            {
                static assert((bitOps && hasBitOps!M) || !op.among!("<<", ">>", ">>>", "&", "|", "^"),
                    "Bitwise operations are disabled.");

                smartOp!(throws || isThrowingCInt!M).binary!(op ~ "=")(this.bscal, right.bscal);
                return this;
            }

            auto mulPow2(M)(const M exp) const
                if(isCheckedInt!M || isFixedPoint!M)
            {
                enum mixThrows = throws || isThrowingCInt!M;
                const wret = smartOp!(mixThrows).mulPow2(this.bscal, exp.bscal);
                return SmartInt!(typeof(wret), mixThrows, bitOps && hasBitOps!M)(wret);
            }
            auto divPow2(M)(const M exp) const
                if(isCheckedInt!M || isFixedPoint!M)
            {
                enum mixThrows = throws || isThrowingCInt!M;
                const wret = smartOp!(mixThrows).divPow2(this.bscal, exp.bscal);
                return SmartInt!(typeof(wret), mixThrows, bitOps && hasBitOps!M)(wret);
            }
            auto modPow2(M)(const M exp) const
                if(isCheckedInt!M || isFixedPoint!M)
            {
                enum mixThrows = throws || isThrowingCInt!M;
                const wret = smartOp!(mixThrows).modPow2(this.bscal, exp.bscal);
                return SmartInt!(typeof(wret), mixThrows, bitOps && hasBitOps!M)(wret);
            }

            auto pow(M)(const M exp) const
                if(isCheckedInt!M || isFixedPoint!M)
            {
                enum mixThrows = throws || isThrowingCInt!M;
                const wret = smartOp!(mixThrows).pow(this.bscal, exp.bscal);
                return SmartInt!(typeof(wret), mixThrows, bitOps && hasBitOps!M)(wret);
            }
        }
    }
    template SmartInt(N, Flag!"throws" throws, Flag!"bitOps" bitOps = Yes.bitOps)
        if((isIntegral!N && !isUnqual!N) || isCheckedInt!N)
    {
        alias SmartInt = SmartInt!(BasicScalar!N, throws, bitOps);
    }
    private template SmartInt(N, bool throws, bool bitOps)
        if(isIntegral!N)
    {
        alias SmartInt = SmartInt!(
            Unqual!N,
            cast(Flag!"throws")throws,
            cast(Flag!"bitOps")bitOps);
    }

// safe /////////////////////////////////////////////////
    template safeOp(Flag!"throws" throws) {
        static if(throws)
            alias cmp = safeOp!(No.throws).cmp;
        else {
        // No need to redundantly instantiate members which don't depend on `throws`.
        pure: nothrow: @nogc:

            private void cmpTypeCheck(N, M)() {
                static assert(isBoolean!N == isBoolean!M,
                    "The intent of a direct comparison of " ~
                    N.stringof ~ " with " ~ M.stringof ~
                    " is unclear. Add an explicit cast."
                );

                alias OT = OpType!(N, "+", M);
                static assert(isFloatingPoint!OT || isSigned!OT || !(isSigned!N || isSigned!M),
                    "The built-in signed:unsigned comparisons of " ~ N.stringof ~ " to " ~ M.stringof ~
                    " are unsafe. Use an explicit cast, or switch to smartOp/SmartInt."
                );
            }

            bool cmp(string op, N, M)(const N left, const M right)
                if(isScalarType!N && isScalarType!M)
            {
                cmpTypeCheck!(N, M)();
                return mixin("left " ~ op ~ " right");
            }
            int cmp(N, M)(const N left, const M right)
                if(isScalarType!N && isScalarType!M)
            {
                cmpTypeCheck!(N, M)();

                static if(isFloatingPoint!N || isFloatingPoint!M)
                    return std.math.cmp(left, right);
                else
                    return (left < right)? -1 : (right < left);
            }
        }

        N unary(string op, N)(const N num)
            if((isIntegral!N) && op.among!("-", "+", "~"))
        {
            static assert(isSigned!N || op != "-",
                "The built-in unary - operation for " ~ N.stringof ~
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

        N abs(N)(const N num)
            if(isIntegral!N || isBoolean!N)
        {
            static if(isSigned!N) {
                if(num < 0)
                    return unary!"-"(num);
            }
            return num;
        }

        int bsf(N)(const N num)
            if(isFixedPoint!N)
        {
            return bsfImpl!throws(num);
        }
        int bsr(N)(const N num)
            if(isFixedPoint!N)
        {
            return bsrImpl!throws(num);
        }

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
                "The built-in " ~ N.stringof ~ " " ~ op ~ " " ~ M.stringof ~
                " operation is unsafe, due to a signed:unsigned mismatch. " ~
                "Use an explicit cast, or switch to smartOp/SmartInt."
            );
        }
        OpType!(N, op, M) binary(string op, N, M)(const N left, const M right)
            if(isFixedPoint!N && isFixedPoint!M &&
                op.among!("+", "-", "*", "/", "%", "^^", "<<", ">>", ">>>", "&", "|", "^"))
        {
            static assert(op != "^^",
                "pow() should be used instead of operator ^^ because of issue 15288.");

            return binaryImpl!op(left, right);
        }
        /+ref+/ N binary(string op, N, M)(/+return+/ ref N left, const M right)
            if(isIntegral!N && isFixedPoint!M && (op[$ - 1] == '='))
        {
            static assert(op != "^^=",
                "pow() should be used instead of operator ^^= because of issue 15412.");

            left = binaryImpl!op(left, right);
            return left;
        }

        auto mulPow2(N, M)(const N left, const M exp) pure nothrow @nogc
            if((isFloatingPoint!N && isScalarType!M) || (isScalarType!N && isFloatingPoint!M))
        {
            return byPow2Impl!("*", NumFromScal!N, NumFromScal!M)(left, exp);
        }
        auto mulPow2(N, M)(const N left, const M exp)
            if(isFixedPoint!N && isFixedPoint!M)
        {
            return byPow2Impl!("*", throws, NumFromScal!N, NumFromScal!M)(left, exp);
        }
        auto divPow2(N, M)(const N left, const M exp) pure nothrow @nogc
            if((isFloatingPoint!N && isScalarType!M) || (isScalarType!N && isFloatingPoint!M))
        {
            return byPow2Impl!("/", NumFromScal!N, NumFromScal!M)(left, exp);
        }
        auto divPow2(N, M)(const N left, const M exp)
            if(isFixedPoint!N && isFixedPoint!M)
        {
            return byPow2Impl!("/", throws, NumFromScal!N, NumFromScal!M)(left, exp);
        }
        auto modPow2(N, M)(const N left, const M exp) pure nothrow @nogc
            if((isFloatingPoint!N && isScalarType!M) || (isScalarType!N && isFloatingPoint!M))
        {
            return byPow2Impl!("%", NumFromScal!N, NumFromScal!M)(left, exp);
        }
        auto modPow2(N, M)(const N left, const M exp) pure nothrow @nogc
            if(isFixedPoint!N && isFixedPoint!M)
        {
            return byPow2Impl!("%", No.throws, NumFromScal!N, NumFromScal!M)(left, exp);
        }

        CallType!(std.math.pow, N, M) pow(N, M)(const N base, const M exp)
            if(isFixedPoint!N && isFixedPoint!M)
        {
            alias R = typeof(return);
            static assert(!isSigned!N || isSigned!R,
                "std.math.pow(" ~ N.stringof ~ ", " ~ M.stringof ~
                ") is unsafe, due to a signed:unsigned mismatch. Use an explicit cast, or switch to smartOp/SmartInt."
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

    struct SafeInt(N, Flag!"throws" throws, Flag!"bitOps" bitOps = Yes.bitOps)
        if(isIntegral!N && isUnqual!N)
    {
        pure nothrow @nogc {
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
                SafeInt!(N, throws, Yes.bitOps) bits;
            }

            static if(__VERSION__ >= 2067) {
                version(GNU) { static assert(false); }
                enum min = typeof(this)(trueMin!N);
                enum max = typeof(this)(trueMax!N);
            } else {
                static @property pure nothrow @nogc {
                    auto min() {
                        return typeof(this)(trueMin!N); }
                    auto max() {
                        return typeof(this)(trueMax!N); }
                }
            }

            // Construction, assignment, and casting
            private void checkImplicit(M)()
                if(isCheckedInt!M || isScalarType!M)
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
                if(isCheckedInt!M || isScalarType!M)
            {
                checkImplicit!M();
                this.bscal = that.bscal;
            }
            ref typeof(this) opAssign(M)(const M that)
                if(isCheckedInt!M || isScalarType!M)
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
                return safeOp!(throws).cmp!"=="(this.bscal, right.bscal);
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
                return safeOp!(throws).cmp(this.bscal, right.bscal);
            }

            // Unary
            SafeInt!(int, throws, bitOps) popcnt()() const {
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
                return safeOp!(throws).mulPow2(bscal, exp);
            }
            auto divPow2(M)(const M exp) const
                if(isFloatingPoint!M)
            {
                return safeOp!(throws).divPow2(bscal, exp);
            }
            auto modPow2(M)(const M exp) const
                if(isFloatingPoint!M)
            {
                return safeOp!(throws).modPow2(bscal, exp);
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
                import std.conv : impl = to;
                return impl!string(bscal);
            }

            // Unary
            typeof(this) opUnary(string op)() const
                if(op.among!("-", "+", "~"))
            {
                static assert(bitOps || (op != "~"),
                    "Bitwise operations are disabled.");

                return typeof(return)(safeOp!(throws).unary!op(bscal));
            }
            ref typeof(this) opUnary(string op)()
                if(op.among!("++", "--"))
            {
                safeOp!(throws).unary!op(bscal);
                return this;
            }

            typeof(this) abs() const {
                return typeof(return)(safeOp!(throws).abs(bscal)); }

            SafeInt!(int, throws, bitOps) bsf()() const {
                static assert(bitOps, "Bitwise operations are disabled.");

                return typeof(return)(safeOp!(throws).bsf(bscal));
            }
            SafeInt!(int, throws, bitOps) bsr()() const {
                static assert(bitOps, "Bitwise operations are disabled.");

                return typeof(return)(safeOp!(throws).bsr(bscal));
            }

            SafeInt!(int, throws, bitOps) ilogb() const {
                return typeof(return)(safeOp!(throws).ilogb(bscal)); }

            // Binary
            SafeInt!(OpType!(M, op, N), throws, bitOps) opBinaryRight(string op, M)(const M left) const
                if(isFixedPoint!M)
            {
                static assert(bitOps || !op.among!("<<", ">>", ">>>", "&", "|", "^"),
                    "Bitwise operations are disabled.");

                return typeof(return)(safeOp!(throws).binary!op(left, bscal));
            }
            SafeInt!(OpType!(N, op, BasicScalar!M), throws || isThrowingCInt!M, bitOps && hasBitOps!M) opBinary(string op, M)(const M right) const
                if(isSafeInt!M || isFixedPoint!M)
            {
                static assert(bitOps && hasBitOps!M || !op.among!("<<", ">>", ">>>", "&", "|", "^"),
                    "Bitwise operations are disabled.");

                return typeof(return)(safeOp!(throws || isThrowingCInt!M).binary!op(this.bscal, right.bscal));
            }

            ref typeof(this) opOpAssign(string op, M)(const M right)
                if(isCheckedInt!M || isFixedPoint!M)
            {
                static assert((bitOps && hasBitOps!M) || !op.among!("<<", ">>", ">>>", "&", "|", "^"),
                    "Bitwise operations are disabled.");
                checkImplicit!(OpType!(N, op, M))();

                safeOp!(throws || isThrowingCInt!M).binary!(op ~ "=")(this.bscal, right.bscal);
                return this;
            }

            auto mulPow2(M)(const M exp) const
                if(isCheckedInt!M || isFixedPoint!M)
            {
                enum mixThrows = throws || isThrowingCInt!M;
                const wret = safeOp!(mixThrows).mulPow2(this.bscal, exp.bscal);
                return SafeInt!(typeof(wret), mixThrows, bitOps && hasBitOps!M)(wret);
            }
            auto divPow2(M)(const M exp) const
                if(isCheckedInt!M || isFixedPoint!M)
            {
                enum mixThrows = throws || isThrowingCInt!M;
                const wret = safeOp!(mixThrows).divPow2(this.bscal, exp.bscal);
                return SafeInt!(typeof(wret), mixThrows, bitOps && hasBitOps!M)(wret);
            }
            auto modPow2(M)(const M exp) const
                if(isCheckedInt!M || isFixedPoint!M)
            {
                enum mixThrows = throws || isThrowingCInt!M;
                const wret = safeOp!(mixThrows).modPow2(this.bscal, exp.bscal);
                return SafeInt!(typeof(wret), mixThrows, bitOps && hasBitOps!M)(wret);
            }

            SafeInt!(CallType!(std.math.pow, N, BasicScalar!M), throws || isThrowingCInt!M, bitOps && hasBitOps!M) pow(M)(const M exp) const
                if(isCheckedInt!M || isFixedPoint!M)
            {
                return typeof(return)(safeOp!(throws || isThrowingCInt!M).pow(this.bscal, exp.bscal));
            }
        }
    }
    template SafeInt(N, Flag!"throws" throws, Flag!"bitOps" bitOps = Yes.bitOps)
        if((isIntegral!N && !isUnqual!N) || isCheckedInt!N)
    {
        alias SafeInt = SafeInt!(BasicScalar!N, throws, bitOps);
    }
    private template SafeInt(N, bool throws, bool bitOps)
        if(isIntegral!N)
    {
        alias SafeInt = SafeInt!(
            Unqual!N,
            cast(Flag!"throws")throws,
            cast(Flag!"bitOps")bitOps);
    }

// debug /////////////////////////////////////////////////
    template DebugInt(N, Flag!"throws" throws, Flag!"bitOps" bitOps = Yes.bitOps)
        if(isIntegral!N || isCheckedInt!N)
    {
        version (Debug)
            alias DebugInt = SafeInt!(N, throws, bitOps);
        else
            alias DebugInt = Unqual!N;
    }
/+}+/
