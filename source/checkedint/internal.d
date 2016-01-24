/**
Copyright: Copyright Thomas Stuart Bockman 2015
License: <a href="http://www.boost.org/LICENSE_1_0.txt">Boost License 1.0</a>.
Authors: Thomas Stuart Bockman
*/

module checkedint.internal;
import checkedint.flags;

import core.bitop, core.checkedint, std.algorithm, std.conv, future.traits;
static import std.math;

@safe:

private template trueMax(N)
    if(isScalarType!N)
{
    static if(isSomeChar!N)
        enum trueMax = ~cast(N)0;
    else
        enum trueMax = N.max;
}

package:

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
    // nothrow alternative to std.conv.to() using IntFlag
    T toImpl(T, bool throws, S)(const S value)
        if(isScalarType!T && isScalarType!S)
    {
        static if(throws)
            return to!T(value);
        else {
            static if(! isFloatingPoint!T) {
                static if(isFloatingPoint!S) {
                    if(value >= T.min) {
                        if(value > trueMax!T)
                            IntFlag.posOver.raise!throws();
                    } else
                        (value.isNaN? IntFlag.undef : IntFlag.negOver).raise!throws();
                } else {
                    static if(cast(long)S.min < cast(long)T.min) {
                        if(value < cast(S)T.min)
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

    int bsrImpl(bool throws, N)(const N num)
        if(isFixedPoint!N)
    {
        if(num == 0)
            IntFlag.undef.raise!throws();

        static assert(N.sizeof <= ulong.sizeof);
        alias WN = Select!(N.sizeof > size_t.sizeof, ulong, size_t);

        return bsr(cast(WN)num);
    }
    int bsfImpl(bool throws, N)(const N num)
        if(isFixedPoint!N)
    {
        if(num == 0)
            IntFlag.undef.raise!throws();

        static assert(N.sizeof <= ulong.sizeof);
        alias WN = Select!(N.sizeof > size_t.sizeof, ulong, size_t);

        return bsf(cast(WN)num);
    }

    auto byPow2Impl(string op, N, M)(const N coef, const M exp) pure nothrow @nogc
        if(op.among!("*", "/") && ((isFloatingPoint!N && isNumeric!M) || (isNumeric!N && isFloatingPoint!M)))
    {
        enum wantPrec = max(precision!N, precision!M);
        alias R =
            Select!(wantPrec <= precision!float, float,
            Select!(wantPrec <= precision!double, double, real));

        static if(isFloatingPoint!M) {
            R ret = void;
            if(coef == 0 && std.math.isFinite(exp))
                ret = 0;
            else {
                R wexp = cast(R)exp;
                static if(op == "/")
                    wexp = -wexp;

                ret = cast(R)coef * std.math.exp2(wexp);
            }

            return ret;
        } else {
            int wexp =
                (exp > int.max)? int.max :
                (cast(long)exp < -int.max)? -int.max : cast(int)exp;
            static if(op == "/")
                wexp = -wexp;

            return std.math.ldexp(cast(R)coef, wexp);
        }
    }
    Promoted!N byPow2Impl(string op, bool throws, N, M)(const N coef, const M exp)
        if(op.among!("*", "/") && isIntegral!N && isIntegral!M)
    {
        alias R = typeof(return);

        const rc = cast(R)coef;
        const negE = exp < 0;
        const shR = (op == "*")? negE : !negE;
        const absE = cast(Unsigned!M)(negE?
            -exp :
             exp);

        R ret = void;
        R back = void;
        enum shLim = 8 * N.sizeof;
        if(absE >= shLim) {
            if(shR)
                return 0;
            else {
                ret = 0;
                back = 0;
                goto LcheckL;
            }
        }

        if(shR) {
            // ">>" rounds as floor(), but we want trunc() like "/"
            ret = (rc < 0)?
                -(-rc >>> absE) :
                rc >>> absE;
        } else {
            ret  = rc  << absE;
            back = ret >> absE;

        LcheckL:
            if(back != rc)
                IntFlag.over.raise!throws();
        }

        return ret;
    }
/+}+/

/+pragma(inline, false)+/ // reduce template bloat
W powImpl(W)(const W base, bool lezE, ulong exp, ref IntFlag flag) pure nothrow @nogc
    if(is(W == int) || is(W == uint) || is(W == long) || is(W == ulong))
{
    alias cmul = Select!(isSigned!W, muls, mulu);

    const absB = unsigned(std.math.abs(base));

    if(lezE) {
        if(exp == 0)
            return 1;

        if(absB <= 1) {
            if(absB == 0)
                flag = IntFlag.div0;
            else
                goto LAbsB1;
        }

        return 0;
    }
    if(absB <= 1) {
        if(absB == 0)
            return 0;

    LAbsB1:
        return (base < 0 && (exp & 0x1))?
            -1 :
             1;
    }

    /* TODO: Optimize to minimize use of 64-bit ops.
       TODO: Use a shift if the base is a power of two? */

    W ret = 1,
        b = base;
    ulong e = exp;
    if(e & 0x1)
        ret = b;
    e >>>= 1;

    bool over = false;
    while(e != 0) {
        b = cmul(b, b, over);
        if(e & 0x1)
            ret = cmul(ret, b, over);

        e >>>= 1;
    }

    if(over) {
        flag = (base < 0 && (exp & 0x1))?
            IntFlag.negOver :
            IntFlag.posOver;
    }
    return ret;
}
