/**
Copyright: Copyright Thomas Stuart Bockman 2015
License: <a href="http://www.boost.org/LICENSE_1_0.txt">Boost License 1.0</a>.
Authors: Thomas Stuart Bockman
*/

module checkedint.smartop;
import checkedint.flags, checkedint.internal;

import core.checkedint, std.algorithm, std.array, future.traits;
static import std.math;

// Watch out for DMD issue 15483 - Avoiding multiple return statements may help.
@safe: /+pragma(inline, true):+/

// TODO: Should this module accept SafeInt or SmartInt operands? It could theoretically do so without importing checkedint:
/+private @property pure nothrow @nogc {
    ref N bscal(N)(return ref N num)
        if(isScalarType!N)
    {
        return num;
    }
    N bscal(N)(const N num)
        if(isScalarType!N)
    {
        return num;
    }
}
private alias BasicScalar(T) = typeof(function() {
    static if(__traits(compiles, T.init.bscal))
        return T.init.bscal;
    else
        return;
}());
+/

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

N unary(string op, bool throws, N)(const N num)
    if(isIntegral!N && op == "~")
{
    return ~num;
}
N unary(string op, N)(const N num) pure
    if(isIntegral!N && op == "~")
{
    return unary!(op, true)(num);
}
IntFromChar!N unary(string op, bool throws, N)(const N num)
    if(isSomeChar!N && op == "~")
{
    return ~num;
}
IntFromChar!N unary(string op, N)(const N num) pure
    if(isSomeChar!N && op == "~")
{
    return unary!(op, true)(num);
}
Signed!(Promoted!N) unary(string op, bool throws, N)(const N num)
    if(isFixedPoint!N && op.among!("-", "+"))
{
    alias R = typeof(return);
    alias UR = Unsigned!R;

    static if(op == "-") {
        static if(isSigned!N) {
            if(num < -R.max)
                IntFlag.posOver.raise!throws();
        } else {
            if(num > cast(UR)R.min)
                IntFlag.negOver.raise!throws();
        }

        return -cast(R)num;
    } else {
        static if(!isSigned!N) {
            if(num > R.max)
                IntFlag.posOver.raise!throws();
        }

        return num;
    }
}
Signed!(Promoted!N) unary(string op, N)(const N num) pure
    if(isIntegral!N && op.among!("-", "+"))
{
    return unary!(op, true)(num);
}
/+ref+/ N unary(string op, bool throws, N)(/+return+/ ref N num)
    if(isIntegral!N && op.among!("++", "--"))
{
    static if(op == "++") {
        if(num >= N.max)
            IntFlag.posOver.raise!throws();

        return ++num;
    } else static if(op == "--") {
        if(num <= N.min)
            IntFlag.negOver.raise!throws();

        return --num;
    } else
        static assert(false);
}
/+ref+/ N unary(string op, N)(/+return+/ ref N num) pure
    if(isIntegral!N && op.among!("++", "--"))
{
    return unary!(op, true)(num);
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

ubyte bsf(bool throws, N)(const N num)
    if(isFixedPoint!N)
{
    return cast(ubyte) bsfImpl!throws(num);
}
ubyte bsf(N)(const N num) pure
    if(isFixedPoint!N)
{
    return bsf!true(num);
}
ubyte bsr(bool throws, N)(const N num)
    if(isFixedPoint!N)
{
    return cast(ubyte) bsrImpl!throws(num);
}
ubyte bsr(N)(const N num) pure
    if(isFixedPoint!N)
{
    return bsr!true(num);
}

ubyte ilogb(bool throws, N)(const N num)
    if(isFixedPoint!N)
{
    return cast(ubyte) bsrImpl!throws(abs(num));
}
ubyte ilogb(N)(const N num) pure
    if(isFixedPoint!N)
{
    return ilogb!true(num);
}

/* TODO: Optimize opOpAssign()
   TODO: Figure out how to get % and / to inline on DMD
   TODO: Audit binary() to ensure it properly accounts for the fact that (dchar.max < ~cast(dchar)0). */
private template Result(N, string op, M)
    if(isScalarType!N && isScalarType!M)
{
private:
    alias WN = NumFromScal!N;
    alias WM = NumFromScal!M;

    enum reqFloat = isFloatingPoint!WN || isFloatingPoint!WM;
    enum precN = precision!WN, precM = precision!WM;
    enum precStd = reqFloat? precision!float : precision!uint;
    enum smallSub = (op == "-") && precN < precision!int && precM < precision!int;

    enum reqSign = reqFloat ||
        (op.among!("+", "-", "*" , "/") && (isSigned!WN || isSigned!WM || smallSub)) ||
        (op.among!("%", "^^", "<<", ">>", ">>>") && isSigned!WN) ||
        (op.among!("&", "|", "^") && (isSigned!WN && isSigned!WM));

    enum reqPrec = reqFloat? max(precStd, precN, precM) :
        op.among!("+", "-", "*")? max(precStd, precN, precM) - 1 :
        op == "/"? (isSigned!WM? max(precStd, precN) - 1 : precN) :
        op == "%"? min(precision!WN, precision!WM) :
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
auto binary(string op, bool throws, N, M)(const N left, const M right)
    if(isIntegral!N && isIntegral!M)
{
    alias UN = Unsigned!N;
    alias UM = Unsigned!M;
    alias  R = Result!(N, op, M);
    alias UR = Unsigned!R;

    static if(op.among!("+", "-")) {
        alias UP = Select!(precision!N <= 32 && precision!M <= 32, uint, ulong);
        alias W = Select!(isSigned!N && isSigned!M, Signed!UP, UP);

        static if(!isSigned!W &&  isSigned!R) {
            alias cop = Select!(op == "+", addu, subu);

            bool hiBit = false;
            const wRet = cop(cast(W)left, cast(W)right, hiBit);
            const bool wSign = (Select!(isSigned!N, left, right) < 0) ^ hiBit;

            static assert(is(R == Signed!W));
            const ret = cast(R)wRet;
            const over = (ret < 0) != wSign;
        } else {
            static assert(is(R == W));

            static if(precision!W > max(precision!N, precision!M)) {
                enum over = false;
                const ret = mixin("cast(W)left " ~ op ~ " cast(W)right");
            } else {
                alias cop = Select!(isSigned!W,
                    Select!(op == "+", adds, subs),
                    Select!(op == "+", addu, subu));

                bool over = false;
                const ret = cop(cast(W)left, cast(W)right, over);
            }
        }

        if(over)
            IntFlag.over.raise!throws();
        return ret;
    } else
    static if(op == "*") {
        static if(!isSigned!N &&  isSigned!M)
            // Integer multiplication is commutative
            return binary!("*", throws)(right, left);
        else {
            alias cop = Select!(isSigned!R, muls, mulu);

            bool over = false;
            static if( isSigned!N && !isSigned!M) {
                if(right > cast(UR)R.max) {
                    if(left == 0)
                        return cast(R)0;
                    if(left == -1 && right == cast(UR)R.min)
                        return R.min;

                    over = true;
                }
            }
            const ret = cop(cast(R)left, cast(R)right, over);

            if(over)
                IntFlag.over.raise!throws();
            return ret;
        }
    } else
    static if(op == "/") {
        if(right == 0) {
            IntFlag.div0.raise!throws();
            return cast(R)0; // Prevent unrecoverable FPE
        }

        alias UP = Select!(precision!N <= 32 && precision!M <= 32, uint, ulong);
        alias  W = Select!(isSigned!N && isSigned!M, Signed!UP, UP);

        static if(!isSigned!W &&  isSigned!R) {
            W wL = void;
            W wG = void;
            static if(isSigned!N) {
                const negR = left < 0;
                alias side = left;
                alias wS = wL;
                wG = cast(W)right;
            } else {
                const negR = right < 0;
                wL = cast(W)left;
                alias side = right;
                alias wS = wG;
            }

            bool over = void;
            R ret = void;
            if(negR) {
                wS = -cast(W)side;
                const W wR = wL / wG;

                over = (wR > cast(UR)R.min);
                ret = -cast(R)wR;
            } else {
                wS =  cast(W)side;
                const W wR = wL / wG;

                over = (wR > cast(UR)R.max);
                ret =  cast(R)wR;
            }

            if(over)
                IntFlag.over.raise!throws();
            return ret;
        } else {
            static if(isSigned!N && isSigned!M) {
                if(left == R.min && right == -1) {
                    IntFlag.posOver.raise!throws();
                    return cast(R)0; // Prevent unrecoverable FPE
                }
            }

            return cast(R)(left / right);
        }
    } else
    static if(op == "%") {
        UM wG = void;
        if(right >= 0) {
            if(right == 0) {
                IntFlag.undef.raise!throws();
                return cast(R)0; // Prevent unrecoverable FPE
            }

            wG = cast(UM) right;
        } else
            wG = cast(UM)-right;

        if(wG > N.max) {
            return (wG == cast(UN)N.min && left == N.min)?
                cast(R)0 :
                cast(R)left;
        }

        return cast(R)(left % cast(N)wG);
    } else
    static if(op.among!("<<", ">>", ">>>")) {
        const negG = right < 0;
        const shR = (op == "<<")?
             negG :
            !negG;

        R ret = void;
        static if(op == ">>>")
            const wL = cast(UN)left;
        else
            alias wL = left;
        const absG = negG?
            -cast(UM)right :
             cast(UM)right;

        enum maxSh = (8 * N.sizeof) - 1;
        if(absG <= maxSh) {
            const wG = cast(int)absG;
            ret = cast(R)(shR?
                wL >> wG :
                wL << wG);
        } else {
            ret = cast(R)((isSigned!N && (op != ">>>") && shR)?
                (wL >> maxSh) :
                0);
        }

        return ret;
    } else
    static if(op.among!("&", "|", "^"))
        return cast(R)mixin("left " ~ op ~ " right");
    else {
        static assert(op != "^^",
            "pow() should be used instead of operator ^^ because of issue 15288.");

        static assert(false, op ~ " is not implemented for integers.");
    }
}
auto binary(string op, N, M)(const N left, const M right) pure
    if(isIntegral!N && isIntegral!M)
{
    return binary!(op, true)(left, right);
}

auto mulPow2(N, M)(const N coef, const M exp) pure nothrow @nogc
    if((isFloatingPoint!N && isScalarType!M) || (isScalarType!N && isFloatingPoint!M))
{
    return byPow2Impl!("*", NumFromScal!N, NumFromScal!M)(coef, exp);
}
auto mulPow2(bool throws, N, M)(const N coef, const M exp)
    if(isFixedPoint!N && isFixedPoint!M)
{
    return byPow2Impl!("*", throws, NumFromScal!N, NumFromScal!M)(coef, exp);
}
auto mulPow2(N, M)(const N coef, const M exp) pure
    if(isFixedPoint!N && isFixedPoint!M)
{
    return mulPow2!true(coef, exp);
}
auto divPow2(N, M)(const N coef, const M exp) pure nothrow @nogc
    if((isFloatingPoint!N && isScalarType!M) || (isScalarType!N && isFloatingPoint!M))
{
    return byPow2Impl!("/", NumFromScal!N, NumFromScal!M)(coef, exp);
}
auto divPow2(bool throws, N, M)(const N coef, const M exp)
    if(isFixedPoint!N && isFixedPoint!M)
{
    return byPow2Impl!("/", throws, NumFromScal!N, NumFromScal!M)(coef, exp);
}
auto divPow2(N, M)(const N coef, const M exp) pure
    if(isFixedPoint!N && isFixedPoint!M)
{
    return divPow2!true(coef, exp);
}

auto pow(N, M)(const N base, const M exp) pure nothrow @nogc
    if((isFloatingPoint!N && isScalarType!M) || (isScalarType!N && isFloatingPoint!M))
{
    alias R = Result!(N, "^^", M);
    static assert(is(typeof(return) == R));
    return std.math.pow(cast(R)base, exp);
}
auto pow(bool throws, N, M)(const N base, const M exp)
    if(isFixedPoint!N && isFixedPoint!M)
{
    alias R = Result!(N, "^^", M);

    IntFlag flag;
    const ret = powImpl!R(base, exp <= 0, cast(ulong)exp, flag);
    if(! flag.isNull)
        flag.raise!throws();

    return ret;
}
auto pow(N, M)(const N base, const M exp) pure
    if(isFixedPoint!N && isFixedPoint!M)
{
    return pow!true(base, exp);
}
