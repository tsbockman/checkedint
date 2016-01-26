/**
Copyright: Copyright Thomas Stuart Bockman 2015
License: <a href="http://www.boost.org/LICENSE_1_0.txt">Boost License 1.0</a>.
Authors: Thomas Stuart Bockman
*/

module checkedint.smartop;
import checkedint.flags, checkedint.internal;

import core.checkedint, std.algorithm, std.array, future.traits;
static import std.math;
static if(__VERSION__ >= 2068) {
    version(GNU) { static assert(false); }
    import std.meta;
} else {
    import std.typetuple;
    private alias AliasSeq = TypeTuple;
}

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
private auto binaryImpl(string op, bool throws, N, M)(const N left, const M right)
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
                                over = (sa != 0) && (ub != W.min || sa != -1);
                        } else {
                            over = (sa < 0) && (ub != 0);
                            const wR = mulu(sa, ub, over);
                        }
                    }
                }

                alias WR = typeof(wR);
                static if(isSigned!WR && WR.min < R.min) {
                    if(wR < R.min)
                        over = true;
                }
                static if(WR.max > R.max) {
                    if(wR > R.max)
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
                    static if(WR.max > R.max) {
                        const over = (wR < 0)?
                            !wSign || (wR < R.min) :
                             wSign || (wR > R.max);
                    } else
                        const over = (wR < 0) != wSign;
                } else {
                    static if(WR.max > R.max)
                        const over = wSign || (wR > R.max);
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
                    if(left == R.min && right == -1) {
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

                        if(wR > cast(UR)R.min)
                            flag = IntFlag.negOver;
                        ret = -cast(R)wR;
                    } else {
                        wS =  cast(P)side;
                        const P wR = wL / wG;

                        if(wR > cast(UR)R.max)
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

        if(wG <= N.max) {
            if(wG)
                ret = cast(R)(left % cast(N)wG);
            else {
                IntFlag.div0.raise!throws();
                ret = 0;
            }
        } else {
            static if(isSigned!N)
                ret = (wG != cast(UN)N.min || left != N.min)?
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
auto binary(string op, bool throws, N, M)(const N left, const M right)
    if(isFixedPoint!N && isFixedPoint!M && op.among!("+", "-", "*", "/", "%", "^^", "<<", ">>", ">>>", "&", "|", "^"))
{
    static assert(op != "^^",
        "pow() should be used instead of operator ^^ because of issue 15288.");

    return binaryImpl!(op, throws, NumFromScal!N, NumFromScal!M)(left, right);
}
auto binary(string op, N, M)(const N left, const M right) pure
    if(isFixedPoint!N && isFixedPoint!M && op.among!("+", "-", "*", "/", "%", "^^", "<<", ">>", ">>>", "&", "|", "^"))
{
    return binary!(op, true)(left, right);
}
/+ref+/ N binary(string op, bool throws, N, M)(/+return+/ ref N left, const M right)
    if(isIntegral!N && isFixedPoint!M && (op[$ - 1] == '='))
{
    static assert(op != "^^=",
        "pow() should be used instead of operator ^^= because of issue 15412.");

    left = binaryImpl!(op, throws, NumFromScal!N, NumFromScal!M)(left, right);
    return left;
}
/+ref+/ N binary(string op, N, M)(/+return+/ ref N left, const M right) pure
    if(isIntegral!N && isFixedPoint!M && (op[$ - 1] == '='))
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
    const ret = powImpl!(R, Select!(isSigned!M, long, ulong))(base, exp, flag);
    static assert(is(typeof(ret) == const(R)));

    if(!flag.isNull)
        flag.raise!throws();
    return ret;
}
auto pow(N, M)(const N base, const M exp) pure
    if(isFixedPoint!N && isFixedPoint!M)
{
    return pow!true(base, exp);
}
