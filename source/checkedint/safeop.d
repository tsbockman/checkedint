/**
Copyright: Copyright Thomas Stuart Bockman 2015
License: <a href="http://www.boost.org/LICENSE_1_0.txt">Boost License 1.0</a>.
Authors: Thomas Stuart Bockman
*/

module checkedint.safeop;
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

private {
    /+pragma(inline, true)+/
    void cmpTypeCheck(N, M)() {
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

N unary(string op, bool throws, N)(const N num)
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
            const over = (num <= N.min);
            const N ret = -num;
        }

        if(over)
            IntFlag.posOver.raise!throws();

        return ret;
    } else
        return mixin(op ~ "num");
}
N unary(string op, N)(const N num) pure
    if((isIntegral!N) && op.among!("-", "+", "~"))
{
    return unary!(op, true)(num);
}
/+ref+/ N unary(string op, bool throws, N)(/+return+/ ref N num)
    if((isIntegral!N) && op.among!("++", "--"))
{
    static if(op == "++") {
        if(num >= N.max)
            IntFlag.posOver.raise!throws();
    } else
    static if(op == "--") {
        if(num <= N.min)
            IntFlag.negOver.raise!throws();
    }

    return mixin(op ~ "num");
}
/+ref+/ N unary(string op, N)(/+return+/ ref N num) pure
    if((isIntegral!N) && op.among("++", "--"))
{
    return unary!(op, true)(num);
}

N abs(bool throws, N)(const N num)
    if(isIntegral!N || isBoolean!N)
{
    static if(isSigned!N) {
        if(num < 0)
            return unary!("-", throws)(num);
    }
    return num;
}
N abs(N)(const N num) pure
    if(isIntegral!N || isBoolean!N)
{
    return abs!true(num);
}

int bsf(bool throws, N)(const N num)
    if(isFixedPoint!N)
{
    return bsfImpl!throws(num);
}
int bsf(N)(const N num)
    if(isFixedPoint!N)
{
    return bsfImpl!true(num);
}
int bsr(bool throws, N)(const N num)
    if(isFixedPoint!N)
{
    return bsrImpl!throws(num);
}
int bsr(N)(const N num)
    if(isFixedPoint!N)
{
    return bsrImpl!true(num);
}

int ilogb(bool throws, N)(const N num)
    if(isFixedPoint!N)
{
    static if(isSigned!N)
        const absN = cast(Unsigned!N) (num < 0? -num : num);
    else
        alias absN = num;

    return bsrImpl!throws(absN);
}
int ilogb(N)(const N num)
    if(isFixedPoint!N)
{
    return ilogb!true(num);
}

private auto binaryImpl(string op, bool throws, N, M)(const N left, const M right)
    if(isFixedPoint!N && isFixedPoint!M)
{
    enum wop = (op[$-1] == '=')? op[0 .. $-1] : op;
    alias P = OpType!(N, wop, M);
    alias R = Select!(wop == op, P, N);

    static if(wop.among!("+", "-", "*")) {
        enum isPromSafe = !(isSigned!N || isSigned!M) || (isSigned!P && isSigned!R);
        enum needCheck = (wop == "*")?
            (precision!N + precision!M) > precision!P :
            (max(precision!N, precision!M) + 1) > precision!P;

        static if(needCheck) {
            enum cx = (staticIndexOf!(wop, "+", "-", "*") << 1) + isSigned!P;
            alias cop = AliasSeq!(addu, adds, subu, subs, mulu, muls)[cx];

            bool invalid = false;
            const pret = cop(cast(P)left, cast(P)right, invalid);

            if(invalid)
                IntFlag.over.raise!throws();
        } else
            const pret = mixin("left " ~ wop ~ " right");

        return pret.toImpl!(R, throws);
    } else
    static if(wop.among!("/", "%")) {
        enum isPromSafe = !(isSigned!N || isSigned!M) || (isSigned!P && (wop == "%"? (isSigned!R || !isSigned!N) : isSigned!R));

        const div0 = (right == 0);
        static if(isSigned!N && isSigned!M)
            const posOver = (left == R.min) && (right == -1);
        else
            enum posOver = false;

        if(div0 || posOver) {
            (posOver? IntFlag.posOver : IntFlag.div0).raise!throws();
            return cast(R)0; // Prevent unrecoverable FPE
        } else
            return cast(R)mixin("left " ~ wop ~ " right");
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
        " operation is unsafe, due to a signed:unsigned mismatch. Use an explicit cast, or switch to smartOp/SmartInt."
    );
}
OpType!(N, op, M) binary(string op, bool throws, N, M)(const N left, const M right)
    if(isFixedPoint!N && isFixedPoint!M && op.among!("+", "-", "*", "/", "%", "^^", "<<", ">>", ">>>", "&", "|", "^"))
{
    static assert(op != "^^",
        "pow() should be used instead of operator ^^ because of issue 15288.");

    return binaryImpl!(op, throws)(left, right);
}
OpType!(N, op, M) binary(string op, N, M)(const N left, const M right) pure
    if(isFixedPoint!N && isFixedPoint!M && op.among!("+", "-", "*", "/", "%", "^^", "<<", ">>", ">>>", "&", "|", "^"))
{
    return binary!(op, true)(left, right);
}
/+ref+/ N binary(string op, bool throws, N, M)(/+return+/ ref N left, const M right)
    if(isIntegral!N && isFixedPoint!M && (op[$ - 1] == '='))
{
    static assert(op != "^^=",
        "pow() should be used instead of operator ^^= because of issue 15412.");

    left = binaryImpl!(op, throws)(left, right);
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

CallType!(std.math.pow, N, M) pow(bool throws, N, M)(const N base, const M exp)
    if(isFixedPoint!N && isFixedPoint!M)
{
    alias R = typeof(return);
    static assert(!isSigned!N || isSigned!R,
        "std.math.pow(" ~ N.stringof ~ ", " ~ M.stringof ~
        ") is unsafe, due to a signed:unsigned mismatch. Use an explicit cast, or switch to smartOp/SmartInt."
    );

    IntFlag flag;
    const ret = powImpl!R(base, exp <= 0, exp, flag);
    if(exp < 0) {
        /* std.math.pow fails catastrophically for negative exponents, even when the (rounded) result
           is mathematically expressible as an integer. */
        flag = IntFlag.undef;
    }
    if(! flag.isNull)
        flag.raise!throws();

    return ret;
}
CallType!(std.math.pow, N, M) pow(N, M)(const N base, const M exp) pure
    if(isFixedPoint!N && isFixedPoint!M)
{
    return pow!true(left, right);
}
