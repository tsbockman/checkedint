/**
Copyright: Copyright Thomas Stuart Bockman 2015
License: $(LINK2 http://www.boost.org/LICENSE_1_0.txt, Boost License 1.0).
Authors: Thomas Stuart Bockman
*/

module checkedint.tests.contract.safeop;
import checkedint.tests.contract.internal;

import checkedint.flags;

void all()() {
    writeln();
    write("Testing safeOp... ");
    stdout.flush();

    cmp();
    abs();
    ilogb();
    unary();
    binary();
    byPow2();
    pow();

    writeln("DONE");
}

/+@safe:+/

void cmp(string op = null, N = void, M = void)() {
    static if(op == null) {
        foreach(op1; AliasSeq!("==", "!=", "<", "<=", ">", ">="))
            cmp!(op1, N, M)();
    } else
    static if(is(N == void)) {
        foreach(N1; AliasSeq!(IntegralTypes, CharTypes))
            cmp!(op, N1, M)();
    } else
    static if(is(M == void)) {
        foreach(M1; AliasSeq!(IntegralTypes, CharTypes))
            cmp!(op, N, M1)();
    } else {
        static assert(isScalarType!N && isScalarType!M);

        enum sc = "safeOp.cmp!\"" ~ op ~ "\"(n, m)";

        static assert(real.mant_dig >= max(precision!N, precision!M));
        auto control(const real n, const real m) {
            auto wret = stdm.cmp(n, m);
            return mixin("wret " ~ op ~ " 0");
        }

        static if(mostNegative!N <= cast(M)0 && mostNegative!M <= cast(N)0)
            fuzz!(sc, Unqual, OutIs!bool, control, N, M)();
        else
            forbid!(sc, N, M)();
    }
}
alias cmp(N, M = void) = cmp!(null, N, M);

void abs(N = void)() {
    static if(is(N == void)) {
        foreach(N1; AliasSeq!(IntegralTypes, CharTypes))
            abs!N1();
    } else {
        static assert(isFixedPoint!N);

        enum sc = "safeOp.abs(n)";

        static assert(real.mant_dig >= (8 * N.sizeof));
        auto control(const real n, Unused m = null) {
            return stdm.abs(n); }
        alias R = CallType!(stdm.abs, N);

        static if(isIntegral!R)
            fuzz!(sc, Unqual, OutIs!R, control, N)();
        else
            forbid!(sc, N)();
    }
}

void ilogb(N = void)() {
    static if(is(N == void)) {
        foreach(N1; AliasSeq!(IntegralTypes, CharTypes))
            ilogb!N1();
    } else {
        static assert(isFixedPoint!N);

        enum sc = "safeOp.ilogb(n)";

        static assert(real.mant_dig >= (8 * N.sizeof));
        auto control(const real n, Unused m = null) {
            return n != 0? stdm.ilogb(n) : real.nan; }
        alias R = CallType!(stdm.ilogb, IntFromChar!N);

        fuzz!(sc, Unqual, OutIs!R, control, N)();
    }
}

void unary(string op = null, N = void)() {
    static if(op == null) {
        foreach(op1; AliasSeq!("+", "-", "~", "++", "--"))
            unary!(op1, N)();
    } else
    static if(is(N == void)) {
        foreach(N1; AliasSeq!(IntegralTypes, CharTypes))
            unary!(op, N1)();
    } else {
        static assert(isFixedPoint!N);

        enum sc = "safeOp.unary!\"" ~ op ~ "\"(n)";

        static assert(real.mant_dig >= precision!N);
        auto control(Select!(op == "~", N, real) n, Unused m = null) {
            return mixin(op ~ "n"); }
        alias R = OpType!(op, N);

        static if((op != "-" || isSigned!N) && isIntegral!R)
            fuzz!(sc, Unqual, OutIs!R, control, N)();
        else
            forbid!(sc, N)();
    }
}
alias unary(N) = unary!(null, N);

void binary(string op = null, N = void, M = void)() {
    static if(op == null) {
        foreach(op1; AliasSeq!("+", "-", "*", "/", "%", "<<", ">>", ">>>", "&", "|", "^"))
            binary!(op1, N, M)();
    } else
    static if(is(N == void)) {
        foreach(N1; AliasSeq!(IntegralTypes, CharTypes))
            binary!(op, N1, M)();
    } else
    static if(is(M == void)) {
        foreach(M1; AliasSeq!(IntegralTypes, CharTypes))
            binary!(op, N, M1)();
    } else {
        static assert(isFixedPoint!N && isFixedPoint!M);

        static void cover(bool assign)() {
            enum sc = "safeOp.binary!\"" ~ op ~ (assign? "=" : "") ~ "\"(n, m)";

            alias P = OpType!(N, op, M);
            alias R = Select!(assign, N, P);

            static assert(real.mant_dig >= max(precision!N, precision!M));
            enum bc = "n " ~ op ~ " m";
            static if(op.among!("<<", ">>", ">>>")) {
                real control(const N n, const M m) {
                    if(m < 0 || m >= (8 * cast(int)Promoted!(N).sizeof))
                        return real.nan;

                    const wret = mixin(bc);
                    return assign? cast(N)wret : wret;
                }
            } else
            static if(op.among!("&", "|", "^")) {
                auto control(const N n, const M m) {
                    const wret = mixin(bc);
                    static if(assign)
                        return cast(N)wret;
                    else
                        return wret;
                }
            } else {
                real control(const real n , const real m) {
                    const wret = mixin(bc);
                    static if(op == "/")
                        return stdm.trunc(wret);
                    else
                    static if(op == "%")
                        return ((R.min < 0) && (n == R.min) && (m == -1))? real.nan : wret;
                    else
                        return wret;
                }
            }

            enum matchedSigns = (!isSigned!N && !isSigned!M) ||
                (isSigned!P && (isSigned!R || (op == "%" && !isSigned!N)));
            static if((matchedSigns || op.among!("<<", ">>", ">>>", "&", "|", "^")) && isIntegral!R)
                fuzz!(sc, Unqual, OutIs!R, control, N, M)();
            else
                forbid!(sc, N, M)();
        }
        cover!false();
        cover!true();
    }
}
alias binary(N, M = void) = binary!(null, N, M);

void byPow2(string op = null, N = void, M = void)() {
    static if(op == null) {
        foreach(op1; AliasSeq!("*", "/", "%"))
            byPow2!(op1, N, M)();
    } else
    static if(is(N == void)) {
        foreach(N1; AliasSeq!(IntegralTypes, CharTypes))
            byPow2!(op, N1, M)();
    } else
    static if(is(M == void)) {
        foreach(M1; AliasSeq!(IntegralTypes, CharTypes))
            byPow2!(op, N, M1)();
    } else {
        static assert(isScalarType!N && isScalarType!M);

        enum sc = "safeOp." ~ (op == "*"? "mul" : (op == "/"? "div" : "mod")) ~ "Pow2(n, m)";

        static assert(real.mant_dig >= max(precision!N, precision!M));
        real control(const real n, const real m) {
            if(n == 0 && stdm.isFinite(m))
                return 0;
            else {
                const p2 = stdm.exp2(m);

                static if(op.among!("*", "/")) {
                    const wret = mixin("n " ~ op ~ " p2");
                    static if(isFloatingPoint!N || isFloatingPoint!M)
                        return wret;
                    else
                        return stdm.trunc(wret);
                } else {
                    if(!stdm.isFinite(p2))
                        return (p2 > 0)? n : (p2 < 0)? 0 : real.nan;
                    else
                        return n % (p2 == 0? real.min_normal : p2);
                }
            }
        }
        enum isVO(N, M, PR) = (PR.sizeof >= N.sizeof) &&
            ((isFloatingPoint!N || isFloatingPoint!M)?
                isFloatingPoint!PR :
                isIntegral!PR && (isSigned!PR || !isSigned!N));

        fuzz!(sc, Unqual, isVO, control, N, M)();
    }
}
alias byPow2(N, M = void) = byPow2!(null, N, M);

void pow(N = void, M = void)() {
    static if(is(N == void)) {
        foreach(N1; IntegralTypes)
            pow!(N1, M)();
    } else
    static if(is(M == void)) {
        foreach(M1; IntegralTypes)
            pow!(N, M1)();
    } else {
        static assert(isFixedPoint!N && isFixedPoint!M);
        forbid!("safeOp.binary!\"^^\"(n, m)", N, M)();
        forbid!("safeOp.binary!\"^^=\"(n, m)", N, M)();

        enum sc = "safeOp.pow(n, m)";

        static assert(real.mant_dig >= max(precision!N, precision!M));
        real control(const real n, const real m) {
            return (m < 0)?
                real.nan :
                stdm.pow(n, m);
        }
        alias R = CallType!(stdm.pow, N, M);

        static if((!isSigned!N || isSigned!R) && isIntegral!R)
            fuzz!(sc, Unqual, OutIs!R, control, N, M)();
        else
            forbid!(sc, N, M)();
    }
}
