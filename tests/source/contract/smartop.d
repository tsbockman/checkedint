/**
Copyright: Copyright Thomas Stuart Bockman 2015
License: <a href="http://www.boost.org/LICENSE_1_0.txt">Boost License 1.0</a>.
Authors: Thomas Stuart Bockman
*/

module checkedint.tests.contract.smartop;
import checkedint.tests.contract.internal;

import checkedint.flags;

void all() {
    writeln();
    write("Testing smartOp... ");
    stdout.flush();

    cmp();
    abs();
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

        static void cover(bool direct)() {
            static if(direct)
                enum sc = "smartOp.cmp!\"" ~ op ~ "\"(n, m)";
            else
                enum sc = "smartOp.cmp(n, m) " ~ op ~ " 0";

            static assert(real.mant_dig >= max(precision!N, precision!M));
            auto control(const real n, const real m) {
                auto wret = stdm.cmp(n, m);
                return mixin("wret " ~ op ~ " 0");
            }

            fuzz!(sc, Unqual, OutIs!bool, control, N, M)();
        }
        cover!true();
        cover!false();
    }
}
alias cmp(N, M = void) = cmp!(null, N, M);

void abs(N = void)() {
    static if(is(N == void)) {
        foreach(N1; AliasSeq!(IntegralTypes, CharTypes))
            abs!N1();
    } else {
        static assert(isFixedPoint!N);

        enum sc = "smartOp.abs(n)";

        static assert(real.mant_dig >= precision!N);
        auto control(const real n, Unused m = null) {
            return stdm.abs(n); }
        alias R = Unsigned!(IntFromChar!N);

        fuzz!(sc, Unqual, OutIs!R, control, N)();
    }
}

void unary(string op = null, N = void)() {
    static if(op == null) {
        foreach(op1; AliasSeq!("~", "+", "-", "++", "--"))
            unary!(op1, N)();
    } else
    static if(is(N == void)) {
        foreach(N1; AliasSeq!(IntegralTypes, CharTypes))
            unary!(op, N1)();
    } else {
        static assert(isFixedPoint!N);

        enum sc = "smartOp.unary!\"" ~ op ~ "\"(n)";

        static assert(real.mant_dig >= precision!N);
        auto control(Select!(op == "~", N, real) n, Unused m = null) {
            return mixin(op ~ "n"); }
        enum isVO(N, M, PR) = (PR.sizeof >= N.sizeof) && (isSigned!PR || !op.among!("-", "+"));

        static if(isIntegral!N || !op.among!("++", "--"))
            fuzz!(sc, Unqual, isVO, control, N)();
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
        foreach(N1; AliasSeq!(IntegralTypes/+TODO:, CharTypes+/))
            binary!(op, N1, M)();
    } else
    static if(is(M == void)) {
        foreach(M1; AliasSeq!(IntegralTypes/+TODO:, CharTypes+/))
            binary!(op, N, M1)();
    } else {
        static assert(isFixedPoint!N && isFixedPoint!M);

        enum sc = "smartOp.binary!\"" ~ op ~ "\"(n, m)";

        static assert(real.mant_dig >= max(precision!N, precision!M));
        static if(op.among!("<<", ">>", ">>>")) {
            static N control(const N n, const M m) {
                const shL = (op == "<<") ^ (m < 0);
                enum int maxSh = (8 * N.sizeof) - 1;
                const um = cast(Unsigned!M)std.math.abs(m);

                static if(op == ">>>")
                    auto wret = cast(Unsigned!N)n;
                else
                    N wret = n;
                bool again = um > maxSh;
                const im = again? maxSh : cast(int)um;
            Lagain:
                wret = cast(typeof(wret))(shL?
                    wret << im :
                    wret >> im);
                if(again) {
                    again = false;
                    goto Lagain;
                }

                return cast(N)wret;
            }
            enum isVO(N, M, PR) = is(PR == N);
        } else
        static if(op.among!("&", "|", "^")) {
            static auto control(const N n, const M m) {
                alias P = Select!(N.sizeof >= M.sizeof, N, M);
                alias R = Select!(isSigned!N && isSigned!M, P, Unsigned!P);

                return cast(R)mixin("n " ~ op ~ " m");
            }
            template isVO(N, M, PR) {
                private alias UR = Unsigned!PR;
                enum isVO = (isSigned!PR == (isSigned!N && isSigned!M)) &&
                    (is(UR == Unsigned!N) || is(UR == Unsigned!M));
            }
        } else {
            static auto control(const real n, const real m) {
                static if(op == "/")
                    return stdm.trunc(n / m);
                else
                    return mixin("n " ~ op ~ " m");
            }
            enum isVO(N, M, PR) = isIntegral!PR &&
                ((isSigned!PR == (isSigned!N || (isSigned!M && op != "%"))) || op == "-");
        }

        fuzz!(sc, Unqual, isVO, control, N, M)();
    }
}
alias binary(N, M = void) = binary!(null, N, M);

void byPow2(N = void, M = void)() {
    static if(is(N == void)) {
        foreach(N1; AliasSeq!(IntegralTypes, CharTypes))
            byPow2!(N1, M)();
    } else
    static if(is(M == void)) {
        foreach(M1; AliasSeq!(IntegralTypes, CharTypes))
            byPow2!(N, M1)();
    } else {
        static assert(isScalarType!N && isScalarType!M);

        static void cover(bool mul)() {
            enum sc = "smartOp." ~ (mul? "mul" : "div") ~ "Pow2(n, m)";

            static assert(real.mant_dig >= max(precision!N, precision!M));
            real control(const real n, const real m) {
                if(n == 0 && stdm.isFinite(m))
                    return 0;
                else {
                    const p2 = stdm.exp2(m);
                    const wret = mul? (n * p2) : (n / p2);
                    static if(isFloatingPoint!N || isFloatingPoint!M)
                        return wret;
                    else
                        return stdm.trunc(wret);
                }
            }
            enum isVO(N, M, PR) = (PR.sizeof >= N.sizeof) &&
                ((isFloatingPoint!N || isFloatingPoint!M)?
                    isFloatingPoint!PR :
                    isIntegral!PR && (isSigned!PR || !isSigned!N));

            fuzz!(sc, Unqual, isVO, control, N, M)();
        }
        cover!true();
        cover!false();
    }
}

void pow(N = void, M = void)() {
    static if(is(N == void)) {
        foreach(N1; AliasSeq!(IntegralTypes, CharTypes))
            pow!(N1, M)();
    } else
    static if(is(M == void)) {
        foreach(M1; AliasSeq!(IntegralTypes, CharTypes))
            pow!(N, M1)();
    } else {
        static assert(isFixedPoint!N && isFixedPoint!M);

        enum sc = "smartOp.pow(n, m)";

        static assert(real.mant_dig >= max(precision!N, precision!M));
        real control(const real n, const real m) {
            static if(__VERSION__ >= 2070) {
                version(GNU) { static assert(false); }
                return stdm.trunc(stdm.pow(n, m));
            } else {
                // DMD issue #14786
                if(n == -1 && stdm.fabs(m) <= ulong.max)
                    return (cast(ulong)m & 0x1)? -1 : 1;
                else
                    return stdm.trunc(stdm.pow(n, m));
            }
        }
        enum isVO(N, M, PR) = isIntegral!PR && (PR.sizeof >= N.sizeof) && (isSigned!PR == isSigned!N);

        fuzz!(sc, Unqual, isVO, control, N, M)();
    }
}
