/**
Precise and detailed description of the expected behaviour of
`checkedint.smartOp` against which it can be automatically tested.
80+ bit floating-point is used to compute the expected value for each
operation with many different combinations of inputs.

$(RED Note:) These tests currently will not work on systems where
`is(real == double)`, because `Precision!double < Precision!ulong`.

Copyright: Copyright Thomas Stuart Bockman 2015
License: $(LINK2 http://www.boost.org/LICENSE_1_0.txt, Boost License 1.0).
Authors: Thomas Stuart Bockman
**/
module checkedint.tests.contract.smartop;
import checkedint.tests.contract.internal;

import checkedint.flags;

void all()()
{
    writeln();
    write("Testing smartOp... ");
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

@safe:

void cmp(string op = null, N = void, M = void)()
{
    static if (op == null)
    {
        foreach (op1; AliasSeq!("==", "!=", "<", "<=", ">", ">="))
            cmp!(op1, N, M)();
    }
    else static if (is(N == void))
    {
        foreach (N1; AliasSeq!(IntegralTypes, CharTypes))
            cmp!(op, N1, M)();
    }
    else static if (is(M == void))
    {
        foreach (M1; AliasSeq!(IntegralTypes, CharTypes))
            cmp!(op, N, M1)();
    }
    else
    {
        static assert(isScalarType!N && isScalarType!M);

        static void cover(bool direct)()
        {
            static if (direct)
                enum sc = "smartOp.cmp!\"" ~ op ~ "\"(n, m)";
            else
                enum sc = "smartOp.cmp(n, m) " ~ op ~ " 0";

            static assert(real.mant_dig >= max(precision!N, precision!M));
            auto control(const real n, const real m)
            {
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

void abs(N = void)()
{
    static if (is(N == void))
    {
        foreach (N1; AliasSeq!(IntegralTypes, CharTypes))
            abs!N1();
    }
    else
    {
        static assert(isFixedPoint!N);

        enum sc = "smartOp.abs(n)";

        static assert(real.mant_dig >= precision!N);
        auto control(const real n, Unused m = null)
        {
            return stdm.abs(n);
        }
        alias R = Unsigned!(IntFromChar!N);

        fuzz!(sc, Unqual, OutIs!R, control, N)();
    }
}

void ilogb(N = void)()
{
    static if (is(N == void))
    {
        foreach (N1; AliasSeq!(IntegralTypes, CharTypes))
            ilogb!N1();
    }
    else
    {
        static assert(isFixedPoint!N);

        enum sc = "smartOp.ilogb(n)";

        static assert(real.mant_dig >= (8 * N.sizeof));
        auto control(const real n, Unused m = null)
        {
            return n != 0? stdm.ilogb(n) : real.nan;
        }

        fuzz!(sc, Unqual, OutIs!ubyte, control, N)();
    }
}

void unary(string op = null, N = void)()
{
    static if (op == null)
    {
        foreach (op1; AliasSeq!("~", "+", "-", "++", "--"))
            unary!(op1, N)();
    }
    else static if (is(N == void))
    {
        foreach (N1; AliasSeq!(IntegralTypes, CharTypes))
            unary!(op, N1)();
    }
    else
    {
        static assert(isFixedPoint!N);

        enum sc = "smartOp.unary!\"" ~ op ~ "\"(n)";

        static assert(real.mant_dig >= precision!N);
        auto control(Select!(op == "~", N, real) n, Unused m = null)
        {
            return mixin(op ~ "n");
        }
        enum isVO(N, M, PR) = (PR.sizeof >= N.sizeof) && (isSigned!PR || !op.among!("-", "+"));

        static if (isIntegral!N || !op.among!("++", "--"))
            fuzz!(sc, Unqual, isVO, control, N)();
        else
            forbid!(sc, N)();
    }
}
alias unary(N) = unary!(null, N);

void binary(string op = null, N = void, M = void)()
{
    static if (op == null)
    {
        foreach (op1; AliasSeq!("+", "-", "*", "/", "%", "<<", ">>", ">>>", "&", "|", "^"))
            binary!(op1, N, M)();
    }
    else static if (is(N == void))
    {
        foreach (N1; AliasSeq!(IntegralTypes, CharTypes))
            binary!(op, N1, M)();
    }
    else static if (is(M == void))
    {
        foreach (M1; AliasSeq!(IntegralTypes, CharTypes))
            binary!(op, N, M1)();
    }
    else
    {
        static assert(isFixedPoint!N && isFixedPoint!M);

        static if (isIntegral!N)
            alias UN = Unsigned!N;
        else
            alias UN = N;

        static if (isIntegral!M)
            alias UM = Unsigned!M;
        else
            alias UM = M;

        static void cover(bool assign)()
        {
            enum sc = "smartOp.binary!\"" ~ op ~ (assign? "=" : "") ~ "\"(n, m)";

            static assert(real.mant_dig >= max(precision!N, precision!M));
            static if (op.among!("<<", ">>", ">>>"))
            {
                static N control(const N n, const M m)
                {
                    const shL = (op == "<<") ^ (m < 0);
                    enum int maxSh = (8 * N.sizeof) - 1;
                    const um = cast(UM)stdm.abs(cast(Promoted!M)m);

                    static if (op == ">>>")
                        auto wret = cast(UN)n;
                    else
                        N wret = n;
                    bool again = um > maxSh;
                    const im = again? maxSh : cast(int)um;
                Lagain:
                    wret = cast(typeof(wret))(shL?
                        wret << im :
                        wret >> im);
                    if (again)
                    {
                        again = false;
                        goto Lagain;
                    }

                    return cast(N)wret;
                }
                enum isVO(N, M, PR) = isIntegral!PR && (PR.sizeof == N.sizeof) && (isSigned!PR == isSigned!N);
            }
            else static if (op.among!("&", "|", "^"))
            {
                static auto control(const N n, const M m)
                {
                    static if (assign)
                        alias R = N;
                    else
                    {
                        alias P = Select!(N.sizeof >= M.sizeof, N, M);
                        static if (isIntegral!P)
                            alias UP = Unsigned!P;
                        else
                            alias UP = P;

                        alias R = Select!(isSigned!N && isSigned!M, P, UP);
                    }

                    return cast(R)mixin("n " ~ op ~ " m");
                }
                enum isVO(N, M, PR) = isIntegral!PR && (PR.sizeof == max(N.sizeof, M.sizeof)) &&
                    (isSigned!PR == (isSigned!N && isSigned!M));
            }
            else
            {
                static auto control(const real n, const real m)
                {
                    static if (op == "/")
                        return stdm.trunc(n / m);
                    else
                        return mixin("n " ~ op ~ " m");
                }
                enum isVO(N, M, PR) = isIntegral!PR &&
                    ((isSigned!PR == (isSigned!N || (isSigned!M && op != "%"))) || op == "-");
            }

            static if (isIntegral!N || !assign)
                fuzz!(sc, Unqual, Select!(assign, OutIs!N, isVO), control, N, M)();
            else
                forbid!(sc, N, M)();
        }
        cover!false();
        cover!true();
    }
}
alias binary(N, M = void) = binary!(null, N, M);

void byPow2(string op = null, N = void, M = void)()
{
    static if (op == null)
    {
        foreach (op1; AliasSeq!("*", "/", "%"))
            byPow2!(op1, N, M)();
    }
    else static if (is(N == void))
    {
        foreach (N1; AliasSeq!(IntegralTypes, CharTypes))
            byPow2!(op, N1, M)();
    }
    else static if (is(M == void))
    {
        foreach (M1; AliasSeq!(IntegralTypes, CharTypes))
            byPow2!(op, N, M1)();
    }
    else
    {
        static assert(isScalarType!N && isScalarType!M);

        enum sc = "smartOp." ~ (op == "*"? "mul" : (op == "/"? "div" : "mod")) ~ "Pow2(n, m)";

        static assert(real.mant_dig >= max(precision!N, precision!M));
        real control(const real n, const real m)
        {
            if (n == 0 && stdm.isFinite(m))
                return 0;
            else
            {
                const p2 = stdm.exp2(m);

                static if (op.among!("*", "/"))
                {
                    const wret = mixin("n " ~ op ~ " p2");
                    static if (isFloatingPoint!N || isFloatingPoint!M)
                        return wret;
                    else
                        return stdm.trunc(wret);
                }
                else
                {
                    if (!stdm.isFinite(p2))
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

void pow(N = void, M = void)()
{
    static if (is(N == void))
    {
        foreach (N1; AliasSeq!(IntegralTypes, CharTypes))
            pow!(N1, M)();
    }
    else static if (is(M == void))
    {
        foreach (M1; AliasSeq!(IntegralTypes, CharTypes))
            pow!(N, M1)();
    }
    else
    {
        static assert(isFixedPoint!N && isFixedPoint!M);
        forbid!("smartOp.binary!\"^^\"(n, m)", N, M)();
        forbid!("smartOp.binary!\"^^=\"(n, m)", N, M)();

        enum sc = "smartOp.pow(n, m)";

        static assert(real.mant_dig >= max(precision!N, precision!M));
        real control(const real n, const real m)
        {
            return stdm.trunc(stdm.pow(n, m));
        }
        enum isVO(N, M, PR) = isIntegral!PR && (PR.sizeof >= N.sizeof) && (isSigned!PR == isSigned!N);

        fuzz!(sc, Unqual, isVO, control, N, M)();
    }
}
