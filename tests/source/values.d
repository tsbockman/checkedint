/**
Generate numeric test values hitting all the likely corner cases for simple
integer math algorithms. Floating-point is also well-covered, with the
exception of subnormal values.

Copyright: Copyright Thomas Stuart Bockman 2015
License: $(LINK2 http://www.boost.org/LICENSE_1_0.txt, Boost License 1.0).
Authors: Thomas Stuart Bockman
**/
module checkedint.tests.values;

import std.math, future.traits0;
import std.meta : AliasSeq;

pure: nothrow: @nogc: @safe:

alias
    IntegralTypes = AliasSeq!(byte, ubyte, short, ushort, int, uint, long, ulong),
    FloatingTypes = AliasSeq!(float, double ,real),
    NumericTypes = AliasSeq!(IntegralTypes, FloatingTypes),
    CharTypes = AliasSeq!(char, wchar, dchar),
    FixedTypes = AliasSeq!(bool, CharTypes, IntegralTypes),
    ScalarTypes = AliasSeq!(FixedTypes, FloatingTypes);

struct TestValues(N)
    if (is(N == void*))
{
    bool empty = false;
    void* front() const
    {
        return null;
    }
    void popFront()
    {
        empty = true;
    }
}

struct TestValues(N)
    if (is(N == bool))
{
private:
    int idx = 0;

public:
    @property bool empty() const
    {
        return idx <= 1;
    }
    @property bool front() const
    {
        return idx != 0;
    }
    @property void popFront()
    {
        ++idx;
    }
}

struct TestValues(N)
    if ((isIntegral!N || isSomeChar!N) && isUnqual!N)
{
private:
    static if (is(N == ulong))
    {
        static immutable N[] naturals = function()
        {
            ulong[34 + 3*(64 - 5) - 2] nats;

            size_t n = 0;
            while (n <= 33)
            {
                nats[n] = n;
                ++n;
            }

            int sh = 6;
            while (sh < 64)
            {
                nats[n++] = (1uL << sh) -1;
                nats[n++] = (1uL << sh);
                nats[n++] = (1uL << sh) + 1;
                ++sh;
            }
            nats[n] = ulong.max;

            return nats;
        }();

        enum ptrdiff_t maxIdx = naturals.length - 1;
    }
    else
    {
        alias naturals = TestValues!(ulong).naturals;

        enum ptrdiff_t maxIdx = function()
        {
            // Test dchar values greater than dchar.max, also:
            enum ulong trueNmax = isSomeChar!N? ~0uL : N.max;

            auto x = cast(ptrdiff_t)(naturals.length - 1);
            while (naturals[x] > trueNmax)
                --x;
            return x;
        }();
    }
    enum ptrdiff_t minIdx = isSigned!N? -(maxIdx + 1) : 0;

    ptrdiff_t index = minIdx;

public:
    @property bool empty() const
    {
        return index > maxIdx;
    }
    @property N front() const
    {
        static if (isSigned!N)
        {
            if (index < 0)
                return cast(N)-cast(Promoted!N)naturals[-index];
        }

        return cast(N)naturals[index];
    }
    @property void popFront()
    {
        ++index;
    }
}

private enum real ctPow2(int exponent) = mixin("0x1.0p" ~ exponent.stringof ~ "L");

struct TestValues(N)
    if (isFloatingPoint!N && isUnqual!N)
{
private:
    static if (is(N == real))
    {
        enum real[] normal_exps_small = [
            ctPow2!(real.min_exp - 1),
            ctPow2!(real.min_exp)
        ];
        enum real[] normal_exps_core = [
            ctPow2!(double.min_exp - 1),
            ctPow2!(double.min_exp),

            ctPow2!(-722),

            ctPow2!(float.min_exp - 1),
            ctPow2!(float.min_exp),

            ctPow2!(-13),
            ctPow2!(-12),

            ctPow2!(-4),
            ctPow2!(-3),
            ctPow2!(-2),
            ctPow2!(-1),

            1uL << 0,
            1uL << 1,
            1uL << 2,
            1uL << 3,
            1uL << 4,

            // byte
            (byte.max >> 1) + 1,
            // ubyte
            (ubyte.max >> 1) + 1,
            1uL << 8,
            1uL << 10,
            1uL << 11,
            1uL << 12,
            1uL << 13,
            // short
            (short.max >> 1) + 1,
            // ushort
            (ushort.max >> 1) + 1,
            1uL << 16,
            1uL << 23,
            1uL << 24,
            1uL << 25,
            // int
            (int.max >> 1) + 1,
            // uint
            (uint.max >> 1) + 1,
            1uL << 32,
            1uL << 52,
            1uL << 53,
            1uL << 54,
            1uL << 61,
            // long
            (long.max >> 1) + 1,
            // ulong
            (ulong.max >> 1) + 1,
            ctPow2!(64),

            ctPow2!(104),
            ctPow2!(105),
            ctPow2!(106),
            ctPow2!(111),
            ctPow2!(112),
            ctPow2!(113),
            ctPow2!(125),

            // cent
            ctPow2!(float.max_exp - 2),
            // ucent
            ctPow2!(float.max_exp - 1),
            ctPow2!(float.max_exp),
            ctPow2!(437),
            ctPow2!(double.max_exp - 2),
            ctPow2!(double.max_exp - 1)
        ];
        enum real[] normal_exps_large = [
            ctPow2!(double.max_exp),
            ctPow2!(real.max_exp - 2),
            ctPow2!(real.max_exp - 1)
        ];

        static if (is(real == double))
            static immutable real[] normal_exps = normal_exps_core;
        else
            static immutable real[] normal_exps = normal_exps_small ~ normal_exps_core ~ normal_exps_large;
    }
    else
    {
        static immutable N[] normal_exps = function()
        {
            const normal_exps = TestValues!(real).normal_exps;

            ptrdiff_t minExpIdx = 0;
            while (!(normal_exps[minExpIdx] >= N.min_normal))
                ++minExpIdx;

            ptrdiff_t maxExpIdx = normal_exps.length - 1;
            while (!(normal_exps[maxExpIdx] <= N.max))
                --maxExpIdx;

            auto ret = new N[(maxExpIdx - minExpIdx) + 1];
            foreach(x; minExpIdx .. maxExpIdx + 1)
                ret[x - minExpIdx] = cast(N)normal_exps[x];
            return ret.idup;
        }();
    }

    static immutable N[] normal_mants = [
        1.0L,
        1.0L + N.epsilon,
        LN2 * 2.0L,
        E * 0.5L,
        SQRT2,
        PI * 0.5L,
        2.0L - (N.epsilon * 2.0L),
        2.0L - N.epsilon
    ];
    enum ptrdiff_t maxIdx = (normal_exps.length * normal_mants.length) + 2;

    auto index = -maxIdx;
    N _front = -N.infinity;

public:
    @property bool empty() const
    {
        return index > maxIdx;
    }
    @property N front() const
    {
        return _front;
    }
    @property void popFront()
    {
        ++index;

        const negIdx = index < 0;
        const absIdx = negIdx? -index : index;

        if (absIdx <= 1)
            _front = (absIdx == 0)? N.nan : 0;
        else if (absIdx < maxIdx)
        {
            const mant = normal_mants[(absIdx - 2) % normal_mants.length];
            const expC = normal_exps[(absIdx - 2) / normal_mants.length];
            _front = mant * expC;
        }
        else
            _front = N.infinity;

        if (negIdx)
            _front = -_front;
    }
}
