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
static if(__VERSION__ >= 2068) {
    version(GNU) { static assert(false); }
    import std.meta : AliasSeq;
} else
    import std.typetuple : AliasSeq = TypeTuple;

pure: nothrow: @nogc: @safe:

alias
    IntegralTypes = AliasSeq!(byte, ubyte, short, ushort, int, uint, long, ulong),
    FloatingTypes = AliasSeq!(float, double ,real),
    NumericTypes = AliasSeq!(IntegralTypes, FloatingTypes),
    CharTypes = AliasSeq!(char, wchar, dchar),
    FixedTypes = AliasSeq!(bool, CharTypes, IntegralTypes),
    ScalarTypes = AliasSeq!(FixedTypes, FloatingTypes);

struct TestValues(N)
    if(is(N == void*))
{
    bool empty = false;
    void* front() const {
        return null; }
    void popFront() {
        empty = true; }
}

struct TestValues(N)
    if(is(N == bool))
{
private:
    int idx = 0;

public:
    @property bool empty() const {
        return idx <= 1; }
    @property bool front() const {
        return idx != 0; }
    @property void popFront() {
        ++idx; }
}

private enum ulong[] naturals = function() {
    ulong[34 + 3*(64 - 5) - 2] nats;

    size_t n = 0;
    while(n <= 33) {
        nats[n] = n;
        ++n;
    }

    int sh = 6;
    while(sh < 64) {
        nats[n++] = (1uL << sh) -1;
        nats[n++] = (1uL << sh);
        nats[n++] = (1uL << sh) + 1;
        ++sh;
    }
    nats[n] = ulong.max;

    return nats;
}();
struct TestValues(N)
    if(isIntegral!N || isSomeChar!N)
{
private:
    enum maxIdx = function() {
        // Test dchar values greater than dchar.max, also:
        enum ulong trueNmax = isSomeChar!N? ~cast(N)0 : N.max;

        auto x = cast(ptrdiff_t)(naturals.length - 1);
        while(naturals[x] > trueNmax)
            --x;
        return x;
    }();
    enum minIdx = isSigned!N? -(maxIdx + 1) : 0;

    ptrdiff_t index = minIdx;

public:
    @property bool empty() const {
        return index > maxIdx; }
    @property N front() const {
        static if(isSigned!N) {
            if(index < 0)
                return -cast(N)naturals[-index];
        }

        return cast(N)naturals[index];
    }
    @property void popFront() {
        ++index; }
}

private enum real[] normal_exps = [
    real.min_exp < double.min_exp? pow(2.0L, real.min_exp - 1) : 0.0,
    real.min_exp < double.min_exp? pow(2.0L, real.min_exp) : 0.0,

    pow(2.0L, double.min_exp - 1),
    pow(2.0L, double.min_exp),

    pow(2.0L, -722),

    pow(2.0L, float.min_exp - 1),
    pow(2.0L, float.min_exp),

    pow(2.0L, -13),
    pow(2.0L, -12),

    pow(2.0L, -4),
    pow(2.0L, -3),
    pow(2.0L, -2),
    pow(2.0L, -1),

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
    pow(2.0L, 64),

    pow(2.0L, 104),
    pow(2.0L, 105),
    pow(2.0L, 106),
    pow(2.0L, 111),
    pow(2.0L, 112),
    pow(2.0L, 113),
    pow(2.0L, 125),

    // cent
    pow(2.0L, float.max_exp - 2),
    // ucent
    pow(2.0L, float.max_exp - 1),
    pow(2.0L, float.max_exp),
    pow(2.0L, 437),
    pow(2.0L, double.max_exp - 2),
    pow(2.0L, double.max_exp - 1),
    pow(2.0L, double.max_exp),
    real.max_exp > double.max_exp? pow(2.0L, real.max_exp - 2) : real.infinity,
    real.max_exp > double.max_exp? pow(2.0L, real.max_exp - 1) : real.infinity
];
struct TestValues(N)
    if(isFloatingPoint!N)
{
private:
    enum minExpIdx = function() {
        ptrdiff_t expX = 0;
        while(!(normal_exps[expX] >= N.min_normal))
            ++expX;
        return expX;
    }();
    enum maxExpIdx = function() {
        ptrdiff_t expX = normal_exps.length - 1;
        while(!(normal_exps[expX] <= N.max))
            --expX;
        return expX;
    }();
    enum expCount = (maxExpIdx - minExpIdx) + 1;

    enum N[] normal_mants = [
        1.0L,
        1.0L + N.epsilon,
        LN2 * 2.0L,
        E * 0.5L,
        SQRT2,
        PI * 0.5L,
        2.0L - (N.epsilon * 2.0L),
        2.0L - N.epsilon
    ];
    enum ptrdiff_t maxIdx = (expCount * normal_mants.length) + 2;

    auto index = -maxIdx;
    N _front = -N.infinity;

public:
    @property bool empty() const {
        return index > maxIdx; }
    @property N front() const {
        return _front; }
    @property void popFront() {
        ++index;

        const negIdx = index < 0;
        const absIdx = negIdx? -index : index;

        if(absIdx <= 1)
            _front = (absIdx == 0)? N.nan : 0;
        else if(absIdx < maxIdx) {
            const mant = normal_mants[(absIdx - 2) % normal_mants.length];
            const expC = normal_exps[minExpIdx + (absIdx - 2) / normal_mants.length];
            _front = mant * expC;
        } else
            _front = N.infinity;

        if(negIdx)
            _front = -_front;
    }
}
