/**
Copyright: Copyright Thomas Stuart Bockman 2015
License: <a href="http://www.boost.org/LICENSE_1_0.txt">Boost License 1.0</a>.
Authors: Thomas Stuart Bockman
*/

module checkedint.tests.benchmark;
import checkedint, checkedint.flags, checkedint.traits;

import std.algorithm, std.stdio;
static if(__VERSION__ >= 2068) {
    version(GNU) { static assert(false); }
    import std.meta : AliasSeq;
} else
    import std.typetuple : AliasSeq = TypeTuple;

/+@safe:+/

void benchMacro() {
    benchMacro!"trialPrimes"();
    benchMacro!"collatzSort"();
}

ulong checkSum;
bool invalid;
void benchMacro(string testStr)() {
    import std.conv : to;
    import std.datetime : benchmark, Duration;

    mixin("alias test = " ~ testStr ~ ";");
    writeln();
    write("Running "); write(testStr); writeln("() benchmark... ");
    function() @trusted { stdout.flush(); }();

    checkSum = 0;
    test!int();
    enum trials = 3;
    enum laps = 3;
    const compSum = checkSum * laps * trials;

    foreach(V; AliasSeq!(int, uint, long, ulong)) {
        foreach(N; AliasSeq!(
            V,
            SafeInt!(V, true, false),
            SafeInt!(V, true, true),
            SmartInt!(V, true, false),
            SmartInt!(V, true, true)))
        {
            checkSum = 0;
            invalid = false;
            writef("%40s: ", N.stringof);

            auto best = Duration.max;
            foreach(i; 0 .. trials) {
                auto r = to!Duration(benchmark!(test!N)(laps)[0]) / laps;
                if(r < best)
                    best = r;
            }

            if(checkSum != compSum)
                write("!CHECKSUM ");
            if(invalid)
                write("!INVALID ");
            writeln(to!Duration(best));
        }
    }

    writeln("DONE");
}

template SafeFold(N) {
    template SafeFold(real folded) {
        alias BN = BasicScalar!N;
        static assert(BN.min <= folded && folded <= BN.max);
        enum SafeFold = cast(BN)folded;
    }
}

/+pragma(inline, true) {+/
    auto mulPow2(N, M)(const N coef, const M exp) {
        return coef << exp; }
    auto divPow2(N, M)(const N coef, const M exp) {
        return coef >> exp; }
/+}+/

void trialPrimes(N)() {
    alias V = SafeFold!N;

    static auto floorSqrt(N n) {
        assert(n >= V!0);

        enum N maxT = isSigned!N?
            V!((1414L.mulPow2((N.sizeof * 4) - 11)) - 1L) :
            V!((1L.mulPow2(N.sizeof * 4)) - 1L);
        N t = min((n/V!2 + V!1), maxT);
        N r0 = t;
        N sq0 = r0 * r0;
        assert(n <= sq0);

        while(t >= V!1) {
            if(sq0 < n) {
                const r1 = r0 + t;
                const sq1 = r1 * r1;

                if(sq1 <= n) {
                    r0 = r1;
                    sq0 = sq1;
                } else
                    t /= V!2;
            } else if(sq0 > n) {
                r0 = r0 - t;
                sq0 = r0 * r0;

                t /= V!2;
            } else
                break;
        }

        return r0;
    }

    enum PrimeCount = V!40000;
    N[PrimeCount] primes;
    N[PrimeCount] primeRoots;

    N p = V!0;
    primes[idx(p)] = N.max;
    N n = V!2;
    while(true) {
        const N rootN = floorSqrt(n);

        bool pass = true;
        for(N dP = V!0; primes[idx(dP)] <= rootN; ++dP) {
            if(n % primes[idx(dP)] == V!0) {
                pass = false;
                break;
            }
        }

        if(pass) {
            primes[idx(p)] = n;
            primeRoots[idx(p)] = rootN;

            ++p;
            if(p < PrimeCount)
                primes[idx(p)] = N.max;
            else
                break;
        }

        ++n;
    }

    N subSum = V!0;
    for(N pu = V!0; pu < PrimeCount; ++pu)
        subSum += primeRoots[idx(pu)];
    checkSum += subSum.bscal;
    invalid = invalid || IntFlags.local;
    IntFlags.local.clear();

  /+for(N q = 0; q < p; ++q) {
        write(primes[idx(q)]);
        write(" : ");
        write(primeRoots[idx(q)]);
        if(q % 8 != 7)
            write(", ");
        else
            writeln();
    }
    writeln();
    stdin.readln();+/
}

void collatzSort(N)() {
    alias V = SafeFold!N;

    static void quickSort(N[] array, N lowX, N highX) {
        if(lowX >= highX)
            return;

        N pivotX = (lowX + highX).divPow2(1u);
        N pivotV = array[idx(pivotX)];
        array[idx(pivotX)] = array[idx(highX)];
        array[idx(highX)] = pivotV;

        N storeX = lowX;
        N iX = lowX;
        while(iX < highX) {
            const iV = array[idx(iX)];
            if(iV < pivotV) {
                array[idx(iX)] = array[idx(storeX)];
                array[idx(storeX)] = iV;
                ++storeX;
            }
            ++iX;
        }
        pivotX = storeX;

        pivotV = array[idx(pivotX)];
        array[idx(pivotX)] = array[idx(highX)];
        array[idx(highX)] = pivotV;

        quickSort(array, lowX, pivotX - V!1);
        quickSort(array, pivotX + V!1, highX);
    }

    enum N maxN = V!113_382;
    N[idx(maxN)] finalIs;

    for(N n = V!0; n < maxN; ++n) {
        N i = V!0;
        N ai = n + V!1;
        while(ai != V!1) {
            if((ai & V!0x1) ==  V!0)
                ai = ai.divPow2(1u);
            else
                ai = V!3*ai + V!1;

            ++i;
        }

        finalIs[idx(n)] = i;
    }

    quickSort(finalIs, N(V!0), maxN - V!1);

    N subSum = finalIs[0];
    for(N x = V!1; x < maxN; ++x) {
        subSum += finalIs[idx(x)];
        if(finalIs[idx(x)] < finalIs[idx(x - V!1)])
            invalid = true;
    }
    checkSum += subSum.bscal;
    invalid = invalid || IntFlags.local;
    IntFlags.local.clear();
}
