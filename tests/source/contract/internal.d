/**
Utilities for testing contract compliance, and printing detailed error
messages when a test case fails.

Copyright: Copyright Thomas Stuart Bockman 2015
License: $(LINK2 http://www.boost.org/LICENSE_1_0.txt, Boost License 1.0).
Authors: Thomas Stuart Bockman
**/
module checkedint.tests.contract.internal;
public import checkedint.tests.values;

import checkedint.sticky;

public import std.algorithm, std.format, std.stdio, future.traits0;
public static import stdm = std.math;
public import std.meta;

package: @safe:

alias Unused = typeof(null);
template OutIs(T)
{
    enum OutIs(N, M, PR) = is(PR == T);
}

private template TypeFmt(T)
    if (isScalarType!T)
{
    static if (isFloatingPoint!T)
        enum TypeFmt = "%+." ~ format("%d", (T.mant_dig + 2) / 3) ~ "g";
    else static if (isIntegral!T || isSomeChar!T)
        enum TypeFmt = "%+d";
    else
        enum TypeFmt = "%s";
}

void forbid(string subjectCall, N, M = Unused)()
{
    N n;
    static if (! is(M == Unused))
        M m = 1; // Don't try to divide by zero.

    static if (__traits(compiles, mixin(subjectCall)))
    {
        writeln();
        writeln(subjectCall);
        writeln("\t" ~ N.stringof ~ " n;");
        static if (! is(M == Unused))
            writeln("\t" ~ M.stringof ~ " m;");
        writeln("\tFAILS: forbidden");
    }
}

void fuzz(alias subjectCall, alias SubjectIn, alias isValidOut, alias control, N, M = Unused)()
{
    enum isBin = !is(M == Unused);

    static if (is(typeof(subjectCall) == string))
    {
        static auto subject(const N nn, const M mm)
        {
            SubjectIn!N n = nn;
            static if (isBin)
                SubjectIn!M m = mm;
            return mixin(subjectCall);
        }
    } else
        alias subject = subjectCall;

    alias PR = Unqual!(typeof(subject(N.init, M.init)));
    static if (!isValidOut!(N, M, PR))
    {
        writeln();
        writeln(subjectCall);
        writeln("\t" ~ N.stringof ~ " n;");
        static if (isBin)
            writeln("\t" ~ M.stringof ~ " m;");
        writeln("\t" ~ PR.stringof ~ " practice;");
        writeln("\tFAILS: return type");
        return;
    }
    else
    {
        alias TR = Unqual!(typeof(control(N.init, M.init)));
        foreach (const m; TestValues!M())
        {
            foreach (const n; TestValues!N())
            {
                const theory = control(n, m);
                bool thrInval;
                static if (isFloatingPoint!TR || !isScalarType!TR)
                    thrInval = stdm.isNaN(theory);

                IntFlags.local.clear();
                const practice = subject(n, m);
                bool pracInval = IntFlags.local;
                static if (isFloatingPoint!PR || !isScalarType!PR)
                    pracInval |= stdm.isNaN(practice);

                uint failCount = 0;
                void require(string name, bool success)
                {
                    if (success)
                        return;

                    if (failCount <= 0)
                    {
                        writeln();
                        writeln(subjectCall);
                        writefln("\t" ~ N.stringof ~ " n = " ~ TypeFmt!N, n);
                        static if (isBin)
                            writefln("\t" ~ M.stringof ~ " m = " ~ TypeFmt!M, m);
                        writefln("\t" ~ TR.stringof ~ " theory = " ~ TypeFmt!TR, theory);
                        writefln("\t" ~ PR.stringof ~ " practice = " ~ TypeFmt!PR, practice);
                        writefln("\tIntFlags.local  = %s", IntFlags.local);

                        write("\tFAILS: ");
                    }
                    else
                        write(", ");

                    writef(name);
                    ++failCount;
                }

                static if (isFloatingPoint!TR && isFloatingPoint!PR)
                    const tpMatch = stdm.feqrel(theory, practice) >= (min(TR.mant_dig, PR.mant_dig) - 1);
                else
                    const tpMatch = (theory == practice);
                require("correct", (!thrInval && tpMatch) ^ pracInval);

                enum allFlags = IntFlag.undef | IntFlag.div0 | IntFlag.imag |
                    IntFlag.over | IntFlag.posOver | IntFlag.negOver;
                IntFlags.local = allFlags;
                const practiceT = subject(n, m);
                require("sticky", IntFlags.local);
                IntFlags.local.clear();

                bool consistent = (practiceT == practice);
                static if (isFloatingPoint!PR)
                    consistent |= (stdm.isNaN(practiceT) && stdm.isNaN(practice));
                require("consistent", consistent);

                if (failCount > 0)
                    writeln();
            }
        }
    }
}
