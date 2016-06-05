/**
Templates to facilitate treating $(LINK2 ./package.html#SmartInt, `checkedint.SmartInt`) and $(LINK2 ./package.html#SafeInt, `checkedint.SafeInt`) like the built-in numeric types in
generic code.

Copyright: Copyright Thomas Stuart Bockman 2015
License: $(LINK2 http://www.boost.org/LICENSE_1_0.txt, Boost License 1.0).
Authors: Thomas Stuart Bockman

This module wraps various templates from `std.traits` to make them `checkedint`-aware. For example,
`std.traits.isSigned!(SmartInt!int)` is `false`, but `checkedint.traits.isSigned!(SmartInt!int)` is `true`.

This module is separate from `checkedint` because it is only useful in generic code, and its symbols (deliberately)
conflict with some from `std.traits`.
**/
module checkedint.traits;
import checkedint.asserts : SmartInt;

static if (__VERSION__ >= 2068)
{
    version(GNU) { static assert(false); }
    import std.meta : AliasSeq;
}
else
    import std.typetuple : AliasSeq = TypeTuple;

// checkedint.flags //////////////////////////////////////
static import checkedint.flags;

    /// See $(LINK2 ./flags.html#intFlagPolicyOf, `checkedint.flags.intFlagPolicyOf`)
    alias intFlagPolicyOf = checkedint.flags.intFlagPolicyOf;


// checkedint ////////////////////////////////////////////
static import chkd = checkedint;

    /// See $(LINK2 ./package.html#isSafeInt, `checkedint.isSafeInt`)
    alias isSafeInt = chkd.isSafeInt;

    /// See $(LINK2 ./package.html#isSmartInt, `checkedint.isSmartInt`)
    alias isSmartInt = chkd.isSmartInt;

    /// See $(LINK2 ./package.html#isCheckedInt, `checkedint.isCheckedInt`)
    alias isCheckedInt = chkd.isCheckedInt;

    /// See $(LINK2 ./package.html#hasBitOps, `checkedint.hasBitOps`)
    alias hasBitOps = chkd.hasBitOps;

    /// See $(LINK2 ./package.html#BasicScalar, `checkedint.BasicScalar`)
    alias BasicScalar = chkd.BasicScalar;


// std.traits ////////////////////////////////////////////
static import bsct = future.traits0;

    private template isEx(alias Predicate, T)
    {
        static if (isCheckedInt!T)
            enum isEx = Predicate!(BasicScalar!T);
        else
            enum isEx = Predicate!T;
    }

    /// See `std.traits.isScalarType`
    alias isBasicScalar = bsct.isScalarType;
    /// `checkedint`-aware wrapper for `std.traits.isScalarType`
    template isScalarType(T)
    {
        alias isScalarType = isEx!(isBasicScalar, T);
    }
    ///
    unittest
    {
        foreach (T; AliasSeq!(int, ushort, double, bool))
            assert(isBasicScalar!T && isScalarType!T);

        assert(!isBasicScalar!(SmartInt!int));
        assert( isScalarType!(SmartInt!int));

        foreach (T; AliasSeq!(int[]))
            assert(!(isBasicScalar!T || isScalarType!T));
    }

    /// See `std.traits.isNumeric`
    alias isBasicNum = bsct.isNumeric;
    /// `checkedint`-aware wrapper for `std.traits.isNumeric`
    template isNumeric(T)
    {
        alias isNumeric = isEx!(isBasicNum, T);
    }
    ///
    unittest
    {
        foreach (T; AliasSeq!(int, ushort, double))
            assert(isBasicNum!T && isNumeric!T);

        assert(!isBasicNum!(SmartInt!int));
        assert( isNumeric!(SmartInt!int));

        foreach (T; AliasSeq!(int[], bool))
            assert(!(isBasicNum!T || isNumeric!T));
    }

    /// See `std.traits.isFloatingPoint`
    alias isFloatingPoint = bsct.isFloatingPoint;

    /// See `future.traits.isFixedPoint`
    alias isBasicFixed = bsct.isFixedPoint;
    /// `checkedint`-aware wrapper for `future.traits.isFixedPoint`
    template isFixedPoint(T)
    {
        alias isFixedPoint = isEx!(isBasicFixed, T);
    }
    ///
    unittest
    {
        foreach (T; AliasSeq!(int, ushort, bool))
            assert(isBasicFixed!T && isFixedPoint!T);

        assert(!isBasicFixed!(SmartInt!int));
        assert( isFixedPoint!(SmartInt!int));

        foreach (T; AliasSeq!(double, int[]))
            assert(!(isBasicFixed!T || isFixedPoint!T));
    }

    /// See `std.traits.isIntegral`
    alias isBasicInt = bsct.isIntegral;
    /// `checkedint`-aware wrapper for `std.traits.isIntegral`
    template isIntegral(T)
    {
        alias isIntegral = isEx!(isBasicInt, T);
    }
    ///
    unittest
    {
        foreach (T; AliasSeq!(int, ushort))
            assert(isBasicInt!T && isIntegral!T);

        assert(!isBasicInt!(SmartInt!int));
        assert( isIntegral!(SmartInt!int));

        foreach (T; AliasSeq!(double, int[], bool))
            assert(!(isBasicInt!T || isIntegral!T));
    }

    /// See `std.traits.isSomeChar`
    alias isSomeChar = bsct.isSomeChar;
    /// See `std.traits.isBoolean`
    alias isBoolean = bsct.isBoolean;

    /// See `std.traits.isSigned`
    alias isBasicSigned = bsct.isSigned;
    /// `checkedint`-aware wrapper for `std.traits.isSigned`
    template isSigned(T)
    {
        alias isSigned = isEx!(isBasicSigned, T);
    }
    ///
    unittest
    {
        foreach (T; AliasSeq!(int, double))
            assert(isBasicSigned!T && isSigned!T);

        assert(!isBasicSigned!(SmartInt!int));
        assert( isSigned!(SmartInt!int));

        foreach (T; AliasSeq!(ushort, int[], bool))
            assert(!(isBasicSigned!T || isSigned!T));
    }

    /// See `std.traits.isUnsigned`
    alias isBasicUnsigned = bsct.isUnsigned;
    /// `checkedint`-aware wrapper for `isUnsigned`
    template isUnsigned(T)
    {
        alias isUnsigned = isEx!(isBasicUnsigned, T);
    }
    ///
    unittest
    {
        foreach (T; AliasSeq!(ushort))
            assert(isBasicUnsigned!T && isUnsigned!T);

        assert(!isBasicUnsigned!(SmartInt!uint));
        assert( isUnsigned!(SmartInt!uint));

        foreach (T; AliasSeq!(double, int[], bool))
            assert(!(isBasicUnsigned!T || isUnsigned!T));
    }

    /// `checkedint`-aware version of `std.traits.mostNegative`
    template mostNegative(T)
        if (isNumeric!T)
    {
        static if (isFloatingPoint!T)
            enum mostNegative = -T.max;
        else
            enum mostNegative =  T.min;
    }
    ///
    unittest
    {
        assert(mostNegative!int == int.min);
        static assert(is(typeof(mostNegative!int) == int));
        assert(mostNegative!(SmartInt!int) == SmartInt!(int).min);
        static assert(is(typeof(mostNegative!(SmartInt!int)) == SmartInt!int));
    }

    private template TransEx(alias TypeTransform, T)
    {
        static if (isCheckedInt!T)
        {
            import checkedint : SmartInt, SafeInt;
            import future.traits0 : CopyTypeQualifiers, Select;

            alias TTB = TypeTransform!(CopyTypeQualifiers!(T, BasicScalar!T));
            alias CheckedInt = Select!(isSmartInt!T, SmartInt, SafeInt);
            alias TransEx = CopyTypeQualifiers!(TTB, CheckedInt!(TTB, intFlagPolicyOf!T, hasBitOps!T));
        } else
            alias TransEx = TypeTransform!T;
    }

    /// `checkedint`-aware wrapper for `std.traits.Signed`
    template Signed(T)
    {
        alias Signed = TransEx!(bsct.Signed, T);
    }
    ///
    unittest
    {
        static assert(is(Signed!int == int));
        static assert(is(Signed!(SmartInt!int) == SmartInt!int));
        static assert(is(Signed!ulong == long));
        static assert(is(Signed!(SmartInt!ulong) == SmartInt!long));
    }

    /// `checkedint`-aware wrapper for `std.traits.Unsigned`
    template Unsigned(T)
    {
        alias Unsigned = TransEx!(bsct.Unsigned, T);
    }
    ///
    unittest
    {
        static assert(is(Unsigned!int == uint));
        static assert(is(Unsigned!(SmartInt!int) == SmartInt!uint));
        static assert(is(Unsigned!ulong == ulong));
        static assert(is(Unsigned!(SmartInt!ulong) == SmartInt!ulong));
    }

    /// `checkedint`-aware wrapper for `future.traits.Promoted`
    template Promoted(T)
    {
        alias Promoted = TransEx!(bsct.Promoted, T);
    }
    ///
    unittest
    {
        static assert(is(Promoted!byte == int));
        static assert(is(Promoted!(SmartInt!byte) == SmartInt!int));
        static assert(is(Promoted!int == int));
        static assert(is(Promoted!(SmartInt!int) == SmartInt!int));
    }
