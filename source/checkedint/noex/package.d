/**
Copyright: Copyright Thomas Stuart Bockman 2015
License: <a href="http://www.boost.org/LICENSE_1_0.txt">Boost License 1.0</a>.
Authors: Thomas Stuart Bockman
*/

module checkedint.noex;
import checkedint.internal;
public import checkedint.flags;

import future.traits, std.typecons;

public import checkedint :
    isSafeInt,
    isSmartInt,
    isCheckedInt,
    hasBitOps,
    isThrowingCInt,
    BasicScalar;

@safe: /+pragma(inline, true):+/

T to(T, bool throws, S)(const S value)
    if(isScalarType!(BasicScalar!T) && isScalarType!(BasicScalar!S))
{
    const T ret = toImpl!(BasicScalar!T, throws)(value.bscal);

    return ret;
}
T to(T, S)(S value) {
    static if(isScalarType!(BasicScalar!T) && isScalarType!(BasicScalar!S))
        return to!(T, false, S)(value);
    else {
        import std.conv : stdTo = to;
        return stdTo!T(value);
    }
}

public import checkedint :
    bscal,
    bits,
    idx;

public import safeOp = checkedint.noex.safeop;
public import smartOp = checkedint.noex.smartop;

template SafeInt(N, Flag!"bitOps" bitOps = Yes.bitOps, Flag!"throws" throws = No.throws)
    if(isIntegral!N || isCheckedInt!N)
{
    import checkedint : Impl = SafeInt;
    alias SafeInt = Impl!(BasicScalar!N, bitOps, throws);
}
template SafeInt(N, Flag!"throws" throws)
    if(isIntegral!N || isCheckedInt!N)
{
    import checkedint : Impl = SafeInt;
    alias SafeInt = Impl!(BasicScalar!N, Yes.bitOps, throws);
}

template SmartInt(N, Flag!"bitOps" bitOps = Yes.bitOps, Flag!"throws" throws = No.throws)
    if(isIntegral!N || isCheckedInt!N)
{
    import checkedint : Impl = SmartInt;
    alias SmartInt = Impl!(BasicScalar!N, bitOps, throws);
}
template SmartInt(N, Flag!"throws" throws)
    if(isIntegral!N || isCheckedInt!N)
{
    import checkedint : Impl = SmartInt;
    alias SmartInt = Impl!(BasicScalar!N, Yes.bitOps, throws);
}
