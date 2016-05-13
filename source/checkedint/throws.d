/**
Copyright: Copyright Thomas Stuart Bockman 2015
License: $(LINK2 http://www.boost.org/LICENSE_1_0.txt, Boost License 1.0).
Authors: Thomas Stuart Bockman
*/
module checkedint.throws;

import future.traits, std.typecons;

@safe: /+pragma(inline, true):+/

static import checkedint.flags;
public import checkedint.flags :
    IntFlag,
    IntFlags,
    CheckedIntException;

alias raise = checkedint.flags.raise!(Yes.throws);

static import checkedint;

alias SmartInt(N, Flag!"bitOps" bitOps = Yes.bitOps) = checkedint.SmartInt!(N, Yes.throws, bitOps);
SmartInt!(N, bitOps) smartInt(Flag!"bitOps" bitOps = Yes.bitOps, N)(N num) pure
    if(isIntegral!N || isCheckedInt!N)
{
    return typeof(return)(num.bscal);
}
alias smartOp = checkedint.smartOp!(Yes.throws);

alias DebugInt(N, Flag!"bitOps" bitOps = Yes.bitOps) = checkedint.DebugInt!(N, Yes.throws, bitOps);

alias SafeInt(N, Flag!"bitOps" bitOps = Yes.bitOps) = checkedint.SafeInt!(N, Yes.throws, bitOps);
SafeInt!(N, bitOps) safeInt(Flag!"bitOps" bitOps = Yes.bitOps, N)(N num) pure
    if(isIntegral!N || isCheckedInt!N)
{
    return typeof(return)(num.bscal);
}
alias safeOp = checkedint.safeOp!(Yes.throws);

alias to(T) = checkedint.to!(T, Yes.throws);

Select!(isSigned!(BasicScalar!N), ptrdiff_t, size_t) idx(N)(const N num) pure
    if(isScalarType!N || isCheckedInt!N)
{
    return checkedint.to!(typeof(return), Yes.throws)(num.bscal);
}

public import checkedint :
    bscal,
    bits,
    isSafeInt,
    isSmartInt,
    isCheckedInt,
    hasBitOps,
    isThrowingCInt,
    BasicScalar;
