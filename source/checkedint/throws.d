/**
Aliases for the `checkedint` module using the `throws` `IntFlagPolicy`.

Copyright: Copyright Thomas Stuart Bockman 2015
License: $(LINK2 http://www.boost.org/LICENSE_1_0.txt, Boost License 1.0).
Authors: Thomas Stuart Bockman
**/
module checkedint.throws;

import future.traits0, std.typecons;

@safe: /+pragma(inline, true):+/

static import checkedint.flags;
public import checkedint.flags :
    IntFlagPolicy,
    IntFlag,
    IntFlags,
    CheckedIntException;
private alias IFP = IntFlagPolicy;

alias raise = checkedint.flags.raise!(IFP.throws);

static import checkedint;

alias SmartInt(N, Flag!"bitOps" bitOps = Yes.bitOps) = checkedint.SmartInt!(N, IFP.throws, bitOps);
SmartInt!(N, bitOps) smartInt(Flag!"bitOps" bitOps = Yes.bitOps, N)(N num) pure
    if (isIntegral!N || isCheckedInt!N)
{
    return typeof(return)(num.bscal);
}
alias smartOp = checkedint.smartOp!(IFP.throws);

alias DebugInt(N, Flag!"bitOps" bitOps = Yes.bitOps) = checkedint.DebugInt!(N, IFP.throws, bitOps);

alias SafeInt(N, Flag!"bitOps" bitOps = Yes.bitOps) = checkedint.SafeInt!(N, IFP.throws, bitOps);
SafeInt!(N, bitOps) safeInt(Flag!"bitOps" bitOps = Yes.bitOps, N)(N num) pure
    if (isIntegral!N || isCheckedInt!N)
{
    return typeof(return)(num.bscal);
}
alias safeOp = checkedint.safeOp!(IFP.throws);

alias to(T) = checkedint.to!(T, IFP.throws);

Select!(isSigned!(BasicScalar!N), ptrdiff_t, size_t) idx(N)(const N num) pure
    if (isScalarType!N || isCheckedInt!N)
{
    return checkedint.to!(typeof(return), IFP.throws)(num.bscal);
}

public import checkedint :
    bscal,
    bits,
    isSafeInt,
    isSmartInt,
    isCheckedInt,
    hasBitOps,
    intFlagPolicyOf,
    BasicScalar;
