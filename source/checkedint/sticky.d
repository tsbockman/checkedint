/**
Aliases for the $(LINK2 ./package.html, `checkedint`) module using `IntFlagPolicy.sticky`.

Copyright: Copyright Thomas Stuart Bockman 2015
License: $(LINK2 http://www.boost.org/LICENSE_1_0.txt, Boost License 1.0).
Authors: Thomas Stuart Bockman
**/
module checkedint.sticky;

import future.traits0, std.typecons;

@safe: pragma(inline, true):

static import checkedint.flags;
public import checkedint.flags :
    IntFlagPolicy,
    intFlagPolicyOf,
    IntFlag,
    IntFlags,
    CheckedIntException;
private alias IFP = IntFlagPolicy;

alias raise = checkedint.flags.raise!(IFP.sticky);

static import checkedint;

alias SmartInt(N, Flag!"bitOps" bitOps = Yes.bitOps) = checkedint.SmartInt!(N, IFP.sticky, bitOps);
SmartInt!(N, bitOps) smartInt(Flag!"bitOps" bitOps = Yes.bitOps, N)(N num) nothrow @nogc
    if (isIntegral!N || isCheckedInt!N)
{
    return typeof(return)(num.bscal);
}
alias smartOp = checkedint.smartOp!(IFP.sticky);

alias DebugInt(N, Flag!"bitOps" bitOps = Yes.bitOps) = checkedint.DebugInt!(N, IFP.sticky, bitOps);

alias SafeInt(N, Flag!"bitOps" bitOps = Yes.bitOps) = checkedint.SafeInt!(N, IFP.sticky, bitOps);
SafeInt!(N, bitOps) safeInt(Flag!"bitOps" bitOps = Yes.bitOps, N)(N num) nothrow @nogc
    if (isIntegral!N || isCheckedInt!N)
{
    return typeof(return)(num.bscal);
}
alias safeOp = checkedint.safeOp!(IFP.sticky);

alias to(T) = checkedint.to!(T, IFP.sticky);

Select!(isSigned!(BasicScalar!N), ptrdiff_t, size_t) idx(N)(const N num) nothrow @nogc
    if (isScalarType!N || isCheckedInt!N)
{
    return checkedint.to!(typeof(return), IFP.sticky)(num.bscal);
}

public import checkedint :
    bscal,
    bits,
    isSafeInt,
    isSmartInt,
    isCheckedInt,
    hasBitOps,
    BasicScalar;
