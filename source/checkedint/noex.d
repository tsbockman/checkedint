/**
Aliases for the `checkedint` module using the `noex` `IntFlagPolicy`.

Copyright: Copyright Thomas Stuart Bockman 2015
License: $(LINK2 http://www.boost.org/LICENSE_1_0.txt, Boost License 1.0).
Authors: Thomas Stuart Bockman
**/
module checkedint.noex;

import future.traits0, std.typecons;

@safe: /+pragma(inline, true):+/

static import checkedint.flags;
public import checkedint.flags :
    IntFlagPolicy,
    IntFlag,
    IntFlags,
    CheckedIntException;
private alias IFP = IntFlagPolicy;

alias raise = checkedint.flags.raise!(IFP.noex);

static import checkedint;

alias SmartInt(N, Flag!"bitOps" bitOps = Yes.bitOps) = checkedint.SmartInt!(N, IFP.noex, bitOps);
SmartInt!(N, bitOps) smartInt(Flag!"bitOps" bitOps = Yes.bitOps, N)(N num) nothrow @nogc
    if (isIntegral!N || isCheckedInt!N)
{
    return typeof(return)(num.bscal);
}
alias smartOp = checkedint.smartOp!(IFP.noex);

alias DebugInt(N, Flag!"bitOps" bitOps = Yes.bitOps) = checkedint.DebugInt!(N, IFP.noex, bitOps);

alias SafeInt(N, Flag!"bitOps" bitOps = Yes.bitOps) = checkedint.SafeInt!(N, IFP.noex, bitOps);
SafeInt!(N, bitOps) safeInt(Flag!"bitOps" bitOps = Yes.bitOps, N)(N num) nothrow @nogc
    if (isIntegral!N || isCheckedInt!N)
{
    return typeof(return)(num.bscal);
}
alias safeOp = checkedint.safeOp!(IFP.noex);

alias to(T) = checkedint.to!(T, IFP.noex);

Select!(isSigned!(BasicScalar!N), ptrdiff_t, size_t) idx(N)(const N num) nothrow @nogc
    if (isScalarType!N || isCheckedInt!N)
{
    return checkedint.to!(typeof(return), IFP.noex)(num.bscal);
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
