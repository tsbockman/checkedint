/**
Copyright: Copyright Thomas Stuart Bockman 2015
License: $(LINK2 http://www.boost.org/LICENSE_1_0.txt, Boost License 1.0).
Authors: Thomas Stuart Bockman
*/
module checkedint.noex;

import future.traits, std.typecons;

@safe: /+pragma(inline, true):+/

static import checkedint.flags;
public import checkedint.flags :
    IntFlag,
    IntFlags,
    CheckedIntException;

alias raise = checkedint.flags.raise!(No.throws);

static import checkedint;

alias SmartInt(N, Flag!"bitOps" bitOps = Yes.bitOps) = checkedint.SmartInt!(N, No.throws, bitOps);
SmartInt!(N, bitOps) smartInt(Flag!"bitOps" bitOps = Yes.bitOps, N)(N num)
    if(isIntegral!N || isCheckedInt!N)
{
    return typeof(return)(num.bscal);
}
alias smartOp = checkedint.smartOp!(No.throws);

alias DebugInt(N, Flag!"bitOps" bitOps = Yes.bitOps) = checkedint.DebugInt!(N, No.throws, bitOps);

alias SafeInt(N, Flag!"bitOps" bitOps = Yes.bitOps) = checkedint.SafeInt!(N, No.throws, bitOps);
SafeInt!(N, bitOps) safeInt(Flag!"bitOps" bitOps = Yes.bitOps, N)(N num)
    if(isIntegral!N || isCheckedInt!N)
{
    return typeof(return)(num.bscal);
}
alias safeOp = checkedint.safeOp!(No.throws);

alias to(T) = checkedint.to!(T, No.throws);

public import checkedint :
    bscal,
    bits,
    idx,
    isSafeInt,
    isSmartInt,
    isCheckedInt,
    hasBitOps,
    isThrowingCInt,
    BasicScalar;
