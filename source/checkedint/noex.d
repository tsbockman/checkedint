module checkedint.noex;

import future.traits, std.typecons;

@safe: nothrow: /+pragma(inline, true):+/

static import checkedint.flags;
public import checkedint.flags :
    IntFlag,
    IntFlags;

alias raise = checkedint.flags.raise!(No.throws);

static import checkedint;
public import checkedint :
    isSafeInt,
    isSmartInt,
    isCheckedInt,
    hasBitOps,
    isThrowingCInt,
    BasicScalar;

alias to(T) = checkedint.to!(T, No.throws);

public import checkedint :
    bscal,
    bits,
    idx;

alias safeOp = checkedint.safeOp!(No.throws);
alias smartOp = checkedint.smartOp!(No.throws);

alias SafeInt(N, Flag!"bitOps" bitOps = Yes.bitOps) = checkedint.SafeInt!(N, No.throws, bitOps);
alias SmartInt(N, Flag!"bitOps" bitOps = Yes.bitOps) = checkedint.SmartInt!(N, No.throws, bitOps);
alias DebugInt(N, Flag!"bitOps" bitOps = Yes.bitOps) = checkedint.DebugInt!(N, No.throws, bitOps);
