module checkedint.throws;
public import checkedint.flags;

import future.traits, std.typecons;

@safe: /+pragma(inline, true):+/

static import checkedint.flags;
public import checkedint.flags :
    IntFlag,
    IntFlags,
    CheckedIntException;

alias raise = checkedint.flags.raise!(Yes.throws);

static import checkedint;
public import checkedint :
    isSafeInt,
    isSmartInt,
    isCheckedInt,
    hasBitOps,
    isThrowingCInt,
    BasicScalar;

T to(T, S)(S value) {
    static if(isScalarType!(BasicScalar!T) && isScalarType!(BasicScalar!S))
        return chcekedint.to!(T, Yes.throws, S)(value);
    else {
        import std.conv : stdTo = to;
        return stdTo!T(value);
    }
}

public import checkedint :
    bscal,
    bits,
    idx;

alias safeOp = checkedint.safeOp!(Yes.throws);
alias smartOp = checkedint.smartOp!(Yes.throws);

alias SafeInt(N, Flag!"bitOps" bitOps = Yes.bitOps) = checkedint.SafeInt!(N, Yes.throws, bitOps);
alias SmartInt(N, Flag!"bitOps" bitOps = Yes.bitOps) = checkedint.SmartInt!(N, Yes.throws, bitOps);
alias DebugInt(N, Flag!"bitOps" bitOps = Yes.bitOps) = checkedint.DebugInt!(N, Yes.throws, bitOps);
