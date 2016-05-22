/**
Templates to facilitate treating `checkedint.SmartInt` and `checkedint.SafeInt` like the built-in numeric types in
generic code.

Copyright: Copyright Thomas Stuart Bockman 2015
License: $(LINK2 http://www.boost.org/LICENSE_1_0.txt, Boost License 1.0).
Authors: Thomas Stuart Bockman

This module wraps various templates from `std.traits` to make them `checkedint`-aware. For example,
`std.traits.isSigned!(SmartInt!int)` is `false`, but `checkedint.traits.isSigned!(SmartInt!int)` is `true`.

This module is separate from `checkedint` because it is only useful in generic code, and its symbols (deliberately)
conflict with some from `std.traits`.
*/
module checkedint.traits;
public import checkedint :
    isSafeInt,
    isSmartInt,
    isCheckedInt,
    hasBitOps,
    intFlagPolicyOf,
    BasicScalar;

private template isEx(alias Predicate) {
    template isEx(T) {
        static if(isCheckedInt!T)
            enum isEx = Predicate!(BasicScalar!T);
        else
            enum isEx = Predicate!T;
    }
}
public import future.traits :
    isBasicScalar   = isScalarType,
    isBasicNum      = isNumeric,
    isFloatingPoint,
    isBasicFixed    = isFixedPoint,
    isBasicInt      = isIntegral,
    isSomeChar,
    isBoolean,
    isBasicSigned   = isSigned,
    isBasicUnsigned = isUnsigned;
alias
    isScalarType    = isEx!isBasicScalar,
    isNumeric       = isEx!isBasicNum,
    isFixedPoint    = isEx!isBasicFixed,
    isIntegral      = isEx!isBasicInt,
    isSigned        = isEx!isBasicSigned,
    isUnsigned      = isEx!isBasicUnsigned;

template mostNegative(T)
    if(isFixedPoint!T)
{
    static if(isFloatingPoint!T)
        enum mostNegative = -T.max;
    else
        enum mostNegative = T.min;
}

private template TransEx(alias TypeTransform) {
    template TransEx(T) {
        static if(isCheckedInt!T) {
            alias TTB = TypeTransform!(CopyTypeQualifiers!(T, BasicScalar!T));
            alias CheckedInt = Select!(isSmartInt!T, SmartInt, SafeInt);
            alias TransEx = CopyTypeQualifiers!(TTB, CheckedInt!(TTB, TemplateArgsOf!T[1]));
        } else
            alias TransEx = TypeTransform!T;
    }
}
import future.traits :
    BasicSigned = Signed,
    BasicUnsigned = Unsigned,
    BasicPromoted = Promoted;
alias Signed = TransEx!BasicSigned;
alias Unsigned = TransEx!BasicUnsigned;
public import future.traits : IntFromChar;
alias Promoted = TransEx!BasicPromoted;
