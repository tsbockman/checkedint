/**
Copyright: Copyright Thomas Stuart Bockman 2015
License: <a href="http://www.boost.org/LICENSE_1_0.txt">Boost License 1.0</a>.
Authors: Thomas Stuart Bockman
*/

module checkedint.noex.smartop;
import checkedint.internal;
public import checkedint.flags;

import std.algorithm, future.traits;

@safe: /+pragma(inline, true):+/

public import checkedint.smartop : cmp;

N unary(string op, bool throws, N)(const N num)
    if(isIntegral!N && op == "~")
{
    import checkedint.smartop : impl = unary;
    return impl!(op, throws)(num);
}
N unary(string op, N)(const N num) nothrow @nogc
    if(isIntegral!N && op == "~")
{
    import checkedint.smartop : impl = unary;
    return impl!(op, false)(num);
}
IntFromChar!N unary(string op, bool throws, N)(const N num)
    if(isSomeChar!N && op == "~")
{
    import checkedint.smartop : impl = unary;
    return impl!(op, throws)(num);
}
IntFromChar!N unary(string op, N)(const N num) nothrow @nogc
    if(isSomeChar!N && op == "~")
{
    import checkedint.smartop : impl = unary;
    return impl!(op, false)(num);
}
Signed!(Promoted!N) unary(string op, bool throws, N)(const N num)
    if(isFixedPoint!N && op.among!("-", "+"))
{
    import checkedint.smartop : impl = unary;
    return impl!(op, throws)(num);
}
Signed!(Promoted!N) unary(string op, N)(const N num) nothrow @nogc
    if(isFixedPoint!N && op.among!("-", "+"))
{
    import checkedint.smartop : impl = unary;
    return impl!(op, false)(num);
}
/+ref+/ N unary(string op, bool throws, N)(/+return+/ ref N num)
    if(isIntegral!N && op.among!("++", "--"))
{
    import checkedint.smartop : impl = unary;
    return impl!(op, throws)(num);
}
/+ref+/ N unary(string op, N)(/+return+/ ref N num) nothrow @nogc
    if(isIntegral!N && op.among!("++", "--"))
{
    import checkedint.smartop : impl = unary;
    return impl!(op, false)(num);
}

public import checkedint.smartop : abs;

ubyte bsf(bool throws, N)(const N num)
    if(isFixedPoint!N)
{
    return cast(ubyte) bsfImpl!throws(num);
}
ubyte bsf(N)(const N num) nothrow @nogc
    if(isFixedPoint!N)
{
    return bsf!false(num);
}
ubyte bsr(bool throws, N)(const N num)
    if(isFixedPoint!N)
{
    return cast(ubyte) bsrImpl!throws(num);
}
ubyte bsr(N)(const N num) nothrow @nogc
    if(isFixedPoint!N)
{
    return bsr!false(num);
}

ubyte ilogb(bool throws, N)(const N num)
    if(isFixedPoint!N)
{
    import checkedint.smartop : impl = ilogb;
    return impl!throws(abs(num));
}
ubyte ilogb(N)(const N num) nothrow @nogc
    if(isFixedPoint!N)
{
    import checkedint.smartop : impl = ilogb;
    return ilogb!false(num);
}

auto binary(string op, bool throws, N, M)(const N left, const M right)
    if(isFixedPoint!N && isFixedPoint!M)
{
    import checkedint.smartop : impl = binary;
    return impl!(op, throws)(left, right);
}
auto binary(string op, N, M)(const N left, const M right) nothrow @nogc
    if(isFixedPoint!N && isFixedPoint!M)
{
    import checkedint.smartop : impl = binary;
    return impl!(op, false)(left, right);
}
/+ref+/ N binary(string op, bool throws, N, M)(/+return+/ ref N left, const M right)
    if(isIntegral!N && isFixedPoint!M && (op[$ - 1] == '='))
{
    import checkedint.smartop : impl = binary;
    return impl!(op, throws)(left, right);
}
/+ref+/ N binary(string op, N, M)(/+return+/ ref N left, const M right) nothrow @nogc
    if(isIntegral!N && isFixedPoint!M && (op[$ - 1] == '='))
{
    import checkedint.smartop : impl = binary;
    return impl!(op, false)(left, right);
}

auto mulPow2(N, M)(const N left, const M exp) pure nothrow @nogc
    if((isFloatingPoint!N && isScalarType!M) || (isScalarType!N && isFloatingPoint!M))
{
    import checkedint.smartop : impl = mulPow2;
    return impl(left, exp);
}
auto mulPow2(bool throws, N, M)(const N left, const M exp)
    if(isFixedPoint!N && isFixedPoint!M)
{
    import checkedint.smartop : impl = mulPow2;
    return impl!throws(left, exp);
}
auto mulPow2(N, M)(const N left, const M exp) nothrow @nogc
    if(isFixedPoint!N && isFixedPoint!M)
{
    import checkedint.smartop : impl = mulPow2;
    return impl!false(left, exp);
}
auto divPow2(N, M)(const N left, const M exp) pure nothrow @nogc
    if((isFloatingPoint!N && isScalarType!M) || (isScalarType!N && isFloatingPoint!M))
{
    import checkedint.smartop : impl = divPow2;
    return impl(left, exp);
}
auto divPow2(bool throws, N, M)(const N left, const M exp)
    if(isFixedPoint!N && isFixedPoint!M)
{
    import checkedint.smartop : impl = divPow2;
    return impl!throws(left, exp);
}
auto divPow2(N, M)(const N left, const M exp) nothrow @nogc
    if(isFixedPoint!N && isFixedPoint!M)
{
    import checkedint.smartop : impl = divPow2;
    return impl!false(left, exp);
}
auto modPow2(N, M)(const N left, const M exp) pure nothrow @nogc
    if((isFloatingPoint!N && isScalarType!M) || (isScalarType!N && isFloatingPoint!M))
{
    import checkedint.smartop : impl = modPow2;
    return impl(left, exp);
}
auto modPow2(N, M)(const N left, const M exp) pure nothrow @nogc
    if(isFixedPoint!N && isFixedPoint!M)
{
    import checkedint.smartop : impl = modPow2;
    return impl(left, exp);
}

auto pow(N, M)(const N base, const M exp) pure nothrow @nogc
    if((isFloatingPoint!N && isScalarType!M) || (isScalarType!N && isFloatingPoint!M))
{
    import checkedint.smartop : impl = pow;
    return impl(base, exp);
}
auto pow(bool throws, N, M)(const N base, const M exp)
    if(isFixedPoint!N && isFixedPoint!M)
{
    import checkedint.smartop : impl = pow;
    return impl!throws(base, exp);
}
auto pow(N, M)(const N base, const M exp) nothrow @nogc
    if(isFixedPoint!N && isFixedPoint!M)
{
    import checkedint.smartop : impl = pow;
    return impl!false(base, exp);
}
