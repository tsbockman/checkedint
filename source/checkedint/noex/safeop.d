/**
Copyright: Copyright Thomas Stuart Bockman 2015
License: <a href="http://www.boost.org/LICENSE_1_0.txt">Boost License 1.0</a>.
Authors: Thomas Stuart Bockman
*/

module checkedint.noex.safeop;
import checkedint.internal;
public import checkedint.flags;

import std.algorithm, future.traits;

@safe: /+pragma(inline, true):+/

public import checkedint.safeop : cmp;

N unary(string op, bool throws, N)(const N num)
    if((isIntegral!N || isSomeChar!N) && op.among!("-", "+", "~"))
{
    import checkedint.safeop : impl = unary;
    return impl!(op, throws)(num);
}
N unary(string op, N)(const N num) nothrow @nogc
    if((isIntegral!N || isSomeChar!N) && op.among!("-", "+", "~"))
{
    import checkedint.safeop : impl = unary;
    return impl!(op, false)(num);
}
/+ref+/ N unary(string op, bool throws, N)(/+return+/ ref N num)
    if((isIntegral!N || isSomeChar!N) && op.among!("++", "--"))
{
    import checkedint.safeop : impl = unary;
    return impl!(op, throws)(num);
}
/+ref+/ N unary(string op, N)(/+return+/ ref N num) nothrow @nogc
    if((isIntegral!N || isSomeChar!N) && op.among("++", "--"))
{
    import checkedint.safeop : impl = unary;
    return impl!(op, false)(num);
}

N abs(bool throws, N)(const N num)
    if(isFixedPoint!N)
{
    import checkedint.safeop : impl = abs;
    return impl!throws(num);
}
N abs(N)(const N num) nothrow @nogc
    if(isFixedPoint!N)
{
    import checkedint.safeop : impl = abs;
    return impl!false(num);
}

int bsf(bool throws, N)(const N num)
    if(isFixedPoint!N)
{
    return bsfImpl!throws(num);
}
int bsf(N)(const N num) nothrow @nogc
    if(isFixedPoint!N)
{
    return bsfImpl!false(num);
}
int bsr(bool throws, N)(const N num)
    if(isFixedPoint!N)
{
    return bsrImpl!throws(num);
}
int bsr(N)(const N num) nothrow @nogc
    if(isFixedPoint!N)
{
    return bsrImpl!false(num);
}

int ilogb(bool throws, N)(const N num)
    if(isFixedPoint!N)
{
    import checkedint.safeop : impl = ilogb;
    return impl!throws(num);
}
int ilogb(N)(const N num) nothrow @nogc
    if(isFixedPoint!N)
{
    import checkedint.safeop : impl = ilogb;
    return impl!false(num);
}

OpType!(N, op, M) binary(string op, bool throws, N, M)(const N left, const M right)
    if(isFixedPoint!N && isFixedPoint!M && op.among!("+", "-", "*", "/", "%", "^^", "<<", ">>", ">>>", "&", "|", "^"))
{
    import checkedint.safeop : impl = binary;
    return impl!(op, throws)(left, right);
}
OpType!(N, op, M) binary(string op, N, M)(const N left, const M right) nothrow @nogc
    if(isFixedPoint!N && isFixedPoint!M && op.among!("+", "-", "*", "/", "%", "^^", "<<", ">>", ">>>", "&", "|", "^"))
{
    import checkedint.safeop : impl = binary;
    return impl!(op, false)(left, right);
}
/+ref+/ N binary(string op, bool throws, N, M)(/+return+/ ref N left, const M right)
    if((isIntegral!N || isSomeChar!N) && isFixedPoint!M && (op[$ - 1] == '='))
{
    import checkedint.safeop : impl = binary;
    return impl!(op, throws)(left, right);
}
/+ref+/ N binary(string op, N, M)(/+return+/ ref N left, const M right) nothrow @nogc
    if((isIntegral!N || isSomeChar!N) && isFixedPoint!M && (op[$ - 1] == '='))
{
    import checkedint.safeop : impl = binary;
    return impl!(op, false)(left, right);
}

auto mulPow2(N, M)(const N left, const M exp) pure nothrow @nogc
    if((isFloatingPoint!N && isScalarType!M) || (isScalarType!N && isFloatingPoint!M))
{
    import checkedint.safeop : impl = mulPow2;
    return impl(left, exp);
}
auto mulPow2(bool throws, N, M)(const N left, const M exp)
    if(isFixedPoint!N && isFixedPoint!M)
{
    import checkedint.safeop : impl = mulPow2;
    return impl!throws(left, exp);
}
auto mulPow2(N, M)(const N left, const M exp) nothrow @nogc
    if(isFixedPoint!N && isFixedPoint!M)
{
    import checkedint.safeop : impl = mulPow2;
    return impl!false(left, exp);
}
auto divPow2(N, M)(const N left, const M exp) pure nothrow @nogc
    if((isFloatingPoint!N && isScalarType!M) || (isScalarType!N && isFloatingPoint!M))
{
    import checkedint.safeop : impl = divPow2;
    return impl(left, exp);
}
auto divPow2(bool throws, N, M)(const N left, const M exp)
    if(isFixedPoint!N && isFixedPoint!M)
{
    import checkedint.safeop : impl = divPow2;
    return impl!throws(left, exp);
}
auto divPow2(N, M)(const N left, const M exp) nothrow @nogc
    if(isFixedPoint!N && isFixedPoint!M)
{
    import checkedint.safeop : impl = divPow2;
    return impl!false(left, exp);
}
auto modPow2(N, M)(const N left, const M exp) pure nothrow @nogc
    if((isFloatingPoint!N && isScalarType!M) || (isScalarType!N && isFloatingPoint!M))
{
    import checkedint.safeop : impl = modPow2;
    return impl(left, exp);
}
auto modPow2(N, M)(const N left, const M exp) pure nothrow @nogc
    if(isFixedPoint!N && isFixedPoint!M)
{
    import checkedint.safeop : impl = modPow2;
    return impl(left, exp);
}

CallType!(std.math.pow, N, M) pow(bool throws, N, M)(const N base, const M exp)
    if(isFixedPoint!N && isFixedPoint!M)
{
    import checkedint.safeop : impl = pow;
    return impl!throws(base, exp);
}
CallType!(std.math.pow, N, M) pow(N, M)(const N base, const M exp) nothrow @nogc
    if(isFixedPoint!N && isFixedPoint!M)
{
    import checkedint.safeop : impl = pow;
    return impl!false(base, exp);
}
