/**
Compatibility shim to allow code written against the latest `std.traits`
module to compile with older versions of D.

Copyright: Copyright Thomas Stuart Bockman 2015
License: $(LINK2 http://www.boost.org/LICENSE_1_0.txt, Boost License 1.0).
Authors: Thomas Stuart Bockman
**/

/* HACK: Added '0' to the end of the name to preventdub build -b docs
         from overwriting the output of checkedint.traits */
module future.traits0; 

public import std.traits;

enum isUnqual(T) = is(T == Unqual!T);
enum isFixedPoint(T) = isIntegral!T || isSomeChar!T || isBoolean!T;

template IntFromChar(N)
    if (isSomeChar!N)
{
    static if (N.sizeof == char.sizeof)
        alias IntFromChar = ubyte;
    else
    static if (N.sizeof == wchar.sizeof)
        alias IntFromChar = ushort;
    else
    static if (N.sizeof == dchar.sizeof)
        alias IntFromChar = uint;
    else
        static assert(false);
}
template IntFromChar(N)
    if (isIntegral!N)
{
    alias IntFromChar = Unqual!N;
}
template Promoted(N)
    if (isScalarType!N)
{
    alias Promoted = CopyTypeQualifiers!(N, typeof(N.init + N.init));
}

alias CallType(alias callable, ArgTypes...) = typeof(function()
    {
        import std.typecons : Tuple;
        return callable(Tuple!(ArgTypes)().expand);
    }());
alias OpType(string op, T) = typeof(function()
    {
        T t;
        return mixin(op ~ "t");
    }());
alias OpType(T, string op, V) = typeof(function()
    {
        T t;
        V v = 1; // Prevent "divide by zero" errors at CTFE
        return mixin("t " ~ op ~ " v");
    }());

template precision(N)
    if (isScalarType!N)
{
    import future.bitop : bsr;
    static if (isFloatingPoint!N)
        enum int precision = N.mant_dig;
    else static if (isSomeChar!N)
        enum int precision = N.sizeof * 8; // dchar may hold values greater than dchar.max
    else
        enum int precision = bsr(N.max) + 1;
}
