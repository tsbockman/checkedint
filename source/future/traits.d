/**
Copyright: Copyright Thomas Stuart Bockman 2015
License: <a href="http://www.boost.org/LICENSE_1_0.txt">Boost License 1.0</a>.
Authors: Thomas Stuart Bockman
*/

module future.traits;

public import std.traits;
static if(__VERSION__ < 2068)
    alias CopyTypeQualifiers(From, To) = To; // HACK!
else {
    version(GNU) { static assert(false); }
}

enum isUnqual(T) = is(T == Unqual!T);
enum isFixedPoint(T) = isIntegral!T || isSomeChar!T || isBoolean!T;

template IntFromChar(N)
    if(isSomeChar!N)
{
    static if(N.sizeof == char.sizeof)
        alias IntFromChar = ubyte;
    else
    static if(N.sizeof == wchar.sizeof)
        alias IntFromChar = ushort;
    else
    static if(N.sizeof == dchar.sizeof)
        alias IntFromChar = uint;
    else
        static assert(false);
}
template IntFromChar(N)
    if(isIntegral!N)
{
    alias IntFromChar = Unqual!N;
}
template Promoted(N)
    if(isScalarType!N)
{
    alias Promoted = CopyTypeQualifiers!(N, typeof(N.init + N.init));
}

alias CallType(alias callable, ArgTypes...) = typeof(function() {
        import std.typecons : Tuple;
        return callable(Tuple!(ArgTypes)().expand);
    }());
alias OpType(string op, T) = typeof(function() {
        T t;
        return mixin(op ~ "t");
    }());
alias OpType(T, string op, V) = typeof(function() {
        T t;
        V v = 1; // Prevent "divide by zero" errors at CTFE
        return mixin("t " ~ op ~ " v");
    }());

template precision(N)
    if(isScalarType!N)
{
    import future.bitop : bsr;
    static if(isFloatingPoint!N)
        enum int precision = N.mant_dig;
    else static if(isSomeChar!N)
        enum int precision = N.sizeof * 8; // dchar may hold values greater than dchar.max
    else
        enum int precision = bsr(N.max) + 1;
}
