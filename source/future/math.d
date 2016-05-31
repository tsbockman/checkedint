/**
Compatibility shim to allow code written against the latest `std.math`
module to compile with older versions of D.

Copyright: Copyright Thomas Stuart Bockman 2016
License: $(LINK2 http://www.boost.org/LICENSE_1_0.txt, Boost License 1.0).
Authors: Thomas Stuart Bockman
**/
module future.math;
public import std.math;

static if(__VERSION__ >= 2067) {
    version(GNU) { static assert(false); }
} else {
    import std.traits;

    int cmp(T)(const(T) x, const(T) y) @nogc @safe pure nothrow
        if(isFloatingPoint!T)
    {
        if(x < y)
            return -1;
        if(y < x)
            return  1;
        const eq = (x == y);
        if(eq && x != 0)
            return  0;

        int sgnX = (-signbit(x) | 1) << isNaN(x);
        int sgnY = (-signbit(y) | 1) << isNaN(y);
        if(sgnX < sgnY)
            return -1;
        if(sgnY < sgnX)
            return  1;
        if(eq)
            return  0;

        const pldX = getNaNPayload(x);
        const pldY = getNaNPayload(y);
        if(pldX < pldY)
            return -sgnX;
        if(pldY < pldX)
            return  sgnX;
        return 0;
    }
}
