/**
Copyright: Copyright Thomas Stuart Bockman 2015
License: <a href="http://www.boost.org/LICENSE_1_0.txt">Boost License 1.0</a>.
Authors: Thomas Stuart Bockman
*/

module future.math;
public import std.math;

static if(__VERSION__ >= 2069) {
    version(GNU) { static assert(false); }
} else {
    int cmp(const real x, const real y) @safe pure nothrow @nogc {
        if(x < y)
            return -1;
        if(x > y)
            return 1;

        const sx = signbit(x);
        const sy = signbit(y);

        if(x.isNaN) {
            if(!y.isNaN)
                return sx? -1 : 1;
        } else
        if(y.isNaN)
            return sy? 1 : -1;

        return (sx < sy)? -1 : (sx > sy);
    }
}
