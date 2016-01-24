/**
Copyright: Copyright Thomas Stuart Bockman 2015
License: <a href="http://www.boost.org/LICENSE_1_0.txt">Boost License 1.0</a>.
Authors: Thomas Stuart Bockman
*/

module future.format;
public import std.format;

static if(__VERSION__ < 2068) {
    string format(Char, Args...)(in Char[] fmt, Args args) {
        import std.array : appender;
        import std.format : formattedWrite;

        auto writer = appender!string();
        formattedWrite(writer, fmt, args);
        return writer.data.idup;
    }
} else {
    version(GNU) { static assert(false); }
}
