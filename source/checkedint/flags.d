/**
Copyright: Copyright Thomas Stuart Bockman 2015
License: <a href="http://www.boost.org/LICENSE_1_0.txt">Boost License 1.0</a>.
Authors: Thomas Stuart Bockman
*/

module checkedint.flags;

import core.bitop, std.algorithm, std.array, std.format, std.range/+.primitives+/;

@safe:

// flags
struct IntFlag {
pure: nothrow: @nogc: /+pragma(inline, true):+/
private:
    uint index;
    this(uint index) {
        assert(index < strs.length);
        this.index = index;
    }

    private static immutable strs = [
        "{NULL}",
        "{undefined result}",
        "{divide by zero}",
        "{imaginary component}",
        "{overflow}",
        "{positive overflow}",
        "{negative overflow}"
    ];
public:
    static if(__VERSION__ >= 2067) {
        version(GNU) { static assert(false); }
        enum {
            undef   = IntFlag(1),
            div0    = IntFlag(2),
            imag    = IntFlag(3),
            over    = IntFlag(4),
            posOver = IntFlag(5),
            negOver = IntFlag(6)
        }
    } else {
        static @property {
            auto undef() {
                return IntFlag(1); }
            auto div0() {
                return IntFlag(2); }
            auto imag() {
                return IntFlag(3); }
            auto over() {
                return IntFlag(4); }
            auto posOver() {
                return IntFlag(5); }
            auto negOver() {
                return IntFlag(6); }
        }
    }

    @property {
        bool isNull() const {
            return index == 0; }
        IntFlags mask() const {
            return IntFlags(1u << index); }
        alias mask this;

        string desc() const {
            return strs[index][1 .. ($ - 1)]; }
    }
    void toString(Writer, Char)(Writer sink, FormatSpec!Char fmt = (FormatSpec!Char).init) const @trusted {
        formatValue(sink, strs[index], fmt); }
    string toString() const {
        return strs[index]; }
}

struct IntFlags {
    pure nothrow @nogc /+pragma(inline, true)+/ {
    private:
        uint bits = 0;
        this(uint bits) {
            this.bits = bits;
        }

    public:
        this(IntFlags that) {
            bits = that.bits; }
        ref IntFlags opAssign(IntFlags that) {
            bits = that.bits;
            return this;
        }
        void clear() {
            bits = 0; }

        IntFlags opBinary(string op)(IntFlags that) const
            if(op.among!("&", "|", "-"))
        {
            IntFlags ret = this;
            return ret.opOpAssign!op(that);
        }
        ref IntFlags opOpAssign(string op)(IntFlags that)
            if(op.among!("&", "|", "-"))
        {
            static if(op == "&")
                bits &= that.bits;
            else
            static if(op == "|")
                bits |= that.bits;
            else
            static if(op == "-")
                bits &= ~(that.bits);

            return this;
        }

        @property bool anySet() const {
            return bits > 1; }
        alias anySet this;

        @property bool empty() const {
            return bits <= 1; }
        @property IntFlag front() const {
            // bsr() is undefined for 0.
            return IntFlag(bsr(bits | 1));
        }
        ref IntFlags popFront() {
            // bsr() is undefined for 0.
            bits &= ~(1u << bsr(bits | 1));
            return this;
        }
        @property IntFlags save() const {
            return this; }
        @property uint length() const {
            return popcnt(bits); }

        unittest {
            import std.range : isForwardRange, hasLength;
            static assert(isForwardRange!IntFlags);
            static assert(hasLength!IntFlags);
        }

        static IntFlags local;
        enum string pushPop = r"
IntFlags outerIntFlags = IntFlags.local;
scope(exit) {
    assert(IntFlags.local.empty);
    IntFlags.local = outer;
}";
    }
    public {
        void toString(Writer, Char)(Writer sink, FormatSpec!Char fmt) const @trusted {
            put(sink, '{');

            bool first = true;
            foreach(fd; this.save()) {
                if(first)
                    first = false;
                else
                    put(sink, ", ");
                put(sink, fd.desc);
            }

            put(sink, '}');
        }
        void toString(Writer)(Writer sink) const {
            toString(sink, (FormatSpec!char).init); }
        string toString() const {
            if(length == 1)
                return front.toString();
            else {
                auto buff = appender!string();
                toString(buff);
                return cast(immutable)(buff.data);
            }
        }
    }
}

class CheckedIntException : Exception {
    const IntFlags intFlags;

private:
    enum msg0 = "Integer math exception(s): ";
    private this(IntFlag flag, string fn = __FILE__, size_t ln = __LINE__) pure nothrow {
        intFlags = flag;
        super(msg0 ~ flag.toString(), fn, ln);
    }
    private this(IntFlags flags, string fn = __FILE__, size_t ln = __LINE__) pure nothrow {
        intFlags = flags;

        auto buff = appender(msg0);
        flags.toString(buff);

        super(cast(immutable)(buff.data), fn, ln);
    }
}

/+pragma(inline, false) {+/
    /* The throwing versions of raise() must not be inlined, as doing so tends to
       prevent the caller from being inlined, at least on DMD. */

    void raise(bool throws)(IntFlag flag)
        if(throws)
    {
        throw new CheckedIntException(flag);
    }
    void raise(bool throws)(IntFlags flags)
        if(throws)
    {
        if(flags.anySet)
            throw new CheckedIntException(flags);
    }
/+}
pragma(inline, true) {+/
    void raise(bool throws)(IntFlag flag)
        if(!throws)
    {
        IntFlags.local |= flag;
    }
    void raise(IntFlag flag) {
        raise!true(flag); }

    void raise(bool throws = true)(IntFlags flags)
        if(!throws)
    {
        IntFlags.local |= flags;
    }
    void raise(IntFlags flags) {
        raise!true(flags); }
/+}+/
