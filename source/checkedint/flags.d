/**
Common error signaling facilities for the `checkedint` package.

Copyright: Copyright Thomas Stuart Bockman 2015
License: $(LINK2 http://www.boost.org/LICENSE_1_0.txt, Boost License 1.0).
Authors: Thomas Stuart Bockman

$(BIG $(B `Yes.throws`)) $(BR)
When the `Yes.throws` is set, errors are signalled by simply throwing a new `CheckedIntException`. This is the default
method because:
$(UL
    $(LI The API user is not required to explicitly handle errors.)
    $(LI Printing a precise stack trace is very helpful for debugging.)
)
However, this approach is not suitable in all cases. In particular:
$(UL
    $(LI Obviously, it will not work in `nothrow` code.)
    $(LI As of $(B D 2.070), exceptions are still not safe to use in `@nogc` code.)
    $(LI Exceptions are too slow for code that is expected to signal many integer math errors in $(B normal) operation.)
)
$(BIG $(B `No.throws`)) $(BR)
An alternative error signalling method may be selected using the `No.throws` option:
$(OL
    $(LI Whenever an integer math error occurs, a bit flag is raised in `IntFlags.local`, which is a TLS variable.)
    $(LI The integer math operations in `checkedint` only set bit flags; they never clear them. Thus, any flag that is
    raised because of an error will remain set until handled by the API user.)
    $(LI The API user periodically checks whether any flags have been raised like so: `if (IntFlags.local)`)
    $(LI `IntFlags.local` may be inspected to determine the general cause of the error - for example, "divide by zero".)
    $(LI Once the API user has handled the error somehow, `IntFlags.clear()` can be used to unset all bit flags before
    continuing the program.)
)
The `IntFlags.pushPop` mixin can be used to prevent a function from handling or clearing flags that were set by the
caller.

Care must be taken when using `No.throws` to insert sufficient `if (IntFlags.local)` checks; otherwise `checkedint` will
not provide much protection from integer math related bugs.
*/
module checkedint.flags;

import future.bitop, std.algorithm, std.array, std.format, std.range/+.primitives+/, std.typecons;

@safe:

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
    IntFlags.local = outerIntFlags;
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

template raise(Flag!"throws" throws) {
    void raise(IntFlag flag) {
        static if(throws) {
            version (DigitalMars)
                pragma(inline, false); // DMD usually won't inline the caller without this.

            throw new CheckedIntException(flag);
        } else {
            /+pragma(inline, true);+/
            IntFlags.local |= flag;
        }
    }
    void raise(IntFlags flags) {
        static if(throws) {
            version (DigitalMars)
                pragma(inline, false); // DMD usually won't inline the caller without this.

            if(flags.anySet)
                throw new CheckedIntException(flags);
        } else {
            /+pragma(inline, true);+/
            IntFlags.local |= flags;
        }
    }
}
