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

/**
Function used to signal a failure and its proximate cause from integer math code. Depending on the value of the `throws`
parameter, `raise()` will either:
$(UL
    $(LI Throw a `CheckedIntException`, or)
    $(LI Set a bit in `IntFlags.local` that can be checked by the caller later.)
)
*/
template raise(Flag!"throws" throws) {
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
}
///
unittest {
    import checkedint.throws; // set Yes.throws

    bool caught = false;
    try {
        raise(IntFlag.div0);
    } catch(CheckedIntException e) {
        caught = (e.intFlags == IntFlag.div0);
    }
    assert(caught);
}
///
unittest {
    import checkedint.noex; // set No.throws

    raise(IntFlag.div0);
    raise(IntFlag.posOver);

    assert(IntFlags.local == (IntFlag.div0 | IntFlag.posOver));

    IntFlags.local.clear();
}
///
unittest {
    // Both signaling strategies may be usefully mixed within the same program:
    static void fails() nothrow {
        raise!(No.throws)(IntFlag.negOver);
        raise!(No.throws)(IntFlag.imag);
    }

    bool caught = false;
    try {
        fails();
        // Flags that were raised by `nothrow` code can easily be turned into an exception by the caller.
        raise!(Yes.throws)(IntFlags.local.clear());
    } catch(CheckedIntException e) {
        caught = (e.intFlags == (IntFlag.negOver | IntFlag.imag));
    }
    assert(caught);
}

/// Represents a single cause of failure for an integer math operation.
struct IntFlag {
/+pragma(inline, true):+/
private:
    uint index;
    this(uint index) pure nothrow @nogc {
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

/// The result of the operation is undefined mathematically, by the API, or both.
        enum IntFlag undef   = 1;
/// A division by zero was attempted.
        enum IntFlag div0    = 2;
/// The result is imaginary, and as such not representable by an integral type.
        enum IntFlag imag    = 3;
/// Overflow occured.
        enum IntFlag over    = 4;
/// Overflow occured because a value was too large.
        enum IntFlag posOver = 5;
/// Overflow occured because a value was too negative.
        enum IntFlag negOver = 6;
    } else {
        static @property pure nothrow @nogc {
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

/// `false` if this `IntFlag` is set to one of the error signals listed above. Otherwise `true`.
    @property bool isNull() const pure nothrow @nogc {
        return index == 0; }
    ///
    unittest {
        assert( IntFlag.init.isNull);
        assert(!IntFlag.div0.isNull);
    }

/// An `IntFlag` value is implicitly convertible to an `IntFlags` with only the one flag raised.
    @property IntFlags mask() const pure nothrow @nogc {
        return IntFlags(1u << index); }
/// ditto
    alias mask this;
    ///
    unittest {
        IntFlags flags = IntFlag.over;
        assert(flags == IntFlag.over);
    }

/// Get a description of this error flag.
    @property string desc() const pure nothrow @nogc {
        return strs[index][1 .. ($ - 1)]; }
    ///
    unittest {
        assert(IntFlag.over.desc == "overflow");
        assert(IntFlag.init.desc == "NULL");
    }

/// Get a string representation of this `IntFlag`. The format is the same as that returned by `IntFlags.toString()`.
    void toString(Writer, Char)(Writer sink, FormatSpec!Char fmt = (FormatSpec!Char).init) const @trusted pure nothrow @nogc {
        formatValue(sink, strs[index], fmt); }
/// ditto
    string toString() const pure nothrow @nogc {
        return strs[index]; }
    ///
    unittest {
        assert(IntFlag.over.toString() == "{overflow}");
        assert(IntFlag.over.toString() == IntFlag.over.mask.toString());
    }
}

/**
A bitset that can be used to track integer math failures.

`IntFlags` is also a forward range which can be used to iterate over the set (raised) `IntFlag` values. Fully consuming
the range is equivalent to calling `clear()`; iterate over a copy made with `save()`, instead, if this is not your
intention.
*/
struct IntFlags {
/+pragma(inline, true):+/
private:
    uint bits = 0;
    this(uint bits) pure nothrow @nogc {
        this.bits = bits;
    }

public:
/**
Assign the set of flags represented by `that` to this `IntFlags`. Note that `IntFlag` values are accepted also,
because `IntFlag` is implicitly convertible to `IntFlags`.
*/
    this(IntFlags that) pure nothrow @nogc {
        bits = that.bits; }
    ref IntFlags opAssign(IntFlags that) pure nothrow @nogc {
        bits = that.bits;
        return this;
    }
    ///
    unittest {
        IntFlags flags = IntFlag.div0;
        assert(flags == IntFlag.div0);
        flags = IntFlag.negOver | IntFlag.imag;
        assert(flags == (IntFlag.negOver | IntFlag.imag));

        IntFlags.local = flags;
        assert(IntFlags.local == (IntFlag.negOver | IntFlag.imag));

        IntFlags.local.clear();
    }

/**
Clear all flags, and return the set of flags that were previously set.

`raise!(Yes.throws)(IntFlags.local.clear())` is a convenient way that the caller of a `nothrow` function can
*/
    IntFlags clear() pure nothrow @nogc {
        IntFlags ret = this;
        bits = 0;
        return ret;
    }
    ///
    unittest {
        IntFlags.local = IntFlag.posOver | IntFlag.negOver;
        assert(IntFlags.local.clear() == (IntFlag.posOver | IntFlag.negOver));
        assert(!IntFlags.local);
    }

/// Test (`&`), set (`|`), or unset (`-`) individual flags.
    IntFlags opBinary(string op)(IntFlags that) const pure nothrow @nogc
        if(op.among!("&", "|", "-"))
    {
        IntFlags ret = this;
        return ret.opOpAssign!op(that);
    }
/// ditto
    ref IntFlags opOpAssign(string op)(IntFlags that) pure nothrow @nogc
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
    ///
    unittest {
        IntFlags flags = IntFlag.undef | IntFlag.posOver | IntFlag.negOver;

        flags &= IntFlag.posOver | IntFlag.negOver;
        assert(!(flags & IntFlag.undef));

        flags -= IntFlag.undef | IntFlag.negOver;
        assert(  flags & IntFlag.posOver);
        assert(!(flags & IntFlag.negOver));
    }

/**
`true` if any non-null flag is set, otherwise `false`.

An `IntFlags` value is implicitly convertible to `bool` through `anySet`.
*/
    @property bool anySet() const pure nothrow @nogc {
        return bits > 1; }
/// ditto
    alias anySet this;
    ///
    unittest {
        IntFlags flags;
        assert(!flags);
        flags = IntFlag.imag | IntFlag.undef;
        assert( flags);
    }

/// `true` if no non-null flags are set.
    @property bool empty() const pure nothrow @nogc {
        return bits <= 1; }
/// Get the first set `IntFlag`.
    @property IntFlag front() const pure nothrow @nogc {
        // bsr() is undefined for 0.
        return IntFlag(bsr(bits | 1));
    }
/// Clear the first set `IntFlag`. This is equivalent to `flags -= flags.front`.
    ref IntFlags popFront() pure nothrow @nogc {
        // bsr() is undefined for 0.
        bits &= ~(1u << bsr(bits | 1));
        return this;
    }
/// Get a mutable copy of this `IntFlags` value, so as not to `clear()` the original by iterating through it.
    @property IntFlags save() const pure nothrow @nogc {
        return this; }
/// Get the number of raised flags.
    @property uint length() const pure nothrow @nogc {
        return popcnt(bits & ~1); }

    unittest {
        import std.range : isForwardRange, hasLength;
        static assert(isForwardRange!IntFlags);
        static assert(hasLength!IntFlags);
    }

/// The standard `IntFlags` set for the current thread. `raise!(No.throws)()` mutates this variable.
    static IntFlags local;

/**
A `mixin` string that may be used to (effectively) push a new `IntFlags.local` variable onto the stack at the
beginning of a scope, and restore the previous one at the end.

Any flags raised during the scope must be manually checked, handled, and cleared before the end, otherwise a debugging
`assert` will be triggered to warn you that restoring the old `IntFlags.local` value would cause a loss of information.
*/
    enum string pushPop = r"
IntFlags outerIntFlags = IntFlags.local.clear();
scope(exit) {
    assert(IntFlags.local.empty);
    IntFlags.local = outerIntFlags;
}";
    ///
    unittest {
        import checkedint.noex; // set No.throws

        string[] log;

        void onlyZero(int x) {
            mixin(IntFlags.pushPop);

            if(x < 0)
                raise(IntFlag.negOver);
            if(x > 0)
                raise(IntFlag.posOver);

            if(IntFlags.local)
                log ~= IntFlags.local.clear().toString();
        }

        IntFlags.local = IntFlag.imag;
        onlyZero(-50);
        onlyZero(22);
        onlyZero(0);
        assert(IntFlags.local == IntFlag.imag);
        import std.conv;
        assert(log == ["{negative overflow}", "{positive overflow}"]);
    }

/+pragma(inline):+/
/// Get a string representation of the list of set flags.
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
/// ditto
    void toString(Writer)(Writer sink) const {
        toString(sink, (FormatSpec!char).init); }
/// ditto
    string toString() const pure {
        switch(length) {
        case 0:
            return "{}";
        case 1:
            return front.toString();
        default:
            auto buff = appender!string();
            toString(buff);
            return cast(immutable)(buff.data);
        }
    }
    ///
    unittest {
        IntFlags flags;
        assert(flags.toString() == "{}");

        flags = IntFlag.undef;
        assert((flags.toString() == "{undefined result}") && (flags.toString() == IntFlag.undef.toString()));

        flags |= IntFlag.imag;
        assert(flags.toString() == "{imaginary component, undefined result}", flags.toString());
    }
}

/**
An `Exception` representing the cause of an integer math failure.

A new instances may be created and thrown using `raise!(Yes.throws)()`.
*/
class CheckedIntException : Exception {
    /// An `IntFlags` bitset indicating the proximate cause(s) of the exception.
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
