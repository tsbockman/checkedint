/**
Common error signaling facilities for the `checkedint` package.

Copyright: Copyright Thomas Stuart Bockman 2015
License: $(LINK2 http://www.boost.org/LICENSE_1_0.txt, Boost License 1.0).
Authors: Thomas Stuart Bockman

$(BIG $(B `IntFlagPolicy.throws`)) $(BR)
When the `throws` policy is set, errors are signalled by simply throwing a new `CheckedIntException`. This is the
recommended policy because:
$(UL
    $(LI The API user is not required to explicitly handle errors.)
    $(LI Printing a precise stack trace is very helpful for debugging.)
)
However, this approach is not suitable in all cases. In particular:
$(UL
    $(LI Obviously, it will not work in `nothrow` code.)
    $(LI As of $(B D 2.071), exceptions are still not safe to use in `@nogc` code.)
    $(LI Exceptions are too slow for code that is expected to signal many integer math errors in $(B normal) operation.)
)

$(BIG $(B `IntFlagPolicy.asserts`)) $(BR)
When the `asserts` policy is set, errors trigger an assertion failure. The result depends upon whether assertions were
enabled at compiler time:
$(UL
    $(LI With `version(assert)` - enabled by default in debug and unittest builds - a `core.exception.AssertError` will
    be thrown. Its `msg` property will be set to the description of an `IntFlag` that was raised.)
    $(LI Otherwise (in release mode), `assert(0);` will be used to halt the program immediately. Unfortunately, no
    message or stack trace can be provided in this case. Use one of the other two error signalling policies if you need
    detailed information in release mode.)
)
The `asserts` policy is the only one that is compatible with `pure nothrow @nogc` code.

$(BIG $(B `IntFlagPolicy.noex`)) $(BR)
An alternative error signalling method may be selected using the `noex` policy:
$(OL
    $(LI Whenever an integer math error occurs, a bit flag is raised in `IntFlags.local`, which is a TLS variable.)
    $(LI The integer math operations in `checkedint` only set bit flags; they never clear them. Thus, any flag that is
    raised because of an error will remain set until handled by the API user.)
    $(LI The API user periodically checks whether any flags have been raised like so: `if (IntFlags.local)`)
    $(LI `IntFlags.local` may be inspected to determine the general type of the error - for example, "divide by zero".)
    $(LI Once the API user has handled the error somehow, `IntFlags.clear()` can be used to unset all bit flags before
    continuing the program.)
)
The `IntFlags.pushPop` mixin can be used to prevent a function from handling or clearing flags that were set by the
caller.

Care must be taken when using the `noex` policy to insert sufficient `if (IntFlags.local)` checks; otherwise
`checkedint` will not provide much protection from integer math related bugs.
*/
module checkedint.flags;

import future.bitop, std.algorithm, std.array, std.format, std.range/+.primitives+/;

@safe:

///
enum IntFlagPolicy {
    none = 0,
    noex = 1,
    asserts = 2,
    throws = 3
}
/// In mixed-policy `checkedint` operations, the higher ranking policy should be used.
unittest {
    assert(!IntFlagPolicy.none); // none == 0
    assert(IntFlagPolicy.noex > IntFlagPolicy.none);
    assert(IntFlagPolicy.asserts > IntFlagPolicy.noex);
    assert(IntFlagPolicy.throws > IntFlagPolicy.asserts);
}

/**
Function used to signal a failure and its proximate cause from integer math code. Depending on the value of the `policy`
parameter, `raise()` will either:
$(UL
    $(LI Throw a `CheckedIntException`,)
    $(LI Trigger an assertion failure, or)
    $(LI Set a bit in `IntFlags.local` that can be checked by the caller later.)
)
*/
template raise(IntFlagPolicy policy) {
    static if(policy == IntFlagPolicy.throws) {
        void raise(IntFlags flags) pure {
            version(DigitalMars) pragma(inline, false); // DMD usually won't inline the caller without this.
            if(flags) throw new CheckedIntException(flags);
        }
        void raise(IntFlag flag) pure {
            version(DigitalMars) pragma(inline, false); // DMD usually won't inline the caller without this.
            if(flag) throw new CheckedIntException(flag);
        }
    } else
    static if(policy == IntFlagPolicy.asserts) {
        void raise(IntFlags flags) pure nothrow @nogc {
            version(assert) {
                version(DigitalMars) pragma(inline, false); // DMD usually won't inline the caller without this.
                assert(!flags, flags.front.desc); // throw AssertError
            } else
                if(flags) assert(0); // halt
        }
        void raise(IntFlag flag) pure nothrow @nogc {
            version(assert) {
                version(DigitalMars) pragma(inline, false); // DMD usually won't inline the caller without this.
                assert(!flag, flag.desc); // throw AssertError
            } else
                if(flag) assert(0); // halt
        }
    } else
    static if(policy == IntFlagPolicy.noex) {
        void raise(IntFlags flags) nothrow @nogc {
          /+pragma(inline, true);+/
            IntFlags.local |= flags;
        }
        void raise(IntFlag flag) nothrow @nogc {
          /+pragma(inline, true);+/
            IntFlags.local |= flag;
        }
    } else
    static if(policy == IntFlagPolicy.none) {
        void raise(IntFlags flags) pure nothrow @nogc {
          /+pragma(inline, true);+/ }
        void raise(IntFlag flag) pure nothrow @nogc {
          /+pragma(inline, true);+/ }
    } else
        static assert(false);
}
///
unittest {
    import checkedint.throws : raise; // set IntFlagPolicy.throws

    bool caught = false;
    try {
        raise(IntFlag.div0);
    } catch(CheckedIntException e) {
        caught = (e.intFlags == IntFlag.div0);
    }
    assert(caught);
}
///
@trusted unittest {
    import checkedint.asserts : raise; // set IntFlagPolicy.asserts

    bool caught = false;
    try {
        raise(IntFlag.div0);
    } catch(Error e) {
        caught = (e.msg == "divide by zero");
    }
    assert(caught);
}
///
unittest {
    import checkedint.noex : raise; // set IntFlagPolicy.noex

    raise(IntFlag.div0);
    raise(IntFlag.posOver);

    assert(IntFlags.local == (IntFlag.div0 | IntFlag.posOver));

    IntFlags.local.clear();
}
///
unittest {
    // Multiple signaling strategies may be usefully mixed within the same program:
    alias IFP = IntFlagPolicy;

    static void fails() nothrow {
        raise!(IFP.noex)(IntFlag.negOver);
        raise!(IFP.noex)(IntFlag.imag);
    }

    bool caught = false;
    try {
        fails();
        // Flags that were raised by `nothrow` code can easily be turned into an exception by the caller.
        raise!(IFP.throws)(IntFlags.local.clear());
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

    // Ordered from lowest to highest priority, because pure @nogc assert can only show one.
    private static immutable strs = [
        "{NULL}",
        "{overflow}",
        "{positive overflow}",
        "{negative overflow}",
        "{imaginary component}",
        "{undefined result}",
        "{divide by zero}"
    ];
public:
    static if(__VERSION__ >= 2067) {
        version(GNU) { static assert(false); }

/// Overflow occured.
        enum IntFlag over    = 1;
/// Overflow occured because a value was too large.
        enum IntFlag posOver = 2;
/// Overflow occured because a value was too negative.
        enum IntFlag negOver = 3;
/// The result is imaginary, and as such not representable by an integral type.
        enum IntFlag imag    = 4;
/// The result of the operation is undefined mathematically, by the API, or both.
        enum IntFlag undef   = 5;
/// A division by zero was attempted.
        enum IntFlag div0    = 6;
    } else {
        static @property pure nothrow @nogc {
            auto over() {
                return IntFlag(1); }
            auto posOver() {
                return IntFlag(2); }
            auto negOver() {
                return IntFlag(3); }
            auto imag() {
                return IntFlag(4); }
            auto undef() {
                return IntFlag(5); }
            auto div0() {
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
    uint _bits = 0;
    @property uint bits() const pure nothrow @nogc {
        return _bits; }
    @property void bits(uint bits) pure nothrow @nogc {
        // filter out {NULL}
        _bits = bits & ~1;
    }

    this(uint bits) pure nothrow @nogc {
        this.bits = bits; }

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

`raise!(IntFlagPolicy.throws)(IntFlags.local.clear())` is a convenient way that the caller of a `nothrow` function can
convert any flags that were raised into an exception.
*/
    IntFlags clear() pure nothrow @nogc {
        IntFlags ret = this;
        _bits = 0;
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
            bits = this.bits & that.bits;
        else
        static if(op == "|")
            bits = this.bits | that.bits;
        else
        static if(op == "-")
            bits = this.bits & ~(that.bits);

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
        return bits != 0; }
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
        return bits == 0; }
/// Get the first set `IntFlag`.
    @property IntFlag front() const pure nothrow @nogc {
        // bsr() is undefined for 0.
        return IntFlag(bsr(bits | 1));
    }
/// Clear the first set `IntFlag`. This is equivalent to `flags -= flags.front`.
    ref IntFlags popFront() pure nothrow @nogc {
        // bsr() is undefined for 0.
        bits = bits & ~(1u << bsr(bits | 1));
        return this;
    }
/// Get a mutable copy of this `IntFlags` value, so as not to `clear()` the original by iterating through it.
    @property IntFlags save() const pure nothrow @nogc {
        return this; }
/// Get the number of raised flags.
    @property uint length() const pure nothrow @nogc {
        return popcnt(bits); }

    unittest {
        import std.range : isForwardRange, hasLength;
        static assert(isForwardRange!IntFlags);
        static assert(hasLength!IntFlags);
    }

/// The standard `IntFlags` set for the current thread. `raise!(IntFlagPolicy.noex)()` mutates this variable.
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
        import checkedint.noex : raise; // set IntFlagPolicy.noex

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
        assert(flags.toString() == "{undefined result, imaginary component}", flags.toString());
    }

/// An IntFlags value with all possible flags raised.
    enum IntFlags all = IntFlags((~0u >>> (8*_bits.sizeof - IntFlag.strs.length)) ^ 0x1);
    ///
    unittest {
        assert(IntFlags.all.length == 6);
    }
}

/**
An `Exception` representing the cause of an integer math failure.

A new instances may be created and thrown using `raise!(IntFlagPolicy.throws)()`.
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
