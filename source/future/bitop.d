/**
Copyright: Copyright Thomas Stuart Bockman 2015
License: <a href="http://www.boost.org/LICENSE_1_0.txt">Boost License 1.0</a>.
Authors: Thomas Stuart Bockman
*/

module future.bitop;
public import core.bitop;

static if(__VERSION__ < 2071) {
@safe: pure: nothrow: @nogc:

    private union Split64 {
        ulong u64;
        struct {
            version(LittleEndian) {
                uint lo;
                uint hi;
            } else {
                uint hi;
                uint lo;
            }
        }
    }
    private auto split64(ulong x) {
        if(__ctfe) {
            Split64 ret = void;
            ret.lo = cast(uint)x;
            ret.hi = cast(uint)(x >>> 32);
            return ret;
        } else
            return Split64(x);
    }

    int bsf(size_t v) {
        return core.bitop.bsf(v); }
    static if(size_t.sizeof == uint.sizeof) {
        int bsf(ulong v) pure
        {
            const sv = split64(v);
            return (sv.lo == 0)?
                bsf(sv.hi) + 32 :
                bsf(sv.lo);
        }
    } else
        static assert(size_t.sizeof == ulong.sizeof);

    int bsr(size_t v) {
        return core.bitop.bsr(v); }
    static if(size_t.sizeof == uint.sizeof) {
        int bsr(ulong v) {
            const sv = split64(v);
            return (sv.hi == 0)?
                bsr(sv.lo) :
                bsr(sv.hi) + 32;
        }
    } else
        static assert(size_t.sizeof == ulong.sizeof);

    int popcnt(uint x) {
        // Select the fastest method depending on the compiler and CPU architecture
        version(LDC) {
            return _popcnt(x);
        } else {
            version(DigitalMars) {
                static if (is(typeof(_popcnt(uint.max)))) {
                    import core.cpuid;
                    if (!__ctfe && hasPopcnt)
                        return _popcnt(x);
                }
            }

            return soft_popcnt!uint(x);
        }
    }
    int popcnt(ulong x) {
        // Select the fastest method depending on the compiler and CPU architecture
        version(LDC)
            return _popcnt(x);
        else {
            import core.cpuid;

            static if (size_t.sizeof == uint.sizeof) {
                const sx = split64(x);
                version(DigitalMars) {
                    static if (is(typeof(_popcnt(uint.max)))) {
                        if (!__ctfe && hasPopcnt)
                            return _popcnt(sx.lo) + _popcnt(sx.hi);
                    }
                }

                return soft_popcnt!uint(sx.lo) + soft_popcnt!uint(sx.hi);
            } else
            static if (size_t.sizeof == ulong.sizeof) {
                version(DigitalMars) {
                    static if (is(typeof(_popcnt(ulong.max)))) {
                        if (!__ctfe && hasPopcnt)
                            return _popcnt(x);
                    }
                }

                return soft_popcnt!ulong(x);
            } else
                static assert(false);
        }
    }

    private int soft_popcnt(N)(N x) pure
        if (is(N == uint) || is(N == ulong))
    {
        // Avoid branches, and the potential for cache misses which
        // could be incurred with a table lookup.

        // We need to mask alternate bits to prevent the
        // sum from overflowing.
        // add neighbouring bits. Each bit is 0 or 1.
        enum mask1 = cast(N) 0x5555_5555_5555_5555L;
        x = x - ((x>>1) & mask1);
        // now each two bits of x is a number 00,01 or 10.
        // now add neighbouring pairs
        enum mask2a = cast(N) 0xCCCC_CCCC_CCCC_CCCCL;
        enum mask2b = cast(N) 0x3333_3333_3333_3333L;
        x = ((x & mask2a)>>2) + (x & mask2b);
        // now each nibble holds 0000-0100. Adding them won't
        // overflow any more, so we don't need to mask any more

        enum mask4 = cast(N) 0x0F0F_0F0F_0F0F_0F0FL;
        x = (x + (x >> 4)) & mask4;

        enum shiftbits = is(N == uint)? 24 : 56;
        enum maskMul = cast(N) 0x0101_0101_0101_0101L;
        x = (x * maskMul) >> shiftbits;

        return cast(int) x;
    }
}
