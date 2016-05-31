/**
Copyright: Copyright Thomas Stuart Bockman 2015
License: $(LINK2 http://www.boost.org/LICENSE_1_0.txt, Boost License 1.0).
Authors: Thomas Stuart Bockman
**/
module checkedint.tests;
static import safeOp = checkedint.tests.contract.safeop;
static import smartOp = checkedint.tests.contract.smartop;
import checkedint.tests.benchmark;

void main()
{
    import std.stdio;

    void compiledMsg(string name) {
        writefln("Compiled with %s %s-bit, version %s.", name, size_t.sizeof * 8, __VERSION__); }
    version(DigitalMars) { compiledMsg("DMD"); }
    version(GNU)         { compiledMsg("GDC"); }
    version(LDC)         { compiledMsg("LDC"); }
    version(SDC)         { compiledMsg("SDC"); }

    debug { writeln("This is a DEBUG build. Inlining and optimizations are required for good performance."); }

    safeOp.all();
    smartOp.all();

    benchMacro();
}
