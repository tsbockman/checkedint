# Checked integer math module for the [D Programming Language](http://dlang.org) 

As with many other languages (C, C++, Java, etc.), D's built-in integer data types are quite difficult to use correctly.

It is tempting to think of `int`, for example, as if it were an actual mathematical integer. Doing so, however leads to buggy code due to unintuitive behaviour like:

* Wrapped overflow
* Reinterpretation of signed values as unsigned in mixed expressions
* `Floating Point Exception`s which aren't `Exception`s and have nothing to do with floating point
* Formally "undefined behaviour" with some inputs for various operations

This `checkedint` module provides alternative operations and types that protect the user from most difficulties of this sort, while maintaining good performance (provided that inlining and optimizations are enabled).

The main downsides to using `checkedint` are:

* Some added friction when interfacing to non-`checkedint`-aware code.
* Slower compilation and larger binaries.

Use `dub build -b docs` to generate more extensive documentation for this package.

## Installation

This library is available as a DUB package: http://code.dlang.org/packages/checkedint
