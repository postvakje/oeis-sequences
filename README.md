# oeis-sequences
[![Code style: black](https://img.shields.io/badge/code%20style-black-000000.svg)](https://github.com/psf/black)

Python functions to generate [The On-Line Encyclopedia of Integer Sequences](https://oeis.org/) (OEIS) sequences.

Python is the ideal language for this purpose because of the following reasons:

1. Python is a general purpose programming language with support for file I/O and graphing.
2. Arbitrary size integer format is standard in Python. This is important as many sequences in OEIS contain very large integers that will not fit in 64-bit integer formats. This allows the implemented functions to generate terms for arbitrary large `n` and they do not depend on floating point precision. For higher performance, one can use [`gmpy2`](https://pypi.org/project/gmpy2/).
3. There exists extensive modules for combinatorics and number theory such as `math`, `itertools` and [`sympy`](https://www.sympy.org/en/index.html).

Although Python can be slow as it is an interpreted language, this can be mitigated somewhat using tools such as [`pypy`](https://www.pypy.org/) and [`numba`](https://numba.pydata.org/).

## Requirements
Requires `python` >= 3.8

## Installation
`pip install OEISsequences`

## Usage
After installation, `from oeis_sequences import OEISsequences` will import all the functions accessible via `OEISsequences.Axxxxxx`.
Alternatively, invidividual functions can be imported as `from oeis_sequences.OEISsequences import Axxxxxx`.

For each sequence, there are (up to) 3 different kinds of functions:

1. Functions named `Axxxxxx`: Axxxxxx(n) returns the *n*-th term of OEIS sequence Axxxxxx.

2. Functions named `Axxxxxx_T`: returns T(n,k) for OEIS sequences where the natural definition is a 2D table *T*.

3. Functions named `Axxxxxx_gen`: Axxxxxx_gen() returns a generator of OEIS sequence Axxxxxx.

The function `Axxxxxx` is best used to compute a single term. The generator `Axxxxxx_gen` is typically defined for sequences where terms are best generated sequentially and is best used when computing a sequence of consecutive terms. 

For the generator, we can for example use `list(islice(Axxxxxx_gen(),10))` to return the first 10 terms of sequence Axxxxxx
Alternatively, setting `gen = Axxxxxx_gen()` and using `next(gen)` returns the next term of the sequence.

Given `Axxxxxx_gen`, one can define a function `Axxxxxx` as: 

```
def Axxxxxx(n,offset=1): return next(islice(Axxxxxx_gen(),n-offset,None))
```

where a(*offset*) is the first term returned by the generator. This value of *offset* is the same as the *offset* parameter in the OEIS database.

Some functions `Axxxxxx_gen` contain an optional keyword `startvalue` that returns a generator of terms that are larger than or equal to `startvalue`. This keyword is only available on sequences that are nondecreasing.

For some sequences, e.g. `A269483`, both types of functions `Axxxxxx` and `Axxxxxx_gen` are provided.

## Examples

Least power of 3 having exactly n consecutive 7's in its decimal representation.
``` 
from oeis_sequences.OEISsequences import A131546
print(A131546(5))
>> 721
```  
Minimal exponents m such that the fractional part of (10/9)<sup>m</sup> obtains a maximum (when starting with m=1).   
```
from itertools import islice
from oeis_sequences.OEISsequences import A153695_gen
print(list(islice(A153695_gen(),10)))
>> [1, 2, 3, 4, 5, 6, 13, 17, 413, 555]
```

Numbers n such that n<sup>3</sup> has one or more occurrences of exactly nine different digits.
```
from oeis_sequences.OEISsequences import A235811_gen 
print(list(islice(A235811_gen(startvalue=1475),10))) # print first 10 terms >= 1475
>> [1475, 1484, 1531, 1706, 1721, 1733, 1818, 1844, 1895, 1903]
```

## Utility functions
The module also includes some utility functions for exploring integer sequences in OEIS such as palindrome generator, Boustrophedon transform, run length transform, lunar arithmetic, etc.
