# oeis-sequences
[![Code style: black](https://img.shields.io/badge/code%20style-black-000000.svg)](https://github.com/psf/black)

Python functions to generate [The On-Line Encyclopedia of Integer Sequences](https://oeis.org/) (OEIS) sequences

## Requirements
Requires `python` >= 3.8

## Installation
`pip install oeis-sequences`

## Usage
After installation, `import OEISsequences` will import all the functions accessible via `OEISsequences.Axxxxxx`.
Alternatively, invidividual functions can be imported as `from OEISsequences import Axxxxxx`.

For each sequence, there are 3 different kinds of functions:

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

where a(*offset*) is the first term returned by the generator, this value of *offset* is the same as the *offset* parameter in the OEIS database.

Some functions `Axxxxxx_gen` contain an optional keyword `startvalue` that returns a generator of terms that are larger than or equal to `startvalue`.

## Examples

Least power of 3 having exactly n consecutive 7's in its decimal representation.
``` 
from OEISsequences import A131546
print(A131546(5))
>> 721
```  
Minimal exponents m such that the fractional part of (10/9)<sup>m</sup> obtains a maximum (when starting with m=1).   
```
from itertools import islice
from OEISsequences import A153695_gen
print(list(islice(A153695_gen(),10)))
>> [1, 2, 3, 4, 5, 6, 13, 17, 413, 555]
```

Numbers n such that n<sup>3</sup> has one or more occurrences of exactly nine different digits.
```
from OEISsequences import A235811_gen 
print(list(islice(A235811_gen(startvalue=1475),10)))
>> [1475, 1484, 1531, 1706, 1721, 1733, 1818, 1844, 1895, 1903]
```