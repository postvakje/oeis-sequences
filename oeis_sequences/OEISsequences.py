# -*- coding: utf-8 -*-
"""
Created on Thu Dec  2 11:43:37 2021

@author: Chai Wah Wu

Python functions to generate The On-Line Encyclopedia of Integer Sequences (OEIS) sequences

Requires python >= 3.8

Installation: pip install OEISsequences

After installation, `from oeis_sequences import OEISsequences` will import all the functions accessible via `OEISsequences.Axxxxxx`.
Alternatively, invidividual functions can be imported as `from oeis_sequences.OEISsequences import Axxxxxx`.

For each sequence, there are 3 different kinds of functions:

1. Functions named `Axxxxxx`: Axxxxxx(n) returns the *n*-th term of OEIS sequence Axxxxxx.

2. Functions named `Axxxxxx_T`: returns T(n,k) for OEIS sequences where the natural definition is a 2D table T.

3. Functions named `Axxxxxx_gen`: Axxxxxx_gen() returns a generator of OEIS sequence Axxxxxx.

The function `Axxxxxx` is best used to compute a single term. The generator `Axxxxxx_gen` is typically defined for sequences where terms are best generated sequentially and is best used when computing a sequence of consecutive terms. 

For the generator, we can for example use `list(islice(Axxxxxx_gen(),10))` to return the first 10 terms of sequence Axxxxxx
Alternatively, setting `gen = Axxxxxx_gen()` and using `next(gen)` returns the next term of the sequence.

Given `Axxxxxx_gen`, one can define a function `Axxxxxx` as: 

def Axxxxxx(n,offset=1): return next(islice(Axxxxxx_gen(),n-offset,None))

where a(offset) is the first term returned by the generator. This value of offset is the same as the offset parameter in the OEIS database.

Some functions `Axxxxxx_gen` contain an optional keyword `startvalue` that returns a generator of terms that are larger than or equal to `startvalue`.

For some sequences, e.g. `A269483`, both type of functions `Axxxxxx` and `Axxxxxx_gen` are provided.

Examples:
    
   from oeis_sequences.OEISsequences import A131546
   print(A131546(5))
   >> 721
  
   from itertools import islice
   from oeis_sequences.OEISsequences import A153695_gen
   print(list(islice(A153695_gen(),10)))
   >> [1, 2, 3, 4, 5, 6, 13, 17, 413, 555]
   
   from oeis_sequences.OEISsequences import A235811_gen 
   print(list(islice(A235811_gen(startvalue=1475),10)))
   >> [1475, 1484, 1531, 1706, 1721, 1733, 1818, 1844, 1895, 1903]

The module also includes some utility functions for exploring integer sequences in OEIS such as palindrome generator, 
Boustrophedon transform, run length transform, lunar arithmetic, etc.

"""

from __future__ import print_function, division
import sys, bisect, re
from functools import lru_cache, reduce
from itertools import (
    islice,
    count,
    product,
    permutations,
    takewhile,
    accumulate,
    combinations_with_replacement,
    combinations,
    repeat,
    groupby,
    chain,
    starmap,
    zip_longest,
)
from fractions import Fraction
from collections import Counter, deque
from math import factorial, floor, comb, prod, isqrt
from operator import mul, xor, add, or_
from operator import sub as operator_sub
from re import finditer, split, sub
from statistics import pvariance
from sympy.core.numbers import igcdex
from sympy import (
    factorint,
    divisors,
    integer_nthroot,
    divisor_sigma,
    nextprime,
    Matrix,
    divisor_count,
    isprime,
    prime,
    totient,
    sympify,
    primerange,
    primepi,
    composite,
    compositepi,
    factorial2,
    prevprime,
    primefactors,
    harmonic,
    multiplicity,
    n_order,
    primorial,
    sqrt,
    bernoulli,
    ff,
    rf,
    sin,
    cos,
    tan,
    fibonacci,
    lucas,
    pi,
    hyperexpand,
    expand,
    Poly,
    hermite,
    mod_inverse,
    EulerGamma,
    digamma,
    discrete_log,
    S,
    catalan,
    npartitions,
    ceiling,
    log,
    simplify,
)
from sympy.functions import hyper, partition, euler
from sympy.ntheory import (
    mobius,
    jacobi_symbol,
    legendre_symbol,
    sqrt_mod,
    multinomial_coefficients,
)
from sympy.ntheory.factor_ import (
    digits as sympydigits,
    udivisor_sigma,
    sieve,
    reduced_totient,
    core as numbercore,
    antidivisors,
    udivisors,
    antidivisor_count,
    primeomega,
    primenu,
)
from sympy.combinatorics.partitions import IntegerPartition
from sympy.utilities.iterables import (
    partitions,
    multiset_permutations,
    multiset_combinations,
    multiset_partitions,
)
from sympy.functions.combinatorial.numbers import stirling, bell
from sympy.ntheory.continued_fraction import (
    continued_fraction,
    continued_fraction_periodic,
    continued_fraction_reduce,
)
from sympy.ntheory.modular import crt
from sympy.ntheory.residue_ntheory import nthroot_mod
from sympy.combinatorics.subsets import Subset
from sympy.solvers.diophantine import diophantine
from sympy.solvers.diophantine.diophantine import diop_quadratic, diop_DN
from sympy.abc import x as symbolx, y as symboly
from gmpy2 import (
    mpz,
    fac,
    popcount,
    is_prime,
    is_square,
    next_prime,
    c_divmod,
    lucas2,
    fib,
    fib2,
    isqrt_rem,
    iroot_rem,
    is_power,
    digits as gmpy2digits,
)
from num2words import num2words
from unidecode import unidecode

if sys.version_info < (3, 9):
    from sympy import lcm as sympylcm, gcd as sympygcd

    def gcd(*x):
        r = x[0]
        for y in x[1:]:
            r = sympygcd(r, y)
        return r

    def lcm(*x):
        r = x[0]
        for y in x[1:]:
            r = sympylcm(r, y)
        return r

else:
    from math import lcm, gcd

""" Utility functions """


def is_pal(n, b=10):
    """check if n is a palindrome in base b"""
    return (s := sympydigits(n, b)[1:])[: (t := (len(s) + 1) // 2)] == s[: -t - 1 : -1]


def is_cubefree_string(s):
    """check if s is a cubefree string, i.e. there is no substring of the form ttt"""
    l = len(s)
    for i in range(l - 2):
        for j in range(1, (l - i) // 3 + 1):
            if s[i : i + 2 * j] == s[i + j : i + 3 * j]:
                return False
    return True


def pal10_gen():
    """generator of palindromes in base 10"""
    yield 0
    for x in count(1):
        for y in range(10 ** (x - 1), 10**x):
            s = str(y)
            yield int(s + s[-2::-1])
        for y in range(10 ** (x - 1), 10**x):
            s = str(y)
            yield int(s + s[::-1])


def pal_gen(b=10):
    """generator of palindromes in base b"""
    yield 0
    x = 1
    while True:
        n = b ** (x - 1)
        n2 = n * b
        for y in range(n, n2):  # odd-length
            k, m = y // b, 0
            while k >= b:
                k, r = divmod(k, b)
                m = b * m + r
            yield y * n + b * m + k
        for y in range(n, n2):  # even length
            k, m = y, 0
            while k >= b:
                k, r = divmod(k, b)
                m = b * m + r
            yield y * n2 + b * m + k
        x += 1


def palbase_gen(b=10):
    """generator of palindromes in base b <=10 written in base b"""
    yield 0
    for x in count(1):
        for y in range(b ** (x - 1), b**x):
            s = gmpy2digits(y, b)
            yield int(s + s[-2::-1])
        for y in range(b ** (x - 1), b**x):
            s = gmpy2digits(y, b)
            yield int(s + s[::-1])


def pal_odd_gen(l, b=10):
    """generator of odd-length palindromes in base b of length <= 2*l"""
    if l > 0:
        yield 0
        for x in range(1, l + 1):
            n = b ** (x - 1)
            n2 = n * b
            for y in range(n, n2):
                k, m = y // b, 0
                while k >= b:
                    k, r = divmod(k, b)
                    m = b * m + r
                yield y * n + b * m + k


def pal10_odd_range_gen(m=1):
    """generator of odd-length palindromes in base 10 of length at least m"""
    if m == 1:
        yield 0
    for x in count(m // 2 + 1):
        n = 10 ** (x - 1)
        for y in range(n, n * 10):
            s = str(y)
            yield int(s + s[-2::-1])


def multiset_perm_count(x):
    """count the number of permutations in a multiset (from a list or tuple)"""
    return factorial(len(x)) // prod(factorial(d) for d in Counter(x).values())


def intpartitiongen(n, m):
    """generator of partition of n into m decimal digits, return as list of strings"""
    return (
        "".join(str(d) for d in IntegerPartition(p).partition + [0] * (m - s))
        for s, p in partitions(n, k=9, m=m, size=True)
    )


@lru_cache(maxsize=None)
def intpartition(n, m):
    """partition of n into m decimal digits, return as list of strings"""
    return tuple(intpartitiongen(n, m))


def partitionpairs(xlist):
    """generator of all partitions into pairs and at most 1 singleton, returning the sums of the pairs"""
    if len(xlist) <= 2:
        yield [sum(xlist)]
    else:
        m = len(xlist)
        for i in range(m - 1):
            for j in range(i + 1, m):
                rem = xlist[:i] + xlist[i + 1 : j] + xlist[j + 1 :]
                y = [xlist[i] + xlist[j]]
                for d in partitionpairs(rem):
                    yield y + d


def integerlog(n, b):
    """computes largest integer k>=0 such that b^k <= n"""
    kmin, kmax = 0, 1
    while b**kmax <= n:
        kmax *= 2
    while True:
        kmid = (kmax + kmin) // 2
        if b**kmid > n:
            kmax = kmid
        else:
            kmin = kmid
        if kmax - kmin <= 1:
            break
    return kmin


def ispandigital(m, n):
    """return True iff m is pandigital in base n"""
    s = set()
    while m > 0:
        m, b = divmod(m, n)
        if b in s:
            return False
        s.add(b)
    return True


def ispandigital0(m, n):
    """return (True, s) if m is pandigital in base n and (False, False) otherwise where s is true iff m has a zero digit"""
    s = set()
    z = False
    while m > 0:
        m, b = divmod(m, n)
        if b in s:
            return False, False
        if b == 0:
            z = True
        s.add(b)
    return True, z


def intbase(dlist, b=10):
    """convert list of digits in base b to integer"""
    y = 0
    for d in dlist:
        y = y * b + d
    return y


def is_emirp(n, b=10):
    """check if n is an emirp in base b"""
    x, y = n, 0
    while x >= b:
        x, r = divmod(x, b)
        y = y * b + r
    y = y * b + x
    return n != y and isprime(y)


def antidivisor_sigma(n):
    """sum of antidivisors of n"""
    return (
        sum(2 * d for d in divisors(n, generator=True) if n > 2 * d and n % (2 * d))
        + sum(d for d in divisors(2 * n - 1, generator=True) if n > d >= 2 and n % d)
        + sum(d for d in divisors(2 * n + 1, generator=True) if n > d >= 2 and n % d)
    )


def divisor_prod(n):
    """product of divisors of n"""
    d = divisor_count(n)
    return isqrt(n) ** d if d % 2 else n ** (d // 2)


def divisor_sigma_mod(n, m):
    """computes divisor_sigma(n) mod m"""
    y = 1
    for p, e in factorint(n).items():
        y = (y * (p ** (e + 1) - 1) // (p - 1)) % m
    return y


def reversedigits(n, b=10):
    """reverse digits of n in base b"""
    x, y = n, 0
    while x >= b:
        x, r = divmod(x, b)
        y = b * y + r
    return b * y + x


@lru_cache(maxsize=None)
def divisor_tuple(n):
    """cached unordered tuple of divisors"""
    return tuple(divisors(n, generator=True))


def RLT(n, f):
    """run length transform of a function f"""
    return prod(f(len(d)) for d in split("0+", bin(n)[2:]) if d != "") if n > 0 else 1


def repeating_decimals_expr(f, digits_only=False):
    """returns repeating decimals of Fraction f as the string aaa.bbb[ccc].
    returns only digits if digits_only=True.
    """
    a, b = f.as_integer_ratio()
    m2, m5 = multiplicity(2, b), multiplicity(5, b)
    r = max(m2, m5)
    k, m = 10**r, 10 ** (t := n_order(10, b // 2**m2 // 5**m5)) - 1
    c = k * a // b
    s = str(c).zfill(r)
    if digits_only:
        return s + str(m * k * a // b - c * m).zfill(t)
    else:
        w = len(s) - r
        return s[:w] + "." + s[w:] + "[" + str(m * k * a // b - c * m).zfill(t) + "]"


def Boustrophedon_transform(x):
    """Boustrophedon transform of the iterable x
    returns generator"""
    blist = tuple()
    for m in x:
        yield (blist := tuple(accumulate(reversed(blist), initial=m)))[-1]


def inverse_Boustrophedon_transform(x):
    """inverse Boustrophedon transform of the iterable x
    returns generator"""
    blist = tuple()
    for m in x:
        yield (
            blist := tuple(accumulate(reversed(blist), func=operator_sub, initial=m))
        )[-1]


""" Lunar arithmetic """


def lunar_add(n, m):
    """lunar addition"""
    sn, sm = str(n), str(m)
    l = max(len(sn), len(sm))
    return int("".join(max(i, j) for i, j in zip(sn.rjust(l, "0"), sm.rjust(l, "0"))))


def lunar_mul(n, m):
    """lunar multiplication"""
    sn, sm, y = str(n), str(m), 0
    for i in range(len(sm)):
        c = sm[-i - 1]
        y = lunar_add(y, int("".join(min(j, c) for j in sn)) * 10**i)
    return y


""" """

""" List of OEIS sequences """


def A349804(n):
    return int((lambda x: x + x[::-1])("".join(str(d) for d in range(1, n + 1))))


def A349805(n):
    return int((lambda x: x + x[::-1])("".join(str(d) for d in range(1, n + 1)))) // 11


def A173426(n):
    return int(
        "".join(str(d) for d in range(1, n + 1))
        + "".join(str(d) for d in range(n - 1, 0, -1))
    )


def A349724():  # generator of terms
    for k in count(1):
        if (
            not k
            * (k + 1)
            // 2
            % prod(p ** (e - 1) * ((p - 1) * e + p) for p, e in factorint(k).items())
        ):
            yield k


def A018804(n):
    return prod(p ** (e - 1) * ((p - 1) * e + p) for p, e in factorint(n).items())


def A349711(n):
    f = factorint(n)
    plist, m = list(f.keys()), sum(f[p] * p for p in f)
    return sum(
        (lambda x: x * (m - x))(sum(d[i] * p for i, p in enumerate(plist)))
        for d in product(*(list(range(f[p] + 1)) for p in plist))
    )


def A349712(n):
    f = factorint(n)
    plist = list(f.keys())
    return sum(
        sum(int(d[i] > 0) * p for i, p in enumerate(plist))
        * sum(int(d[i] < f[p]) * p for i, p in enumerate(plist))
        for d in product(*(list(range(f[p] + 1)) for p in plist))
    )


def A348169_gen(startvalue=1):  # generator of terms
    for n in count(max(startvalue, 1)):
        for d in divisors(n, generator=False):
            x, x2 = 1, 1
            while 3 * x2 <= d:
                y, y2 = x, x2
                z2 = d - x2 - y2
                while z2 >= y2:
                    z, w = integer_nthroot(z2, 2)
                    if w:
                        A = n // d
                        B, u = divmod(n, x * (y + z) + y * z)
                        if u == 0 and gcd(A, B) == 1:
                            yield n
                            break
                    y += 1
                    y2 += 2 * y - 1
                    z2 -= 2 * y - 1
                else:
                    x += 1
                    x2 += 2 * x - 1
                    continue
                break
            else:
                continue
            break


def A349680(n):
    return n + (n - 1) * divisor_sigma(n, 0) - divisor_sigma(n, 1)


def A349643(n):
    plist, clist = [2], [1]
    for i in range(1, n + 1):
        plist.append(nextprime(plist[-1]))
        clist.append((-1) ** i * comb(n, i))
    while True:
        if sum(clist[i] * plist[i] for i in range(n + 1)) == 0:
            return plist[0]
        plist = plist[1:] + [nextprime(plist[-1])]


def A349544helper_(k, n):
    if k == 0 and n == 0:
        return (x for x in (1,))
    if k < n:
        return (y * 3 for y in A349544helper_(k, n - 1))
    return (abs(x + y) for x in A349544helper_(k - 1, n) for y in (2**n, -(2**n)))


def A349544(n):
    return min(A349544helper_(n, n))


def A348183(n):
    return Matrix(n, n, [pow(i + j, 2, n) for i in range(n) for j in range(n)]).det()


def A348226(n):
    """code assumes n <= 63 or n is prime"""
    if is_prime(n):
        return 2
    if n > 63:
        return "Error: n <= 63 or n is prime"
    p = 2
    while True:
        for i in range(n - 1, 1, -1):
            s = gmpy2digits(p, i)
            if not is_prime(int(s, n)):
                break
        else:
            return p
        p = next_prime(p)


def A349529(n):
    return len(
        list(
            filter(
                lambda x: x == 1,
                Counter(
                    "".join(d)
                    for d in permutations(bin(i)[2:] for i in range(1, n + 1))
                ).values(),
            )
        )
    )


def A066640_gen():
    return filter(
        lambda n: all(
            set(str(m)) <= {"1", "3", "5", "7", "9"}
            for m in divisors(n, generator=True)
        ),
        count(1, 2),
    )


def A014261_gen():
    return filter(lambda n: set(str(n)) <= {"1", "3", "5", "7", "9"}, count(1, 2))


def A117960_gen():
    return filter(
        lambda n: set(str(n)) <= {"1", "3", "5", "7", "9"},
        (m * (m + 1) // 2 for m in count(0)),
    )


def A349243_gen(startvalue=0):
    return filter(
        lambda n: set(str(n * (n + 1) // 2)) <= {"1", "3", "5", "7", "9"},
        count(max(startvalue, 0)),
    )


def A348162_gen():  # generator of terms
    s, n, m = "0", 1, 0
    while True:
        yield m
        n, m = n * 2, int(s, 4) + int(("02" * n)[: len(s)], 4)
        s = format(m, "0" + str(n) + "b")


def A349360(n):
    m = divisor_count(n)
    return m * (m - n) + n * (n + 1) // 2


def A349460_gen():
    return filter(lambda n: set(str(n)) <= {"0", "2", "4"}, (n * n for n in count(0)))


def A342975_gen():
    return filter(lambda n: set(str(n)) <= {"0", "1", "3"}, (n**3 for n in count(0)))


def A050251(n):
    return (
        4 * n if n <= 1 else 1 + sum(1 for i in pal_odd_gen((n + 1) // 2) if isprime(i))
    )


def A229629_gen(startvalue=1):  # generator of terms
    for n in count(max(startvalue, 1)):
        s, sn = str(n**n), str(n)
        l, ln = len(s), len(sn)
        if (ln - l) % 2 == 0 and s[l // 2 - ln // 2 : l // 2 + (ln + 1) // 2] == sn:
            yield n


def A347113_gen():  # generator of terms
    j, nset, m = 2, {1}, 2
    yield 1
    while True:
        k = m
        while k == j or gcd(k, j) == 1 or k in nset:
            k += 1
        yield k
        j = k + 1
        nset.add(k)
        while m in nset:
            m += 1


def A347313(n):
    p, gen = prime(n), A347113_gen()
    for i in count(1):
        q = next(gen)
        if p == q:
            return i


def A179993_gen(startvalue=1):  # generator of terms
    for m in count(max(startvalue, 1)):
        if all(
            isprime(m // a - a) for a in takewhile(lambda x: x * x <= m, divisors(m))
        ):
            yield m


def A349327_gen():  # generator of terms
    n = 2
    while True:
        if isprime(n**2 - 2) and isprime(2 * n**2 - 1):
            yield n
        n = nextprime(n)


def A348784_gen():  # generator of terms
    i = 1
    for m in A347113_gen():
        if isprime(m):
            yield i
        i += 1


def A348158(n):
    return sum(set(map(totient, divisors(n, generator=True))))


def A348213(n):
    c, k = 0, n
    m = A348158(k)
    while m != k:
        k, m = m, A348158(m)
        c += 1
    return c


def A003434(n):
    c, m = 0, n
    while m > 1:
        c += 1
        m = totient(m)
    return c


def A013588(n):
    s, k = set(Matrix(n, n, p).det() for p in product([0, 1], repeat=n**2)), 1
    while k in s:
        k += 1
    return k


def iteratedphi(n):
    m = n
    while m > 1:
        m = totient(m)
        yield m


def A092694(n):
    return prod(iteratedphi(n))


def A092693(n):
    return sum(iteratedphi(n))


def A254007(n):
    return (
        1
        if n == 0
        else len(
            set(tuple(sorted(accumulate(d))) for d in product((-1, 1), repeat=n - 1))
        )
    )


def A348780(n):
    return sum(islice(A347113_gen(), n))


def A343878(n):
    k, c = 0, dict()
    while True:
        m, r = 0, 1
        while r > 0:
            k += 1
            r = c.get(m, 0)
            if n == r:
                return k
            c[r] = c.get(r, 0) + 1
            m += 1


def A348781(n):
    k, s, c = 0, 0, dict()
    while True:
        m, r = 0, 1
        while r > 0:
            k += 1
            if k > n:
                return s
            r = c.get(m, 0)
            s += r
            c[r] = c.get(r, 0) + 1
            m += 1


def A172500(n):
    return sympify("0.[" + str(n) + "]").p


def A172502(n):
    return sympify("0.[" + str(n) + "]").q


def A348870(n):
    return (lambda m, r: r.p if m % 2 else r.q)(
        n, sympify("0.[" + str((n + 1) // 2) + "]")
    )


def A339665(n):
    ds = tuple(divisors(n, generator=True))
    return sum(
        sum(1 for d in combinations(ds, i) if n * i % sum(d) == 0)
        for i in range(1, len(ds) + 1)
    )


def A339453(n):
    m = lcm(*range(2, n + 1))
    return sum(
        1
        for i in range(1, n + 1)
        for d in combinations((m // i for i in range(1, n + 1)), i)
        if m * i % sum(d) == 0
    )


def A349148(n):
    k = lcm(*range(2, n + 1))
    return sum(
        1
        for d in combinations_with_replacement((k // d for d in range(1, n + 1)), n)
        if sum(d) % k == 0
    )


def A349215(n):
    fs = factorint(n)
    return sum(a - 1 for a in fs.keys()) + prod(1 + d for d in fs.values())


def A349214(n):
    p = list(primerange(2, n + 1))
    return n - len(p) + sum(p)


@lru_cache(maxsize=None)
def A339508(n):
    nlist = [i for i in range(2, n) if i % 10 != 0]
    if n == 0 or n == 1:
        return 1
    c = A339508(n - 1)
    if n % 10 != 0:
        sn = str(n)
        if sn == sn[::-1]:
            c += 1
        for i in range(1, len(nlist) + 1):
            for d in combinations(nlist, i):
                s = str(prod(d) * n)
                if s == s[::-1]:
                    c += 1
    return c


@lru_cache(maxsize=None)
def A339484(n):
    return (
        1
        if n == 1
        else A339484(n - 1)
        + sum(
            sum(d) + n == (i + 1) ** 2
            for i in range(1, n)
            for d in combinations(range(1, n), i)
        )
    )


def A348516(n):
    k, s = 1, gmpy2digits(n, 3).rstrip("0")
    if s == "1" or s == "":
        return 1 - len(s)
    m = int(s, 3)
    mk = m
    while s.count("1") != s.count("2"):
        k += 1
        mk *= m
        s = gmpy2digits(mk, 3)
    return k


def A349179_gen():  # generator of terms
    c = 0
    for i in count(1):
        if (m := A339665(i)) > c:
            yield i
            c = m


def A349145(n):
    return sum(
        1
        for d in product(range(1, n + 1), repeat=n)
        if sum(Fraction(i + 1, j) for i, j in enumerate(d)).denominator == 1
    )


def A349146(n):
    k = lcm(*range(2, n + 1))
    dlist = tuple(k // d for d in range(1, n + 1))
    return sum(
        multiset_perm_count(d)
        for d in combinations_with_replacement(range(1, n + 1), n)
        if sum(dlist[e - 1] for e in d) % k == 0
    )


def A348895(n):
    l, c, nmax, k = 9 * n, 0, 0, 10 ** (n - 1)
    while l > c:
        for p in intpartition(l, n):
            for q in multiset_permutations(p):
                w = int("".join(q))
                if w >= k:
                    wr = w % l
                    if wr > c:
                        c = wr
                        nmax = w
                    if wr == c and nmax < w:
                        nmax = w
        l -= 1
    return nmax


def A348894(n):
    l, c, nmin, k = 9 * n, 0, 10**n - 1, 10 ** (n - 1)
    while l > c:
        for p in intpartition(l, n):
            for q in multiset_permutations(p):
                w = int("".join(q))
                if w >= k:
                    wr = w % l
                    if wr > c:
                        c = wr
                        nmin = w
                    if wr == c and nmin > w:
                        nmin = w
        l -= 1
    return nmin


def A348730(n):
    l, c, k = 9 * n, 0, 10 ** (n - 1)
    while l - 1 > c:
        c = max(
            c,
            max(
                s % l
                for s in (
                    int("".join(q))
                    for p in intpartition(l, n)
                    for q in multiset_permutations(p)
                )
                if s >= k
            ),
        )
        l -= 1
    return c


def A348706(n):
    return int(gmpy2digits(n, 3).replace("0", ""), 3)


def A348651(n):
    return popcount(fac(fac(n)))


def A348658_gen(startvalue=1):  # generator of terms
    for k in count(max(startvalue, 1)):
        a, b = divisor_sigma(k), divisor_sigma(k, 0) * k
        c = gcd(a, b)
        n1, n2 = 5 * (a // c) ** 2 - 4, 5 * (b // c) ** 2 - 4
        if (integer_nthroot(n1, 2)[1] or integer_nthroot(n1 + 8, 2)[1]) and (
            integer_nthroot(n2, 2)[1] or integer_nthroot(n2 + 8, 2)[1]
        ):
            yield k


def A108861_gen():  # generator of terms
    k2, kf = 1, 1
    for k in count(1):
        k2 *= 2
        kf *= k
        if not sum(int(d) for d in str(k2 * kf)) % k:
            yield k


def A244060(n):
    return sum(int(d) for d in str(factorial(2**n)))


def A008906(n):
    return len(str(factorial(n)).rstrip("0"))


def A348446_gen():  # generator of terms. Greedy algorithm.
    a = 1
    c, b = Counter(), 1
    while True:
        k, kb = 1, b
        while c[kb] >= kb:
            k += 1
            kb += b
        c[kb] += 1
        b = k
        a2 = k
        yield a - a2
        k, kb = 1, b
        while c[kb] >= kb:
            k += 1
            kb += b
        c[kb] += 1
        b = k
        a = k


def A348441_gen():  # generator of terms
    yield 1
    c, p, a = 1, {1}, 1
    for i in count(3):
        n, na = 1, a
        while na in p:
            n += 1
            na += a
        p.add(na)
        a = n
        if c < n:
            c = n
            yield i


def A348247(n):
    c, b, p = Counter(), 1, prime(n)
    for i in count(1):
        k, kb = 1, b
        while c[kb] >= kb:
            k += 1
            kb += b
        if kb == p:
            return i
        c[kb] += 1
        b = k


def A348353_gen():  # generator of terms.
    p, q, r = 2, 3, 5
    while True:
        if isprime(p * p + q + r) and isprime(p + q * q + r) and isprime(p + q + r * r):
            yield p
        p, q, r = q, r, nextprime(r)


def A307730_gen():  # generator of terms. Greedy algorithm.
    c, b = Counter(), 1
    while True:
        k, kb = 1, b
        while c[kb] >= kb:
            k += 1
            kb += b
        c[kb] += 1
        b = k
        yield kb


def A348442_gen():  # generator of terms
    yield 1
    c, p, a = 1, {1}, 1
    while True:
        n, na = 1, a
        while na in p:
            n += 1
            na += a
        p.add(na)
        a = n
        if c < na:
            c = na
            yield c


def A348443_gen():  # generator of terms
    yield 1
    c, p, a = 1, {1}, 1
    for i in count(2):
        n, na = 1, a
        while na in p:
            n += 1
            na += a
        p.add(na)
        a = n
        if c < na:
            c = na
            yield i


def A348440_gen():  # generator of terms
    yield 1
    c, p, a = 1, {1}, 1
    while True:
        n, na = 1, a
        while na in p:
            n += 1
            na += a
        p.add(na)
        a = n
        if c < n:
            c = n
            yield c


def A088177_gen():  # generator of terms
    yield 1
    yield 1
    p, a = {1}, 1
    while True:
        n = 1
        while n * a in p:
            n += 1
        p.add(n * a)
        a = n
        yield n


def A088178_gen():  # generator of terms
    yield 1
    p, a = {1}, 1
    while True:
        n, na = 1, a
        while na in p:
            n += 1
            na += a
        p.add(na)
        a = n
        yield na


def A099378(n):
    return (lambda x, y: x // gcd(x, y * n))(divisor_sigma(n), divisor_sigma(n, 0))


def A099377(n):
    return (lambda x, y: y * n // gcd(x, y * n))(divisor_sigma(n), divisor_sigma(n, 0))


def A103339(n):
    return (lambda x, y: y * n // gcd(x, y * n))(
        udivisor_sigma(n), udivisor_sigma(n, 0)
    )


def A103340(n):
    return (lambda x, y: x // gcd(x, y * n))(udivisor_sigma(n), udivisor_sigma(n, 0))


def A348411_gen():
    return filter(
        (
            lambda n: (lambda x, y: 2 * gcd(x, y * n) == x)(
                divisor_sigma(n), divisor_sigma(n, 0)
            )
        ),
        count(1),
    )


def A066411(n):
    b = tuple(comb(n, k) for k in range(n // 2 + 1))
    return len(
        set(
            (
                sum(d[i] * b[i] for i in range(n // 2 + 1))
                for d in partitionpairs(list(range(n + 1)))
            )
        )
    )


def A348338(n):
    m, s = 10**n, set()
    for k in range(m):
        c, k2, kset = 0, k, set()
        while k2 not in kset:
            kset.add(k2)
            c += 1
            k2 = 2 * k2 % m
        s.add(c)
    return len(s)


def A348339(n):
    m, s = 10**n, set()
    for k in range(m):
        c, k2, kset = 0, k, set()
        while k2 not in kset:
            kset.add(k2)
            c += 1
            k2 = k2 * k2 % m
        s.add(c)
    return len(s)


def A260355_T(n, k):  # compute T(n, k)
    if k == 1:
        return n * (n + 1) // 2
    ntuple, count = tuple(range(1, n + 1)), n ** (k + 1)
    for s in combinations_with_replacement(permutations(ntuple, n), k - 2):
        t = list(ntuple)
        for d in s:
            for i in range(n):
                t[i] *= d[i]
        t.sort()
        v = 0
        for i in range(n):
            v += (n - i) * t[i]
        if v < count:
            count = v
    return count


def A219032(n):
    s = str(n * n)
    m = len(s)
    return len(
        set(
            filter(
                lambda x: integer_nthroot(x, 2)[1],
                (int(s[i:j]) for i in range(m) for j in range(i + 1, m + 1)),
            )
        )
    )


def A348467(n):
    s = str(factorial(n))
    m = len(s)
    return len(set(int(s[i:j]) for i in range(m) for j in range(i + 1, m + 1)))


def A120004(n):
    s = str(n)
    m = len(s)
    return len(set(int(s[i:j]) for i in range(m) for j in range(i + 1, m + 1)))


def A348428_gen(startvalue=1):  # generator of terms
    for n in count(max(startvalue, 1)):
        s = [int(d) for d in str(n)]
        m = len(s)
        if n == Matrix(m, m, lambda i, j: s[(i + j) % m]).det():
            yield n


def A306853_gen(startvalue=1):  # generator of terms
    for n in count(max(startvalue, 1)):
        s = [int(d) for d in str(n)]
        m = len(s)
        if n == Matrix(m, m, lambda i, j: s[(i - j) % m]).per():
            yield n


def A219325_gen(startvalue=1):  # generator of terms
    for n in count(max(startvalue, 1)):
        s = [int(d) for d in bin(n)[2:]]
        m = len(s)
        if n == Matrix(m, m, lambda i, j: s[(i - j) % m]).det():
            yield n


def A000108_gen():  # generator of terms
    yield 1
    yield 1
    m = 1
    for n in count(1):
        m = m * (4 * n + 2) // (n + 2)
        yield m


@lru_cache(maxsize=None)
def A000700(n):
    return (
        1
        if n == 0
        else sum(
            (-1) ** (k + 1)
            * A000700(n - k)
            * prod(
                (p ** (e + 1) - 1) // (p - 1) for p, e in factorint(k).items() if p > 2
            )
            for k in range(1, n + 1)
        )
        // n
    )


def A010815(n):
    m = isqrt(24 * n + 1)
    return (
        0
        if m**2 != 24 * n + 1
        else ((-1) ** ((m - 1) // 6) if m % 6 == 1 else (-1) ** ((m + 1) // 6))
    )


if sys.version_info >= (3, 10):

    def A000120(n):
        return n.bit_count()

else:

    def A000120(n):
        return bin(n).count("1")


def A000110_gen():  # generator of terms
    yield 1
    blist, b = (1,), 1
    while True:
        blist = list(accumulate(blist, initial=(b := blist[-1])))
        yield b


def A000110(n):
    return bell(n)


@lru_cache(maxsize=None)
def A000009(n):
    return (
        1
        if n == 0
        else A010815(n)
        + 2 * sum((-1) ** (k + 1) * A000009(n - k**2) for k in range(1, isqrt(n) + 1))
    )


def A007953(n):
    return sum(int(d) for d in str(n))


def A000984_gen():  # generator of terms
    yield 1
    m = 1
    for n in count(0):
        m = m * (4 * n + 2) // (n + 1)
        yield m


def A000578(n):
    return n**3


def A002808(n):
    return composite(n)


def A002808_gen():  # generator of terms
    n, m = 3, 5
    while True:
        for i in range(n + 1, m):
            yield i
        n, m = m, nextprime(m)


def A000961_gen():  # generator of terms
    yield 1
    for n in count(2):
        if len(factorint(n)) == 1:
            yield n


def A002113_gen():
    return pal10_gen()


def A003415(n):
    return sum((n * e // p for p, e in factorint(n).items())) if n > 1 else 0


def A000265(n):
    while not n % 2:
        n //= 2
    return n


def A001006_gen():  # generator of terms
    yield 1
    yield 1
    m, k = 1, 1
    for n in count(2):
        m, k = k, (k * (2 * n + 1) + (3 * n - 3) * m) // (n + 2)
        yield k


def A000166_gen():  # generator of terms
    m, x = 1, 1
    for n in count(0):
        x, m = x * n + m, -m
        yield x


def A004086(n):
    return int(str(n)[::-1])


def A001414(n):
    return sum(p * e for p, e in factorint(n).items())


def A002144_gen():
    for n in count(1):
        p = prime(n)
        if not (p - 1) % 4:
            yield p


def A002182_gen():  # generator of terms
    r = 0
    for i in count(1):
        if (d := divisor_count(i)) > r:
            r = d
            yield i


def A001700(n):
    return comb(2 * n + 1, n + 1)


def A001700_gen():  # generator of terms
    b = 1
    for n in count(0):
        yield b
        b = b * (4 * n + 6) // (n + 2)


def A003418(n):
    return prod(p ** integerlog(n, p) for p in sieve.primerange(1, n + 1))


def A000111_gen():  # generator of terms
    yield from (1, 1)
    blist = (0, 1)
    while True:
        yield (blist := tuple(accumulate(reversed(blist), initial=0)))[-1]


def A014137_gen():
    return accumulate(A000108_gen())


def A014138_gen():
    return (x - 1 for x in A014137_gen())


def A349866_gen(startvalue=1):
    return filter(
        lambda m: sum(divisor_sigma(m) % d for d in divisors(m, generator=True)) == m,
        count(max(startvalue, 1)),
    )


def A005349_gen(startvalue=1):
    return filter(
        lambda n: not n % sum((int(d) for d in str(n))), count(max(startvalue, 1))
    )


def A002322(n):
    return reduced_totient(n)


def A006318_gen():  # generator of terms
    m, k = 1, 2
    yield m
    yield k
    for n in count(3):
        m, k = k, (k * (6 * n - 9) - (n - 3) * m) // n
        yield k


def A007913(n):
    return prod(p for p, e in factorint(n).items() if e % 2)


def A000178_gen():  # generator of terms
    yield 1
    n, m = 1, 1
    for i in count(1):
        m *= i
        n *= m
        yield n


def A010888(n):
    return 1 + (n - 1) % 9


def A000523(n):
    return n.bit_length() - 1


def A000583(n):
    return n**4


def A000593(n):
    return prod((p ** (e + 1) - 1) // (p - 1) for p, e in factorint(n).items() if p > 2)


def A064413_gen():  # generator of terms
    yield 1
    yield 2
    l, s, b = 2, 3, set()
    while True:
        i = s
        while True:
            if not i in b and gcd(i, l) > 1:
                yield i
                l = i
                b.add(i)
                while s in b:
                    b.remove(s)
                    s += 1
                break
            i += 1


def A006218(n):
    return 2 * sum(n // k for k in range(1, isqrt(n) + 1)) - isqrt(n) ** 2


def A001694_gen(startvalue=1):
    return filter(
        lambda n: n == 1 or min(factorint(n).values()) > 1, count(max(startvalue, 1))
    )


def A019565(n):
    return (
        prod(prime(i + 1) for i, v in enumerate(bin(n)[:1:-1]) if v == "1")
        if n > 0
        else 1
    )


def A006882(n):
    return factorial2(n)


if sys.version_info >= (3, 10):

    def A005187(n):
        return 2 * n - n.bit_count()

else:

    def A005187(n):
        return 2 * n - bin(n).count("1")


def A001003_gen():  # generator of terms
    m, k = 1, 1
    yield m
    yield k
    for n in count(3):
        m, k = k, (k * (6 * n - 9) - (n - 3) * m) // n
        yield k


def A005836(n):
    return int(format(n - 1, "b"), 3)


def A002496_gen():
    return filter(
        isprime, (n + 1 for n in accumulate(count(0), lambda x, y: x + 2 * y - 1))
    )


def A052382_gen(startvalue=1):
    return filter(lambda n: "0" not in str(n), count(max(startvalue, 1)))


def A003714(n):
    tlist, s = [1, 2], 0
    while tlist[-1] + tlist[-2] <= n:
        tlist.append(tlist[-1] + tlist[-2])
    for d in tlist[::-1]:
        s *= 2
        if d <= n:
            s += 1
            n -= d
    return s


def A026741(n):
    return n if n % 2 else n // 2


def A006567_gen():
    return filter(
        lambda p: str(p) != str(p)[::-1] and isprime(int(str(p)[::-1])),
        (prime(n) for n in count(1)),
    )


def A006370(n):
    q, r = divmod(n, 2)
    return 3 * n + 1 if r else q


def A151800(n):
    return nextprime(n)


def A051903(n):
    return max(factorint(n).values()) if n > 1 else 0


def A001850_gen():  # generator of terms
    m, k = 1, 3
    yield m
    yield k
    for n in count(2):
        m, k = k, (k * (6 * n - 3) - (n - 1) * m) // n
        yield k


def A002293(n):
    return comb(4 * n, n) // (3 * n + 1)


def A002293_gen():  # generator of terms
    m = 1
    yield m
    for n in count(0):
        m = (
            m
            * 4
            * (4 * n + 3)
            * (4 * n + 2)
            * (4 * n + 1)
            // ((3 * n + 2) * (3 * n + 3) * (3 * n + 4))
        )
        yield m


def A098550_gen():  # generator of terms
    yield from [1, 2, 3]
    l1, l2, s, b = 3, 2, 4, set()
    while True:
        i = s
        while True:
            if not i in b and gcd(i, l1) == 1 and gcd(i, l2) > 1:
                yield i
                l2, l1 = l1, i
                b.add(i)
                while s in b:
                    b.remove(s)
                    s += 1
                break
            i += 1


def A001220_gen():
    return filter(lambda p: pow(2, p - 1, p * p) == 1, (prime(n) for n in count(1)))


def A047999_T(n, k):
    return int(not ~n & k)


@lru_cache(maxsize=None)
def A001175(n):
    if n == 1:
        return 1
    f = factorint(n)
    if len(f) > 1:
        return lcm(*(A001175(a ** f[a]) for a in f))
    else:
        k, x = 1, [1, 1]
        while x != [0, 1]:
            k += 1
            x = [x[1], (x[0] + x[1]) % n]
        return k


def A066272(n):
    return (
        len([d for d in divisors(2 * n) if n > d >= 2 and n % d])
        + len([d for d in divisors(2 * n - 1) if n > d >= 2 and n % d])
        + len([d for d in divisors(2 * n + 1) if n > d >= 2 and n % d])
    )


@lru_cache(maxsize=None)
def A002321(n):
    if n == 0:
        return 0
    c, j = n, 2
    k1 = n // j
    while k1 > 1:
        j2 = n // k1 + 1
        c += (j2 - j) * A002321(k1)
        j, k1 = j2, n // j2
    return j - c


def A007376_gen():
    return (int(d) for n in count(0) for d in str(n))


def A054632_gen():
    return accumulate(A007376_gen())


def A127353_gen():
    return islice(A007376_gen(), 2, None, 2)


def A127050_gen():
    return islice(A007376_gen(), 1, None, 2)


def A127950_gen():
    return islice(A007376_gen(), 2, None, 8)


def A347345_gen():
    return filter(
        lambda k: set(str(k * (k + 1) // 2)) <= {"1", "3", "5", "7", "9"},
        (int("".join(d)) for l in count(1) for d in product("13579", repeat=l)),
    )


def A132739(n):
    a, b = divmod(n, 5)
    while b == 0:
        a, b = divmod(a, 5)
    return 5 * a + b


def A349487(n):
    a, b = divmod(n * n - 25, 5)
    while b == 0:
        a, b = divmod(a, 5)
    return 5 * a + b


def A349791(n):
    b = primepi(n**2) + primepi((n + 1) ** 2) + 1
    return (prime(b // 2) + prime((b + 1) // 2)) // 2 if b % 2 else prime(b // 2)


def A000188(n):
    return isqrt(n // numbercore(n))


def A020449_gen():
    return filter(isprime, (int(format(n, "b")) for n in count(1)))


def A033676(n):
    d = divisors(n)
    return d[(len(d) - 1) // 2]


def A047994(n):
    return prod(p**e - 1 for p, e in factorint(n).items())


def d(n, m):
    return not n % m


def A007678(n):
    return (
        1176 * d(n, 12) * n
        - 3744 * d(n, 120) * n
        + 1536 * d(n, 18) * n
        - d(n, 2) * (5 * n**3 - 42 * n**2 + 40 * n + 48)
        - 2304 * d(n, 210) * n
        + 912 * d(n, 24) * n
        - 1728 * d(n, 30) * n
        - 36 * d(n, 4) * n
        - 2400 * d(n, 42) * n
        - 4 * d(n, 6) * n * (53 * n - 310)
        - 9120 * d(n, 60) * n
        - 3744 * d(n, 84) * n
        - 2304 * d(n, 90) * n
        + 2 * n**4
        - 12 * n**3
        + 46 * n**2
        - 84 * n
    ) // 48 + 1


def A063990_gen(startvalue=2):
    return filter(
        lambda n: divisor_sigma(n) - 2 * n
        and not divisor_sigma(divisor_sigma(n) - n) - divisor_sigma(n),
        count(max(startvalue, 2)),
    )


def A051674(n):
    return prime(n) ** prime(n)


def A001951(n):
    return isqrt(2 * n**2)


def A000587_gen():  # generator of terms
    yield 1
    yield -1
    blist, b = [1], -1
    while True:
        blist = list(accumulate([b] + blist))
        b = -blist[-1]
        yield b


def A003132(n):
    return sum(int(d) ** 2 for d in str(n))


def A003601_gen(startvalue=1):
    return filter(
        lambda n: not sum(divisors(n)) % divisor_count(n), count(max(startvalue, 1))
    )


@lru_cache(maxsize=None)
def A002088(n):  # based on second formula in A018805
    if n == 0:
        return 0
    c, j = 0, 2
    k1 = n // j
    while k1 > 1:
        j2 = n // k1 + 1
        c += (j2 - j) * (2 * A002088(k1) - 1)
        j, k1 = j2, n // j2
    return (n * (n - 1) - c + j) // 2


def A045917(n):
    return sum(1 for i in range(2, n + 1) if isprime(i) and isprime(2 * n - i))


def A019546_gen():
    return filter(
        lambda n: set(str(n)) <= {"2", "3", "5", "7"}, (prime(n) for n in count(1))
    )


def A011540_gen(startvalue=0):
    return filter(lambda n: "0" in str(n), count(max(startvalue, 0)))


def A014963(n):
    y = factorint(n)
    return list(y.keys())[0] if len(y) == 1 else 1


def A115004(n):
    return n**2 + sum(
        totient(i) * (n + 1 - i) * (2 * n + 2 - i) for i in range(2, n + 1)
    )


def A316524(n):
    fs = [primepi(p) for p in factorint(n, multiple=True)]
    return sum(fs[::2]) - sum(fs[1::2])


def A048050(n):
    return 0 if n == 1 else divisor_sigma(n) - n - 1


def A349806(n):
    for i in count(n**2 + (n % 2) + 1, 2):
        if len(fs := factorint(i)) == 2 == sum(fs.values()):
            return i - n**2


def A099610(n):
    for i in count(n**2 + (n % 2) + 1, 2):
        if len(fs := factorint(i)) == 2 == sum(fs.values()):
            return i


def A348762(n):
    a, b = divmod(n * n - 64, 2)
    while b == 0:
        a, b = divmod(a, 2)
    return 2 * a + b


def A069834(n):
    a, b = divmod(n * n + n, 2)
    while b == 0:
        a, b = divmod(a, 2)
    return 2 * a + b


def A328447(n):
    if n == 0:
        return 0
    s = str(n)
    l, s = len(s), "".join(sorted(s.replace("0", "")))
    return int(s[0] + "0" * (l - len(s)) + s[1:])


def A005188_gen():  # generator of terms
    for k in range(1, 40):
        a = tuple(i**k for i in range(10))
        yield from (
            x[0]
            for x in sorted(
                filter(
                    lambda x: x[0] > 0
                    and tuple(int(d) for d in sorted(str(x[0]))) == x[1],
                    (
                        (sum(map(lambda y: a[y], b)), b)
                        for b in combinations_with_replacement(range(10), k)
                    ),
                )
            )
        )


def A031443_gen():  # generator of terms
    for n in count(1):
        yield from (
            int("1" + "".join(p), 2)
            for p in multiset_permutations("0" * n + "1" * (n - 1))
        )


def A071925_gen():  # generator of terms
    for n in count(1):
        yield from (
            int("1" + "".join(p))
            for p in multiset_permutations("0" * n + "1" * (n - 1))
        )


def A349929_gen():  # generator of terms
    for n in count(3, 3):
        if (
            3 * gcd(comb(n * (n * (n + 6) - 6) + 2, 6 * n * (n - 1) + 3), n**3)
            == n**3
        ):
            yield n


def A349509(n):
    return n**3 // gcd(comb(n * (n * (n + 6) - 6) + 2, 6 * n * (n - 1) + 3), n**3)


def A099611(n):
    for i in count(n**2 - (n % 2) - 1, -2):
        fs = factorint(i)
        if len(fs) == 2 == sum(fs.values()):
            return i


def A349809(n):
    for i in count(n**2 - (n % 2) - 1, -2):
        fs = factorint(i)
        if len(fs) == 2 == sum(fs.values()):
            return n**2 - i


def A002982_gen(startvalue=1):
    return filter(lambda n: isprime(factorial(n) - 1), count(max(startvalue, 1)))


def A000058_gen():  # generator of terms
    yield (a := 2)
    while True:
        a = a * (a - 1) + 1
        yield a


def A151799(n):
    return prevprime(n)


def A000078_gen():  # generator of terms
    b = [0, 0, 0, 1]
    yield from b
    while True:
        yield (c := sum(b))
        b = b[1:] + [c]


def A002054(n):
    return comb(2 * n + 1, n - 1)


def A006720_gen():  # generator of terms
    b = [1, 1, 1, 1]
    yield from b
    while True:
        yield (c := (b[-1] * b[-3] + b[-2] ** 2) // b[-4])
        b = b[1:] + [c]


def A033677(n):
    return (lambda d: d[len(d) // 2])(divisors(n))


def A078972_gen():  # generator of terms
    for n in count(0):
        yield from sorted(
            prod(p)
            for p in combinations_with_replacement(
                sieve.primerange(10**n, 10 ** (n + 1)), 2
            )
        )


def A005493_gen():  # generator of terms
    blist, b = [1], 1
    while True:
        blist = list(accumulate([b] + blist))
        b = blist[-1]
        yield blist[-2]


def A188014(n):
    return (
        int((isqrt(5 * n**2) + n) // 2 - (isqrt(5 * (n - 4) ** 2) + n) // 2 - 4)
        if n > 3
        else 1 - (n % 2)
    )


def A348209(n):
    if n > 2 and bin(n).count("1") == 1:
        return 0
    k, m, n1, n2, n3 = 1, 2, n ** (n - 2), n ** (n - 1), n**n
    while m < n2:
        k += 1
        m = (2 * m) % n3
    while k <= n3:
        if m >= n1:
            a = ispandigital0(m, n)
            if a[0] and ((not a[1]) or m >= n2):
                return k
        k += 1
        m = (2 * m) % n3
    return 0


def A000978_gen():
    return filter(lambda p: isprime((2**p + 1) // 3), (prime(n) for n in count(2)))


def A007500_gen():
    return filter(lambda p: isprime(int(str(p)[::-1])), (prime(n) for n in count(1)))


def A010784_gen(startvalue=0):
    return filter(lambda n: len(set(str(n))) == len(str(n)), count(max(startvalue, 0)))


def A050278_gen():
    return (
        int(e + "".join(d))
        for e in "123456789"
        for d in permutations("0123456789".replace(e, ""), 9)
    )


def A071924(n):
    return primepi(
        max(
            primefactors(
                next(
                    islice(
                        (
                            int(e + "".join(d))
                            for e in "123456789"
                            for d in permutations("0123456789".replace(e, ""), 9)
                        ),
                        n - 1,
                        None,
                    )
                )
            )
        )
    )


def A071924_gen():
    return (
        primepi(max(primefactors(m)))
        for m in (
            int(e + "".join(d))
            for e in "123456789"
            for d in permutations("0123456789".replace(e, ""), 9)
        )
    )


def A000538(n):
    return n * (n**2 * (n * (6 * n + 15) + 10) - 1) // 30


def A330151(n):
    return 8 * n * (n**2 * (n * (6 * n + 15) + 10) - 1) // 15


def A259317(n):
    return n * (n * (n**2 * (n * (16 * n + 48) + 40) - 11) - 3) // 45


def A254640(n):
    return (
        n
        * (
            n
            * (
                n
                * (
                    n * (n * (n * (n * (n * (10 * n + 135) + 720) + 1890) + 2394) + 945)
                    - 640
                )
                - 450
            )
            + 36
        )
        // 5040
    )


def A002109_gen():
    return accumulate((k**k for k in count(0)), mul)


def A002109(n):
    return prod(k**k for k in range(1, n + 1))


@lru_cache(maxsize=None)
def A018805(n):  # based on second formula in A018805
    if n == 0:
        return 0
    c, j = 1, 2
    k1 = n // j
    while k1 > 1:
        j2 = n // k1 + 1
        c += (j2 - j) * A018805(k1)
        j, k1 = j2, n // j2
    return n * (n - 1) - c + j


def A023194_gen():  # generator of terms
    yield 2
    yield from filter(lambda n: isprime(divisor_sigma(n)), (n**2 for n in count(1)))


def A010057(n):
    return int(integer_nthroot(n, 3)[1])


def A001286(n):
    return (n - 1) * factorial(n) // 2


def A001286_gen():  # generator of terms
    b = 1
    yield b
    for n in count(2):
        b = b * n * (n + 1) // (n - 1)
        yield b


def A007602_gen(startvalue=1):
    return filter(
        lambda n: not ("0" in str(n) or n % prod(int(d) for d in str(n))),
        count(max(startvalue, 1)),
    )


def A001608_gen():  # generator of terms
    a, b, c = 3, 0, 2
    yield from (a, b, c)
    while True:
        a, b, c = b, c, a + b
        yield c


def A031971(n):
    return harmonic(n, -n)


def A348470(n):
    return 1 if n == 1 else min(primefactors(next(islice(A064413_gen(), n - 1, None))))


def A348470_gen():
    yield from (min(primefactors(n)) if n > 1 else 1 for n in A064413_gen())


def A349662(n):
    return 0 if n <= 1 else isqrt(n**3 - 1) - n


def A349993(n):
    return isqrt(n**3) - n + 1


def A349792_gen():  # generator of terms
    p1 = 0
    for n in count(1):
        p2 = primepi((n + 1) ** 2)
        b = p1 + p2 + 1
        if b % 2:
            p = prime(b // 2)
            q = nextprime(p)
            if p + q == 2 * n * (n + 1):
                yield n
        p1 = p2


def A308533_gen(startvalue=3):  # generator of terms
    for n in count(max(startvalue, 3)):
        a = antidivisors(n)
        if int("".join(str(s) for s in a)) % sum(a) == 0:
            yield n


def A130846(n):
    return int("".join(str(s) for s in antidivisors(n)))


def A003278(n):
    return int(format(n - 1, "b"), 3) + 1


def A000539(n):
    return n**2 * (n**2 * (n * (2 * n + 6) + 5) - 1) // 12


def A027868_gen():
    yield from [0] * 5
    p5 = 0
    for n in count(5, 5):
        p5 += multiplicity(5, n)
        yield from [p5] * 5


def A187950(n):
    return int((isqrt(5 * (n + 4) ** 2) + n) // 2 - (isqrt(5 * n**2) + n) // 2 - 4)


def A018900_gen():
    return (2**a + 2**b for a in count(1) for b in range(a))


@lru_cache(maxsize=None)
def A005728(n):  # based on second formula in A018805
    if n == 0:
        return 1
    c, j = -2, 2
    k1 = n // j
    while k1 > 1:
        j2 = n // k1 + 1
        c += (j2 - j) * (2 * A005728(k1) - 3)
        j, k1 = j2, n // j2
    return (n * (n - 1) - c + j) // 2


def A007629_gen(startvalue=10):  # generator of terms
    for n in count(max(startvalue, 10)):
        x = [int(d) for d in str(n)]
        y = sum(x)
        while y < n:
            x, y = x[1:] + [y], 2 * y - x[0]
        if y == n:
            yield n


def A007774_gen(startvalue=1):
    return filter(lambda n: len(primefactors(n)) == 2, count(max(startvalue, 1)))


def A009994_gen():  # generator of terms
    yield 0
    yield from (
        int("".join(i))
        for l in count(1)
        for i in combinations_with_replacement("123456789", l)
    )


def A004159(n):
    return sum(int(d) for d in str(n * n))


def A001952(n):
    return 2 * n + isqrt(2 * n**2)


def A005917(n):
    return n * (n * (4 * n - 6) + 4) - 1


def A031347(n):
    while n > 9:
        n = prod(int(d) for d in str(n))
    return n


def A069010(n):
    return sum(1 for d in bin(n)[2:].split("0") if len(d))


def A005823(n):
    return 2 * int(format(n - 1, "b"), 3)


def A014311_gen():
    return (
        2**a + 2**b + 2**c
        for a in count(2)
        for b in range(1, a)
        for c in range(b)
    )


def A349783(n):
    return sum(abs(stirling(2 * n, j, kind=1)) for j in range(n + 1))


def A011971_gen():  # generator of terms
    blist = [1]
    yield 1
    while True:
        b = blist[-1]
        blist = list(accumulate([b] + blist))
        yield from blist


def A046936_gen():  # generator of terms
    yield 0
    blist = [1, 1]
    yield from blist
    while True:
        b = blist[-1]
        blist = list(accumulate([b] + blist))
        yield from blist


def A349960(n):
    if n <= 2:
        return 3 - n
    a, b = "", ""
    for i in count(1, 2):
        a += str(i)
        b += str(i + 1)
        ai, bi = int(a), int(b)
        if len(a) + n - 2 == len(b):
            return bi // ai
        m = 10 ** (n - 2 - len(b) + len(a))
        lb = bi * m // (ai + 1)
        ub = (bi + 1) * m // ai
        if lb == ub:
            return lb


def A349958(n):
    for j in range(n + 1):
        for k in range(j + 1):
            if comb(j, k) % n == 0:
                return j


def A045918(n):
    return int(
        "".join(
            [str(len(m.group(0))) + m.group(0)[0] for m in finditer(r"(\d)\1*", str(n))]
        )
    )


def A001602(n):
    a, b, i, p = 0, 1, 1, prime(n)
    while b % p:
        a, b, i = b, (a + b) % p, i + 1
    return i


def A014577(n):
    s = bin(n + 1)[2:]
    m = len(s)
    i = s[::-1].find("1")
    return 1 - int(s[m - i - 2]) if m - i - 2 >= 0 else 1


def A081145_gen():  # generator of terms
    yield from [1, 2]
    l, s, b1, b2 = 2, 3, set(), set([1])
    for n in count(3):
        i = s
        while True:
            m = abs(i - l)
            if not (i in b1 or m in b2):
                yield i
                b1.add(i)
                b2.add(m)
                l = i
                while s in b1:
                    b1.remove(s)
                    s += 1
                break
            i += 1


def A000127(n):
    return n * (n * (n * (n - 6) + 23) - 18) // 24 + 1


def A007407(n):
    return sum(Fraction(1, k**2) for k in range(1, n + 1)).denominator


def A039724(n):
    s, q = "", n
    while q >= 2 or q < 0:
        q, r = divmod(q, -2)
        if r < 0:
            q += 1
            r += 2
        s += str(r)
    return int(str(q) + s[::-1])


def A065855(n):
    return 0 if n < 4 else n - primepi(n) - 1


def A004290(n):
    if n > 0:
        for i in range(1, 2**n):
            x = int(bin(i)[2:])
            if not x % n:
                return x
    return 0


def A006521_gen(startvalue=1):
    return filter(lambda n: pow(2, n, n) == n - 1, count(max(startvalue, 1)))


def A124240_gen(startvalue=1):
    return filter(lambda n: n % reduced_totient(n) == 0, count(max(startvalue, 1)))


def A289257_gen(startvalue=1):
    return filter(
        lambda n: 2 * n % reduced_totient(2 * n) == 0 and pow(2, n, n) == n - 1,
        count(max(startvalue, 1)),
    )


def A306302(n):
    return 2 * n * (n + 1) + sum(
        totient(i) * (n + 1 - i) * (2 * n + 2 - i) for i in range(2, n + 1)
    )


def A307720_gen():  # generator of terms. Greedy algorithm
    yield 1
    c, b = Counter(), 1
    while True:
        k, kb = 1, b
        while c[kb] >= kb:
            k += 1
            kb += b
        c[kb] += 1
        b = k
        yield k


def A007569(n):
    return (
        2
        if n == 2
        else n
        * (
            42 * (not n % 12)
            - 144 * (not n % 120)
            + 60 * (not n % 18)
            - 96 * (not n % 210)
            + 35 * (not n % 24)
            - 38 * (not n % 30)
            - 82 * (not n % 42)
            - 330 * (not n % 60)
            - 144 * (not n % 84)
            - 96 * (not n % 90)
        )
        + (
            n**4
            - 6 * n**3
            + 11 * n**2
            + 18 * n
            - (not n % 2) * (5 * n**3 - 45 * n**2 + 70 * n - 24)
            - 36 * (not n % 4) * n
            - 4 * (not n % 6) * n * (45 * n - 262)
        )
        // 24
    )


def A003401_gen(startvalue=1):
    return filter(
        lambda n: format(totient(n), "b").count("1") == 1, count(max(startvalue, 1))
    )


def A014127_gen():
    return filter(lambda p: pow(3, p - 1, p * p) == 1, (prime(n) for n in count(1)))


def A031346(n):
    mp = 0
    while n > 9:
        n = prod(int(d) for d in str(n))
        mp += 1
    return mp


def A029967_gen():
    return filter(lambda n: is_pal(n, 12), pal10_gen())


def A029968_gen():
    return filter(lambda n: is_pal(n, 13), pal10_gen())


def A049445_gen(startvalue=1):
    return filter(
        lambda n: not n % sum([int(d) for d in bin(n)[2:]]), count(max(startvalue, 1))
    )


def A348623_gen():  # generator of terms
    n = 1
    yield n
    while True:
        n = prod(q + 1 for p, q in factorint(n).items() if p > 2)
        yield n


def A349775_helper(n):  # generate sums of 2 subsets A,B with |A|,|B| >= 2 for A349775
    for l in range(2, n + 2):
        for a in combinations(range(n + 1), l):
            amax = max(a)
            bmax = min(amax, n - amax)
            for lb in range(2, bmax + 2):
                for b in combinations(range(bmax + 1), lb):
                    yield tuple(sorted(set(x + y for x in a for y in b)))


def A349775(n):
    c = Counter()
    for s in set(A349775_helper(n)):
        c[len(s)] += 1
    for i in range(n + 1, 1, -1):
        if c[i] < comb(n + 1, i):
            return i


def A002779_gen():
    return filter(lambda n: str(n) == str(n)[::-1], (n**2 for n in count(0)))


def A004185(n):
    return int("".join(sorted(str(n))).replace("0", "")) if n > 0 else 0


def A029731_gen():
    return filter(lambda n: is_pal(n, 16), pal10_gen())


def A029804_gen():
    return filter(lambda n: is_pal(n, 8), pal10_gen())


def A037861(n):
    return 2 * format(n, "b").count("0") - len(format(n, "b"))


def A056608(n):
    return min(factorint(composite(n)))


def A006261(n):
    return (n * (n * (n * (n * (n - 5) + 25) + 5) + 94) + 120) // 120


def A006561(n):
    return (
        0
        if n == 2
        else n
        * (
            42 * (not n % 12)
            - 144 * (not n % 120)
            + 60 * (not n % 18)
            - 96 * (not n % 210)
            + 35 * (not n % 24)
            - 38 * (not n % 30)
            - 82 * (not n % 42)
            - 330 * (not n % 60)
            - 144 * (not n % 84)
            - 96 * (not n % 90)
        )
        + (
            n**4
            - 6 * n**3
            + 11 * n**2
            - 6 * n
            - (not n % 2) * (5 * n**3 - 45 * n**2 + 70 * n - 24)
            - 36 * (not n % 4) * n
            - 4 * (not n % 6) * n * (45 * n - 262)
        )
        // 24
    )


def A001129_gen():  # generator of terms
    r1, r2 = 1, 0
    yield r2
    yield r1
    while True:
        l, r2 = r1 + r2, r1
        r1 = int(str(l)[::-1])
        yield l


def A034838_gen():  # generator of terms
    for g in count(1):
        for n in product("123456789", repeat=g):
            s = "".join(n)
            m = int(s)
            if not any(m % int(d) for d in s):
                yield m


def A076479(n):
    return mobius(prod(primefactors(n)))


def A229037_gen():  # generator of terms
    blist = []
    for n in count(0):
        i, j, b = 1, 1, set()
        while n - 2 * i >= 0:
            b.add(2 * blist[n - i] - blist[n - 2 * i])
            i += 1
            while j in b:
                b.remove(j)
                j += 1
        blist.append(j)
        yield j


def A034709_gen(startvalue=1):
    return filter(lambda n: n % 10 and not n % (n % 10), count(max(startvalue, 1)))


def A051802(n):
    if n == 0:
        return 1
    while n > 9:
        n = prod(int(d) for d in str(n) if d != "0")
    return n


def A054977(n):
    return 1 if n else 2


def A084937_gen():  # generator of terms
    yield from [1, 2]
    l1, l2, s, b = 2, 1, 3, set()
    while True:
        i = s
        while True:
            if not i in b and gcd(i, l1) == 1 and gcd(i, l2) == 1:
                yield i
                l2, l1 = l1, i
                b.add(i)
                while s in b:
                    b.remove(s)
                    s += 1
                break
            i += 1


def A099165_gen():
    return filter(lambda n: is_pal(n, 32), pal10_gen())


def A133500(n):
    s = str(n)
    l = len(s)
    m = int(s[-1]) if l % 2 else 1
    for i in range(0, l - 1, 2):
        m *= int(s[i]) ** int(s[i + 1])
    return m


def A023109(n):
    if n > 0:
        k = 0
        while True:
            m = k
            for i in range(n):
                if str(m) == str(m)[::-1]:
                    break
                m += int(str(m)[::-1])
            else:
                if str(m) == str(m)[::-1]:
                    return k
            k += 1
    else:
        return 0


def A023330_gen():
    return filter(
        lambda p: all((isprime(2**m * (p + 1) - 1) for m in range(1, 6))),
        (prime(n) for n in count(1)),
    )


def A071321(n):
    fs = factorint(n, multiple=True)
    return sum(fs[::2]) - sum(fs[1::2])


def A290447(n):
    p, p2 = set(), set()
    for b, c, d in combinations(range(1, n), 3):
        e = b + d - c
        f1, f2, g = (
            Fraction(b * d, e),
            Fraction(b * d * (c - b) * (d - c), e**2),
            (n - 1) * e - 2 * b * d,
        )
        for i in range(n - d):
            if 2 * i * e < g:
                p2.add((i + f1, f2))
            elif 2 * i * e == g:
                p.add(f2)
            else:
                break
    return len(p) + 2 * len(p2)


def A000387_gen():  # generator of terms
    m, x = 1, 0
    for n in count(0):
        x, m = x * n + m * (n * (n - 1) // 2), -m
        yield x


def A003893_gen():  # generator of terms
    a, b, = (
        0,
        1,
    )
    yield a
    while True:
        a, b = b, (a + b) % 10
        yield a


def A051801(n):
    return prod(int(d) for d in str(n) if d != "0") if n > 0 else 1


def A001917(n):
    p = prime(n)
    return 1 if n == 2 else (p - 1) // n_order(2, p)


def A007540_gen():  # generator of terms
    for n in count(1):
        p, m = prime(n), 1
        p2 = p * p
        for i in range(2, p):
            m = (m * i) % p2
        if m == p2 - 1:
            yield p


def A027870(n):
    return str(2**n).count("0")


def A029955_gen():
    return pal_gen(9)


def A061910_gen(startvalue=1):
    return filter(
        lambda n: is_square(sum(int(d) for d in str(n * n))), count(max(startvalue, 1))
    )


def A006721_gen():  # generator of terms
    blist = [1, 1, 1, 1, 1]
    yield from blist
    for n in count(5):
        blist = blist[1:] + [
            (blist[-1] * blist[-4] + blist[-2] * blist[-3]) // blist[-5]
        ]
        yield blist[-1]


def A087062_T(n, k):
    return lunar_mul(n, k)


def A007488_gen():
    return filter(lambda p: is_square(int(str(p)[::-1])), (prime(n) for n in count(1)))


def A059758_gen():  # generator of terms
    for l in count(1):
        for a in "1379":
            for b in "0123456789":
                if a != b and isprime(p := int((a + b) * l + a)):
                    yield p


def A175046(n):
    return int(
        "".join(
            d + "1" if "1" in d else d + "0"
            for d in split("(0+)|(1+)", bin(n)[2:])
            if d != "" and d != None
        ),
        2,
    )


def A228407_gen():  # generator of terms
    yield from [0, 11]
    l, s, b = Counter("11"), 1, {11}
    while True:
        i = s
        while True:
            if i not in b:
                li, o = Counter(str(i)), 0
                for d in (l + li).values():
                    if d % 2:
                        if o > 0:
                            break
                        o += 1
                else:
                    yield i
                    l = li
                    b.add(i)
                    while s in b:
                        b.remove(s)
                        s += 1
                    break
            i += 1


def A317081(n):
    if n == 0:
        return 1
    c = 0
    for d in partitions(n):
        s = set(d.values())
        if len(s) == max(s):
            c += 1
    return c


def A000979_gen():
    return filter(isprime, ((2 ** prime(n) + 1) // 3 for n in count(2)))


def A004094(n):
    return int(str(2**n)[::-1])


def A029954_gen():
    return pal_gen(7)


def A036691(n):
    return factorial(composite(n)) // primorial(primepi(composite(n))) if n > 0 else 1


def A054377_gen(startvalue=2):
    return filter(
        lambda n: sum(n / p for p in primefactors(n)) + 1 == n,
        count(max(startvalue, 2)),
    )


def A227349(n):
    return prod(len(d) for d in split("0+", bin(n)[2:]) if d) if n > 0 else 1


def A000540(n):
    return n * (n**2 * (n**2 * (n * (6 * n + 21) + 21) - 7) + 1) // 42


def A034947(n):
    s = bin(n)[2:]
    m = len(s)
    i = s[::-1].find("1")
    return 1 - 2 * int(s[m - i - 2]) if m - i - 2 >= 0 else 1


def A049060(n):
    return prod((p ** (e + 1) - 2 * p + 1) // (p - 1) for p, e in factorint(n).items())


def A057890_gen(startvalue=0):
    return filter(
        lambda n: bin(n)[2:].rstrip("0") == bin(n)[2:].rstrip("0")[::-1],
        count(max(startvalue, 0)),
    )


@lru_cache(maxsize=None)
def A015614(n):  # based on second formula in A018805
    if n == 0:
        return -1
    c, j = 2, 2
    k1 = n // j
    while k1 > 1:
        j2 = n // k1 + 1
        c += (j2 - j) * (2 * A015614(k1) + 1)
        j, k1 = j2, n // j2
    return (n * (n - 1) - c + j) // 2


def A045875(n):
    l, x = [str(d) * n for d in range(10)], 1
    for m in count(0):
        s = str(x)
        for k in l:
            if k in s:
                return m
        x *= 2


def A080670(n):
    return (
        1
        if n == 1
        else int(
            "".join([str(y) for x in sorted(factorint(n).items()) for y in x if y != 1])
        )
    )


def A006590(n):
    return (lambda m: n + 2 * sum((n - 1) // k for k in range(1, m + 1)) - m * m)(
        isqrt(n - 1)
    )


def A006794_gen():  # generator of terms
    p, q = 2, 2
    while True:
        if isprime(q - 1):
            yield p
        p = nextprime(p)
        q *= p


def A036229(n):
    k, r, m = (10**n - 1) // 9, 2**n - 1, 0
    while m <= r:
        t = k + int(bin(m)[2:])
        if isprime(t):
            return t
        m += 1
    return -1


def A047842(n):
    s, x = "", str(n)
    for i in range(10):
        y = str(i)
        c = str(x.count(y))
        if c != "0":
            s += c + y
    return int(s)


def A233466_gen(startvalue=1):
    return filter(
        lambda n: 2 * totient(n) == n - 5,
        count(max(startvalue + 1 - startvalue % 2, 1), 2),
    )


def A078971_gen():  # generator of terms
    for t in count(0):
        yield (2 ** (2 * t) - 1) // 3
        yield from ((2 ** (2 * t + 1) + 2 ** (2 * j + 1) - 1) // 3 for j in range(t))


def A048054(n):
    return len(
        [p for p in primerange(10 ** (n - 1), 10**n) if isprime(int(str(p)[::-1]))]
    )


def A059729(n):
    s = [int(d) for d in str(n)]
    l = len(s)
    t = [0] * (2 * l - 1)
    for i in range(l):
        for j in range(l):
            t[i + j] = (t[i + j] + s[i] * s[j]) % 10
    return int("".join(str(d) for d in t))


if sys.version_info >= (3, 10):

    def A159918(n):
        return n * n.bit_count()

else:

    def A159918(n):
        return bin(n * n).count("1")


def A061712(n):
    l, k = n - 1, 2**n
    while True:
        for d in combinations(range(l - 1, -1, -1), l - n + 1):
            m = k - 1 - sum(2 ** (e) for e in d)
            if isprime(m):
                return m
        l += 1
        k *= 2


def A110566(n):
    return lcm([k for k in range(1, n + 1)]) // harmonic(n).q


def A256630_gen():  # generator of terms
    for l in count(0):
        for a in ("1", "2", "3", "4"):
            for b in product("01234", repeat=l):
                for c in ("0", "1", "2"):
                    s = a + "".join(b) + c
                    if "0" in s and "4" in s:
                        n = int(s)
                        s2 = set(str(n**2))
                        if {"0", "4"} <= s2 <= {"0", "1", "2", "3", "4"}:
                            yield n


def A007608(n):
    s, q = "", n
    while q >= 4 or q < 0:
        q, r = divmod(q, -4)
        if r < 0:
            q += 1
            r += 4
        s += str(r)
    return int(str(q) + s[::-1])


def A000139_gen():  # generator of terms
    b = 2
    yield b
    for n in count(1):
        b = 3 * (3 * n - 2) * (3 * n - 1) * b // (2 * n + 2) // (2 * n + 1)
        yield b


def A000139(n):
    return 2 if n == 0 else 2 * comb(3 * n, n - 1) // n // (n + 1)


def A065197_gen(startvalue=1):
    return filter(
        lambda n: n
        == reduce(lambda m, k: m + (k if (m // k) % 2 else -k), range(n, 1, -1), n),
        count(max(startvalue, 1)),
    )


def A014847_gen():  # generator of terms
    b = 1
    for n in count(1):
        if not b % n:
            yield n
        b = b * (4 * n + 2) // (n + 2)


def A050486(n):
    return (2 * n + 7) * comb(n + 6, 6) // 7


def A053347(n):
    return (n + 4) * comb(n + 7, 7) // 4


def A057147(n):
    return n * sum(int(d) for d in str(n))


def A063655(n):
    d = divisors(n)
    l = len(d)
    return d[(l - 1) // 2] + d[l // 2]


def A074832_gen():
    return filter(
        lambda p: isprime(int(bin(p)[:1:-1], 2)), (prime(n) for n in count(1))
    )


def A175498_gen():  # generator of terms
    yield from [1, 2]
    l, s, b1, b2 = 2, 3, set(), {1}
    for n in count(3):
        i = s
        while True:
            if not (i in b1 or i - l in b2):
                yield i
                b1.add(i)
                b2.add(i - l)
                l = i
                while s in b1:
                    b1.remove(s)
                    s += 1
                break
            i += 1


def A000475_gen():  # generator of terms
    m, x = 1, 0
    for n in count(4):
        x, m = x * n + m * comb(n, 4), -m
        yield x


def A003684(n):
    return len(
        [
            p
            for p in primerange(10 ** (n - 1), 10**n)
            if len(set(str(p))) == len(str(p)) and isprime(int(str(p)[::-1]))
        ]
    )


def A007497_gen():
    return accumulate(repeat(2), lambda x, _: divisor_sigma(x))


def A031877_gen():  # generator of terms
    for n in count(1):
        if n % 10:
            s1 = str(n)
            s2 = s1[::-1]
            if s1 != s2 and not n % int(s2):
                yield n


def A038189(n):
    s = bin(n)[2:]
    m = len(s)
    i = s[::-1].find("1")
    return int(s[m - i - 2]) if m - i - 2 >= 0 else 0


@lru_cache(maxsize=None)
def A071778(n):
    if n == 0:
        return 0
    c, j = 1, 2
    k1 = n // j
    while k1 > 1:
        j2 = n // k1 + 1
        c += (j2 - j) * A071778(k1)
        j, k1 = j2, n // j2
    return n * (n**2 - 1) - c + j


def A078241(n):
    if n > 0:
        for i in range(1, 2**n):
            x = 2 * int(bin(i)[2:])
            if not x % n:
                return x
    return 0


def A161710(n):
    return (
        n
        * (
            n * (n * (n * (n * (n * (154 - 6 * n) - 1533) + 7525) - 18879) + 22561)
            - 7302
        )
        // 2520
        + 1
    )


def A161713(n):
    return n * (n * (n * (n * (15 - n) - 65) + 125) - 34) // 40 + 1


def A250408_gen():
    return filter(lambda n: is_pal(n, 20), pal10_gen())


def A345957(n):
    if n == 1:
        return 1
    fs = factorint(n, multiple=True)
    q, r = divmod(len(fs), 2)
    return 0 if r else len(list(multiset_combinations(fs, q)))


def A004520(n):
    return int("".join(str(2 * int(d) % 10) for d in str(n)))


def A005807_gen():  # generator of terms
    b = 2
    yield b
    for n in count(0):
        b = b * (4 * n + 2) * (5 * n + 9) // ((n + 3) * (5 * n + 4))
        yield b


def A014707(n):
    s = bin(n + 1)[2:]
    m = len(s)
    i = s[::-1].find("1")
    return int(s[m - i - 2]) if m - i - 2 >= 0 else 0


def A031423_gen(startvalue=1):  # generator of terms
    for n in count(max(startvalue, 1)):
        cf = continued_fraction_periodic(0, 1, n)
        if (
            len(cf) > 1
            and len(cf[1]) > 1
            and len(cf[1]) % 2
            and cf[1][len(cf[1]) // 2] == 10
        ):
            yield n


def A114043(n):
    return (
        4 * n**2
        - 6 * n
        + 3
        + 2 * sum(totient(i) * (n - i) * (2 * n - i) for i in range(2, n))
    )


def A249156_gen():
    return filter(lambda n: is_pal(n, 7), pal_gen(5))


def A250410_gen():
    return filter(lambda n: is_pal(n, 25), pal10_gen())


def A000449_gen():  # generator of terms
    m, x = 1, 0
    for n in count(3):
        x, m = x * n + m * (n * (n - 1) * (n - 2) // 6), -m
        yield x


def A000541(n):
    return n**2 * (n**2 * (n**2 * (n * (3 * n + 12) + 14) - 7) + 2) // 24


def A001287(n):
    return comb(n, 10)


def A022842(n):
    return isqrt(8 * n**2)


def A031286(n):
    ap = 0
    while n > 9:
        n = sum(int(d) for d in str(n))
        ap += 1
    return ap


def A055165(n):
    return sum(1 for s in product([0, 1], repeat=n**2) if Matrix(n, n, s).det() != 0)


def A145768(n):
    return reduce(xor, (x**2 for x in range(n + 1)))


def A145829_gen():  # generator of terms
    m = 0
    for n in count(1):
        m ^= n**2
        a, b = integer_nthroot(m, 2)
        if b:
            yield a


def A249155_gen():
    return filter(lambda n: is_pal(n, 15), pal_gen(6))


def A145828_gen():  # generator of terms
    m = 0
    for n in count(0):
        m ^= n**2
        if isqrt(m) ** 2 == m:
            yield m


def A193232(n):
    return reduce(xor, (x * (x + 1) for x in range(n + 1))) // 2


def A062700_gen():  # generator of terms
    yield 3
    yield from filter(isprime, (divisor_sigma(d**2) for d in count(1)))


def A065710(n):
    return str(2**n).count("2")


def A215732(n):
    l, x = [str(d) * n for d in range(10)], 1
    while True:
        s = str(x)
        for k in range(10):
            if l[k] in s:
                return k
        x *= 2


def A260343_gen(startvalue=2):
    return filter(
        lambda n: isprime(
            intbase(list(range(1, n)) + [1, 0] + list(range(n - 1, 0, -1)), n)
        ),
        count(max(startvalue, 2)),
    )


def A320486(n):
    return int("0" + "".join(d if str(n).count(d) == 1 else "" for d in str(n)))


def A002708_gen():  # generator of terms
    a, b = 1, 1
    for n in count(1):
        yield a % n
        a, b = b, a + b


def A003098_gen():
    return filter(
        lambda m: str(m) == str(m)[::-1], (n * (n + 1) // 2 for n in count(0))
    )


def A005001_gen():  # generator of terms
    yield from [0, 1, 2]
    blist, a, b = [1], 2, 1
    while True:
        blist = list(accumulate([b] + blist))
        b = blist[-1]
        a += b
        yield a


def A006533(n):
    return (
        1176 * (not n % 12) * n
        - 3744 * (not n % 120) * n
        + 1536 * (not n % 18) * n
        - (not n % 2) * (5 * n**3 - 42 * n**2 + 40 * n + 48)
        - 2304 * (not n % 210) * n
        + 912 * (not n % 24) * n
        - 1728 * (not n % 30) * n
        - 36 * (not n % 4) * n
        - 2400 * (not n % 42) * n
        - 4 * (not n % 6) * n * (53 * n - 310)
        - 9120 * (not n % 60) * n
        - 3744 * (not n % 84) * n
        - 2304 * (not n % 90) * n
        + 2 * n**4
        - 12 * n**3
        + 46 * n**2
        - 36 * n
    ) // 48 + 1


def A018796(n):
    if n == 0:
        return 0
    else:
        d, nd = 1, n
        while True:
            x = (isqrt(nd - 1) + 1) ** 2
            if x < nd + d:
                return int(x)
            d *= 10
            nd *= 10


def A027611(n):
    return (n * harmonic(n)).q


def A037015_gen(startvalue=0):  # generator of terms
    for n in count(max(startvalue, 0)):
        c = None
        for x, y in groupby(bin(n)[2:]):
            z = len(list(y))
            if c != None and z >= c:
                break
            c = z
        else:
            yield n


def A038003_gen():  # generator of terms
    yield from [1, 1]
    c, s = 1, 3
    for n in count(2):
        c = (c * (4 * n - 2)) // (n + 1)
        if n == s:
            yield c
            s = 2 * s + 1


def A050782(n):
    if n % 10:
        for i in islice(pal10_gen(), 1, None):
            q, r = divmod(i, n)
            if not r:
                return q
    else:
        return 0


def A073327(n):
    return sum(ord(d) - 96 for d in sub(r"\sand\s|[^a-z]", "", num2words(n)))


def A088177():  # generator of terms
    yield 1
    yield 1
    p, a = {1}, 1
    while True:
        n = 1
        while n * a in p:
            n += 1
        p.add(n * a)
        a = n
        yield n


def A096497(n):
    return nextprime((10**n - 1) // 9)


def A101337(n):
    s = str(n)
    l = len(s)
    return sum(int(d) ** l for d in s)


def A141255(n):
    return 2 * (n - 1) * (2 * n - 1) + 2 * sum(
        totient(i) * (n - i) * (2 * n - i) for i in range(2, n)
    )


def A176774(n):
    k = (isqrt(8 * n + 1) - 1) // 2
    while k >= 2:
        a, b = divmod(2 * (k * (k - 2) + n), k * (k - 1))
        if not b:
            return a
        k -= 1


def A002131(n):
    return prod(
        p**e if p == 2 else (p ** (e + 1) - 1) // (p - 1)
        for p, e in factorint(n).items()
    )


def A024916(n):
    return sum(k * (n // k) for k in range(1, n + 1))


def A350146(n):
    return sum(k * (n // k) for k in range(1, n + 1)) - sum(
        k * (n // 2 // k) for k in range(1, n // 2 + 1)
    )


def A252867_gen():  # generator of terms
    yield from [0, 1, 2]
    l1, l2, s, b = 2, 1, 3, set()
    while True:
        i = s
        while True:
            if not (i in b or i & l1) and i & l2:
                yield i
                l2, l1 = l1, i
                b.add(i)
                while s in b:
                    b.remove(s)
                    s += 1
                break
            i += 1


def A002419(n):
    return (6 * n - 2) * comb(n + 2, 3) // 4


def A015950_gen(startvalue=1):
    return filter(lambda n: pow(4, n, n) == n - 1, count(max(startvalue, 1)))


def A016069_gen():  # generator of terms
    for g in count(2):
        n, blist = 2**g - 1, []
        for x in combinations("0123456789", 2):
            for i, y in enumerate(product(x, repeat=g)):
                if i > 0 and i < n and y[0] != "0":
                    z = int("".join(y))
                    a, b = integer_nthroot(z, 2)
                    if b:
                        blist.append(a)
        yield from sorted(blist)


def A350092(n):
    return floor((1 + sqrt(5) / 2) ** n)


def A014217(n):
    return floor(((1 + sqrt(5)) / 2) ** n)


def A350174_gen():
    return chain.from_iterable([k] * prime(k + 1) for k in count(0))


def A350173(n):
    return prime(n) ** (n % 2 + 1)


def A350171(n):
    return prime(n) + n % 2


def A349425(n):
    if n % 10 == 0:
        return 0
    m, n1, n2 = n, 10**n, 10 ** (n - 1)
    while (k := pow(n, m, n1)) != m:
        m = k
    return k // n2


def A309081(n):
    return n + sum((1 if k % 2 else -1) * (n // k**2) for k in range(2, isqrt(n) + 1))


def A055882_gen():  # generator of terms
    yield from [1, 2]
    blist, b, n2 = [1], 1, 4
    while True:
        blist = list(accumulate([b] + blist))
        b = blist[-1]
        yield b * n2
        n2 *= 2


def A068679_gen():  # generator of terms
    for n in count(1):
        if isprime(10 * n + 1):
            s = str(n)
            for i in range(len(s)):
                if not isprime(int(s[:i] + "1" + s[i:])):
                    break
            else:
                yield n


def A082183(n):
    t = n * (n + 1)
    ds = divisors(t)
    for i in range(len(ds) // 2 - 2, -1, -1):
        x = ds[i]
        y = t // x
        a, b = divmod(y - x, 2)
        if b:
            return a
    return -1


def A098464_gen():  # generator of terms
    l, h = 1, Fraction(1, 1)
    for k in count(1):
        l = lcm(l, k)
        h += Fraction(1, k)
        if l == h.denominator:
            yield k


def A109812_gen():  # generator of terms
    yield 1
    l1, s, b = 1, 2, set()
    while True:
        i = s
        while True:
            if not (i in b or i & l1):
                yield i
                l1 = i
                b.add(i)
                while s in b:
                    b.remove(s)
                    s += 1
                break
            i += 1


def A132106(n):
    return (lambda m: 2 * (sum(n // k for k in range(1, m + 1))) + m * (1 - m) + 1)(
        isqrt(n)
    )


def A215727(n):
    l, x = [str(d) * n for d in range(10)], 1
    for m in count(0):
        s = str(x)
        for k in l:
            if k in s:
                return m
        x *= 3


def A000542(n):
    return (
        n
        * (n**2 * (n**2 * (n**2 * (n * (10 * n + 45) + 60) - 42) + 20) - 3)
        // 90
    )


def A002796_gen(startvalue=1):
    return filter(
        lambda n: all((d == "0" or n % int(d) == 0) for d in set(str(n))),
        count(max(startvalue, 1)),
    )


def A004167(n):
    return int(str(3**n)[::-1])


def A014312_gen():
    return (
        2**a + 2**b + 2**c + 2**d
        for a in count(3)
        for b in range(2, a)
        for c in range(1, b)
        for d in range(c)
    )


def A046732_gen():
    return filter(
        lambda p: len(str(p)) == len(set(str(p))) and isprime(int(str(p)[::-1])),
        (prime(n) for n in count(1)),
    )


def A050985(n):
    return 1 if n <= 1 else prod(p ** (e % 3) for p, e in factorint(n).items())


def A061242_gen():
    return filter(lambda p: not (p + 1) % 18, (prime(n) for n in count(1)))


def A061762(n):
    return sum(a := [int(d) for d in str(n)]) + prod(a)


def A219324_gen():  # generator of terms
    for n in count(1):
        s = [int(d) for d in str(n)]
        m = len(s)
        if n == Matrix(m, m, lambda i, j: s[(i - j) % m]).det():
            yield n


def A246544_gen():  # generator of terms
    for m in count(1):
        n = composite(m)
        x = divisors(n)
        x.pop()
        y = sum(x)
        while y < n:
            x, y = x[1:] + [y], 2 * y - x[0]
        if y == n:
            yield n


def A276037_gen():
    yield from (int("".join(d)) for l in count(1) for d in product("15", repeat=l))


def A290131(n):
    return 2 * (n - 1) ** 2 + sum(
        totient(i) * (n - i) * (2 * n - i) for i in range(2, n)
    )


def A317087_gen():  # generator of terms
    yield 1
    for n in count(1):
        d = factorint(n)
        k, l = sorted(d.keys()), len(d)
        if l > 0 and l == primepi(max(d)):
            for i in range(l // 2):
                if d[k[i]] != d[k[l - i - 1]]:
                    break
            else:
                yield n


def A332517(n):
    return sum(totient(d) * (n // d) ** n for d in divisors(n, generator=True))


def A006722_gen():  # generator of terms
    blist = [1] * 6
    yield from blist
    while True:
        blist = blist[1:] + [
            (blist[-1] * blist[-5] + blist[-2] * blist[-4] + blist[-3] ** 2)
            // blist[-6]
        ]
        yield blist[-1]


def A008863(n):
    return (
        n
        * (
            n
            * (
                n
                * (
                    n
                    * (
                        n
                        * (n * (n * (n * (n * (n - 35) + 600) - 5790) + 36813) - 140595)
                        + 408050
                    )
                    - 382060
                )
                + 1368936
            )
            + 2342880
        )
        // 3628800
        + 1
    )


def A011965_gen():  # generator of terms
    yield 1
    blist = [1, 2]
    while True:
        blist = list(accumulate([blist[-1]] + blist))
        yield blist[-3]


def A034302_gen():  # generator of terms
    yield from [23, 37, 53, 73]
    for l in count(1):
        for d in product("123456789", repeat=l):
            for e in product("1379", repeat=2):
                s = "".join(d + e)
                if isprime(int(s)):
                    for i in range(len(s)):
                        if not isprime(int(s[:i] + s[i + 1 :])):
                            break
                    else:
                        yield int(s)


def A036953_gen():
    return filter(isprime, (int(gmpy2digits(n, 3)) for n in count(0)))


def A054683_gen(startvalue=0):
    return filter(
        lambda i: not sum(int(d) for d in str(i)) % 2, count(max(startvalue, 0))
    )


def A064538(n):
    p, m = 2, n + 1
    while p <= (n + 2) // (2 + (n % 2)):
        if sum(d for d in sympydigits(n + 1, p)[1:]) >= p:
            m *= p
        p = nextprime(p)
    return m


def A066321(n):
    if n == 0:
        return 0
    else:
        s, q = "", n
        while q:
            q, r = c_divmod(q, -4)
            s += ("0000", "1000", "0011", "1011")[r]
        return int(s[::-1], 2)


@lru_cache(maxsize=None)
def A082540(n):
    if n == 0:
        return 0
    c, j = 1, 2
    k1 = n // j
    while k1 > 1:
        j2 = n // k1 + 1
        c += (j2 - j) * A082540(k1)
        j, k1 = j2, n // j2
    return n * (n**3 - 1) - c + j


def A087116(n):
    return sum(1 for d in bin(n)[2:].split("1") if len(d))


def A096825(n):
    fs = factorint(n)
    return len(list(multiset_combinations(fs, sum(fs.values()) // 2)))


@lru_cache(maxsize=None)
def A100448(n):
    if n == 0:
        return 0
    c, j = 2, 2
    k1 = n // j
    while k1 > 1:
        j2 = n // k1 + 1
        c += (j2 - j) * (6 * A100448(k1) + 1)
        j, k1 = j2, n // j2
    return (n * (n**2 - 1) - c + j) // 6


def A129135_gen():  # generator of terms
    m, x = 1, 0
    for n in count(5):
        x, m = x * n + m * comb(n, 5), -m
        yield x


def A187795(n):
    return sum(d for d in divisors(n, generator=True) if divisor_sigma(d) > 2 * d)


def A246660(n):
    return prod(factorial(len(d)) for d in split("0+", bin(n)[2:]) if d) if n > 0 else 1


def A256617_gen(startvalue=1):
    return filter(
        lambda n: len(plist := primefactors(n)) == 2
        and plist[1] == nextprime(plist[0]),
        count(max(startvalue, 1)),
    )


def A272369_gen():
    return filter(
        lambda n: all(
            (d in (1, 2, 4, 46) or not isprime(d + 1))
            for d in divisors(n, generator=True)
        ),
        count(92, 92),
    )


def A317086(n):
    if n > 3 and isprime(n):
        return 1
    else:
        c = 1
        for d in partitions(n, k=integer_nthroot(2 * n, 2)[0], m=n * 2 // 3):
            l = len(d)
            if l > 0:
                k = max(d)
                if l == k:
                    for i in range(k // 2):
                        if d[i + 1] != d[k - i]:
                            break
                    else:
                        c += 1
        return c


def A331757(n):
    return (
        8
        if n == 1
        else 2
        * (
            n * (n + 3)
            + sum(totient(i) * (n + 1 - i) * (n + 1 + i) for i in range(2, n // 2 + 1))
            + sum(
                totient(i) * (n + 1 - i) * (2 * n + 2 - i)
                for i in range(n // 2 + 1, n + 1)
            )
        )
    )


def A005351(n):
    s, q = "", n
    while q >= 2 or q < 0:
        q, r = divmod(q, -2)
        if r < 0:
            q += 1
            r += 2
        s += str(r)
    return int(str(q) + s[::-1], 2)


def A028909(n):
    return int("".join(sorted(str(2**n))))


def A028910(n):
    return int("".join(sorted(str(2**n), reverse=True)))


def A039723(n):
    s, q = "", n
    while q >= 10 or q < 0:
        q, r = divmod(q, -10)
        if r < 0:
            q += 1
            r += 10
        s += str(r)
    return int(str(q) + s[::-1])


def A055685_gen(startvalue=2):
    return filter(lambda n: pow(2, n, n - 1) == n - 2, count(max(startvalue, 2)))


def A065712(n):
    return str(2**n).count("1")


def A067388_gen():  # generator of terms
    p = 2
    q, r, s = p + 48, p + 96, p + 144
    while True:
        np = nextprime(p)
        if (
            np == q
            and isprime(r)
            and isprime(s)
            and nextprime(q) == r
            and nextprime(r) == s
        ):
            yield p
        p, q, r, s = np, np + 48, np + 96, np + 144


def A075101(n):
    return (Fraction(2**n) / n).numerator


@lru_cache(maxsize=None)
def A090025(n):
    if n == 0:
        return 0
    c, j = 1, 2
    k1 = n // j
    while k1 > 1:
        j2 = n // k1 + 1
        c += (j2 - j) * A090025(k1)
        j, k1 = j2, n // j2
    return (n + 1) ** 3 - c + 7 * (j - n - 1)


def A350153_gen():
    return filter(
        lambda p: isprime(p),
        (
            int(s)
            for n in count(1)
            for s in accumulate(
                str(d) for d in chain(range(1, n + 1), range(n - 1, 0, -1))
            )
        ),
    )


def A259937(n):
    return int("".join(str(d) for d in chain(range(1, n + 1), range(n, 0, -1))))


def A350233_gen(startvalue=1):
    return filter(
        lambda n: (m := int(str(n)[::-1])) % 5 and not m % 4,
        filter(lambda n: n % 4 and not n % 5, count(max(startvalue, 1))),
    )


def A350232_gen(startvalue=1):
    return filter(
        lambda n: (m := int(str(n)[::-1])) % 4 and not m % 5,
        filter(lambda n: n % 5 and not n % 4, count(max(startvalue, 1))),
    )


def A350228_gen():
    yield from (1, 0)
    b, bdict = 0, {1: (1,), 0: (2,)}
    for n in count(3):
        if len(l := bdict[b]) > 1:
            m = (n - 1 - l[-2]) * b
            if m in bdict:
                bdict[m] = (bdict[m][-1], n)
            else:
                bdict[m] = (n,)
            b = m
        else:
            bdict[1] = (bdict[1][-1], n)
            b = 1
        yield b


def A171918_gen():  # generator of terms
    yield 8
    b, bdict = 8, {8: (1,)}
    for n in count(2):
        if len(l := bdict[b]) > 1:
            b = n - 1 - l[-2]
        else:
            b = 0
        if b in bdict:
            bdict[b] = (bdict[b][-1], n)
        else:
            bdict[b] = (n,)
        yield b


def A171917_gen():  # generator of terms
    b, bdict = 7, {7: (1,)}
    for n in count(2):
        yield b
        if len(l := bdict[b]) > 1:
            b = n - 1 - l[-2]
        else:
            b = 0
        if b in bdict:
            bdict[b] = (bdict[b][-1], n)
        else:
            bdict[b] = (n,)


def A171916_gen():  # generator of terms
    b, bdict = 6, {6: (1,)}
    for n in count(2):
        yield b
        if len(l := bdict[b]) > 1:
            b = n - 1 - l[-2]
        else:
            b = 0
        if b in bdict:
            bdict[b] = (bdict[b][-1], n)
        else:
            bdict[b] = (n,)


def A171915_gen():  # generator of terms
    b, bdict = 5, {5: (1,)}
    for n in count(2):
        yield b
        if len(l := bdict[b]) > 1:
            b = n - 1 - l[-2]
        else:
            b = 0
        if b in bdict:
            bdict[b] = (bdict[b][-1], n)
        else:
            bdict[b] = (n,)


def A171914_gen():  # generator of terms
    b, bdict = 4, {4: (1,)}
    for n in count(2):
        yield b
        if len(l := bdict[b]) > 1:
            b = n - 1 - l[-2]
        else:
            b = 0
        if b in bdict:
            bdict[b] = (bdict[b][-1], n)
        else:
            bdict[b] = (n,)


def A171913_gen():  # generator of terms
    b, bdict = 3, {3: (1,)}
    for n in count(2):
        yield b
        if len(l := bdict[b]) > 1:
            b = n - 1 - l[-2]
        else:
            b = 0
        if b in bdict:
            bdict[b] = (bdict[b][-1], n)
        else:
            bdict[b] = (n,)


def A171912_gen():  # generator of terms
    b, bdict = 2, {2: (1,)}
    for n in count(2):
        yield b
        if len(l := bdict[b]) > 1:
            b = n - 1 - l[-2]
        else:
            b = 0
        if b in bdict:
            bdict[b] = (bdict[b][-1], n)
        else:
            bdict[b] = (n,)


def A171911_gen():  # generator of terms
    b, bdict = 1, {1: (1,)}
    for n in count(2):
        yield b
        if len(l := bdict[b]) > 1:
            b = n - 1 - l[-2]
        else:
            b = 0
        if b in bdict:
            bdict[b] = (bdict[b][-1], n)
        else:
            bdict[b] = (n,)


def A181391_gen():  # generator of terms
    b, bdict = 0, {0: (1,)}
    for n in count(2):
        yield b
        if len(l := bdict[b]) > 1:
            b = n - 1 - l[-2]
            if b in bdict:
                bdict[b] = (bdict[b][-1], n)
            else:
                bdict[b] = (n,)
        else:
            b = 0
            bdict[0] = (bdict[0][-1], n)


def A309363_gen():  # generator of terms
    b, bdict = 0, {0: (1,)}
    for n in count(2):
        yield b
        if len(l := bdict[b]) > 1:
            b = n - 1 - l[-2]
        else:
            b = 2
        if b in bdict:
            bdict[b] = (bdict[b][-1], n)
        else:
            bdict[b] = (n,)


def A092221_gen(startvalue=0):
    return filter(lambda n: not bernoulli(2 * n).p % 59, count(max(startvalue, 0)))


def A281502_gen(startvalue=0):
    return filter(lambda n: not bernoulli(2 * n).p % 691, count(max(startvalue, 0)))


def A100208_gen():  # generator of terms
    xset, a = {1}, 1
    yield a
    while True:
        a, b = 1, 1 + a**2
        while not isprime(b) or a in xset:
            b += 2 * a + 1
            a += 1
        xset.add(a)
        yield a


def A349731(n):
    return -1 if n == 0 else -((-n) ** n) * ff(Fraction(1, n), n)


def A109890_gen():  # generator of terms
    yield from [1, 2]
    s, y, b = 3, 3, set()
    while True:
        for i in divisors(s, generator=True):
            if i >= y and i not in b:
                yield i
                s += i
                b.add(i)
                while y in b:
                    b.remove(y)
                    y += 1
                break


def A110751_gen(startvalue=1):
    return filter(
        lambda n: primefactors(n) == primefactors(int(str(n)[::-1])),
        count(max(startvalue, 1)),
    )


def A112822(n):
    k, l, h = 1, 1, Fraction(1, 1)
    while l != h.denominator * (2 * n - 1):
        k += 1
        l = lcm(l, k)
        h += Fraction(1, k)
    return k


def A115005(n):
    return (n - 1) * (2 * n - 1) + sum(
        totient(i) * (n - i) * (2 * n - i) for i in range(2, n)
    )


def A115920_gen(startvalue=1):
    return filter(
        lambda n: sorted(str(divisor_sigma(n))) == sorted(str(n)),
        count(max(startvalue, 1)),
    )


def A115921_gen(startvalue=1):
    return filter(
        lambda n: sorted(str(totient(n))) == sorted(str(n)), count(max(startvalue, 1))
    )


def A153671_gen():  # generator of terms
    n, k, q = 101, 100, 0
    for m in count(1):
        r = n % k
        if r > q:
            q = r
            yield m
        n *= 101
        k *= 100
        q *= 100


def A215728(n):
    l, x = [str(d) * n for d in range(10)], 1
    for m in count(0):
        s = str(x)
        for k in l:
            if k in s:
                return m
        x *= 5


def A215729(n):
    l, x = [str(d) * n for d in range(10)], 1
    for m in count(0):
        s = str(x)
        for k in l:
            if k in s:
                return m
        x *= 6


def A215730(n):
    l, x = [str(d) * n for d in range(10)], 1
    for m in count(0):
        s = str(x)
        for k in l:
            if k in s:
                return m
        x *= 7


def A215733(n):
    l, x = [str(d) * n for d in range(10)], 1
    while True:
        s = str(x)
        for k in range(10):
            if l[k] in s:
                return k
        x *= 3


def A260273_gen():  # generator of terms
    yield 1
    a = 1
    while True:
        b, s = 1, format(a, "b")
        while format(b, "b") in s:
            b += 1
        a += b
        s = format(a, "b")
        yield a


def A331776(n):
    return (
        4
        if n == 1
        else 20 * n * (n - 1)
        + 4 * sum(totient(i) * (n + 1 - i) * (2 * n + 2 - i) for i in range(2, n + 1))
    )


def A003128_gen():  # generator of terms
    blist, a, b = [1], 1, 1
    while True:
        blist = list(accumulate([b] + blist))
        c = blist[-1]
        yield (c + a - 3 * b) // 2
        a, b = b, c


def A048701(n):
    return int((s := bin(n - 1)[2:]) + s[::-1], 2)


def A049479(n):
    return min(factorint(2**n - 1))


def A061040(n):
    return 9 * n**2 // gcd(n**2 - 9, 9 * n**2)


def A064614(n):
    return (
        prod((5 - p if 2 <= p <= 3 else p) ** e for p, e in factorint(n).items())
        if n > 1
        else n
    )


def A065715(n):
    return str(2**n).count("4")


def A065719(n):
    return str(2**n).count("8")


def A072960_gen():
    return chain(
        [0],
        (
            int(a + "".join(b))
            for l in count(0)
            for a in "3689"
            for b in product("03689", repeat=l)
        ),
    )


@lru_cache(maxsize=None)
def A100449(n):
    if n == 0:
        return 1
    c, j = 0, 2
    k1 = n // j
    while k1 > 1:
        j2 = n // k1 + 1
        c += (j2 - j) * ((A100449(k1) - 3) // 2)
        j, k1 = j2, n // j2
    return 2 * (n * (n - 1) - c + j) + 1


def A127936_gen(startvalue=1):
    return filter(lambda i: isprime(int("01" * i + "1", 2)), count(max(startvalue, 1)))


def A171901is_ok(n):
    s = str(n)
    return any(s[i] == s[i - 1] for i in range(1, len(s)))


def A171901_gen(startvalue=0):
    return filter(A171901is_ok, count(max(startvalue, 0)))


def A215731(n):
    l, x = [str(d) * n for d in range(10)], 1
    for m in count(0):
        s = str(x)
        for k in l:
            if k in s:
                return m
        x *= 11


def A215737(n):
    a, s = 1, tuple(str(i) * n for i in range(10))
    while True:
        a *= 11
        t = str(a)
        for i, x in enumerate(s):
            if x in t:
                return i


def A230625(n):
    return (
        1
        if n == 1
        else int(
            "".join(
                [bin(y)[2:] for x in sorted(factorint(n).items()) for y in x if y != 1]
            ),
            2,
        )
    )


def A237600_gen(startvalue=2):  # generator of terms
    n = max(nextprime(startvalue - 1), 2)
    while True:
        s = format(n, "x")
        for i in range(1, len(s)):
            if not is_prime(int(s[:-i], 16)):
                break
        else:
            yield n
        n = nextprime(n)


def A252648_gen():  # generator of terms
    yield 1
    for m in count(1):
        l, L, dm, xlist, q = 1, 1, [d**m for d in range(10)], [0], 9**m
        while l * q >= L:
            for c in combinations_with_replacement(range(1, 10), l):
                n = sum(dm[d] for d in c)
                if sorted(int(d) for d in str(n)) == [0] * (
                    len(str(n)) - len(c)
                ) + list(c):
                    xlist.append(n)
            l += 1
            L *= 10
        yield from sorted(xlist)


def A272695(n):
    return int((n * sin(n)).round())


def A000790(n):
    c = 4
    while pow(n, c, c) != (n % c) or isprime(c):
        c += 1
    return c


def A008281_gen():  # generator of terms
    blist = [1]
    while True:
        yield from blist
        blist = [0] + list(accumulate(reversed(blist)))


@lru_cache(maxsize=None)
def A015631(n):
    if n == 0:
        return 0
    c, j = 1, 2
    k1 = n // j
    while k1 > 1:
        j2 = n // k1 + 1
        c += (j2 - j) * A015631(k1)
        j, k1 = j2, n // j2
    return n * (n - 1) * (n + 4) // 6 - c + j


def A046447_gen():  # generator of terms
    yield 1
    m = 4
    while True:
        k = nextprime(m)
        for n in range(m, k):
            if (
                s := "".join([str(p) * e for p, e in sorted(factorint(n).items())])
            ) == s[::-1]:
                yield n
        m = k + 1


def A057708_gen():  # generator of terms
    m = 2
    for k in count(1):
        if isprime(int(str(m)[::-1])):
            yield k
        m *= 2


def A063454(n):
    ndict = {}
    for i in range(n):
        m = pow(i, 3, n)
        if m in ndict:
            ndict[m] += 1
        else:
            ndict[m] = 1
    count = 0
    for i in ndict:
        ni = ndict[i]
        for j in ndict:
            k = (i + j) % n
            if k in ndict:
                count += ni * ndict[j] * ndict[k]
    return count


def A350244_gen():
    yield 1
    k, b, bdict = 1, 0, {1: (1,), 0: (2,)}
    for n in count(3):
        if len(l := bdict[b]) > 1:
            m = (n - 1 - l[-2]) * b
            if m in bdict:
                bdict[m] = (bdict[m][-1], n)
            else:
                bdict[m] = (n,)
            b = m
        else:
            bdict[1] = (bdict[1][-1], n)
            b = 1
        if b > k:
            k = b
            yield n


def A069942_gen(startvalue=1):
    return filter(
        lambda n: sum(map(lambda x: int(str(x)[::-1]) if x < n else 0, divisors(n)))
        == int(str(n)[::-1]),
        count(max(startvalue, 1)),
    )


def A071869_gen():  # generator of terms
    p, q, r = 1, 2, 3
    for n in count(2):
        p, q, r = q, r, max(factorint(n + 2))
        if p < q < r:
            yield n


def A071870_gen():  # generator of terms
    p, q, r = 1, 2, 3
    for n in count(2):
        p, q, r = q, r, max(factorint(n + 2))
        if p > q > r:
            yield n


def A076197_gen():  # generator of terms
    g = 1
    for i in count(3, 2):
        g *= i
        if is_prime(g + 1024):
            yield i


@lru_cache(maxsize=None)
def A090026(n):
    if n == 0:
        return 0
    c, j = 1, 2
    k1 = n // j
    while k1 > 1:
        j2 = n // k1 + 1
        c += (j2 - j) * A090026(k1)
        j, k1 = j2, n // j2
    return (n + 1) ** 4 - c + 15 * (j - n - 1)


@lru_cache(maxsize=None)
def A090027(n):
    if n == 0:
        return 0
    c, j = 1, 2
    k1 = n // j
    while k1 > 1:
        j2 = n // k1 + 1
        c += (j2 - j) * A090027(k1)
        j, k1 = j2, n // j2
    return (n + 1) ** 5 - c + 31 * (j - n - 1)


@lru_cache(maxsize=None)
def A090028(n):
    if n == 0:
        return 0
    c, j = 1, 2
    k1 = n // j
    while k1 > 1:
        j2 = n // k1 + 1
        c += (j2 - j) * A090028(k1)
        j, k1 = j2, n // j2
    return (n + 1) ** 6 - c + 63 * (j - n - 1)


@lru_cache(maxsize=None)
def A090029(n):
    if n == 0:
        return 0
    c, j = 1, 2
    k1 = n // j
    while k1 > 1:
        j2 = n // k1 + 1
        c += (j2 - j) * A090029(k1)
        j, k1 = j2, n // j2
    return (n + 1) ** 7 - c + 127 * (j - n - 1)


def A114146(n):
    return (
        1
        if n == 0
        else 8 * n**2
        - 12 * n
        + 6
        + 4 * sum(totient(i) * (n - i) * (2 * n - i) for i in range(2, n))
    )


def A153679_gen():  # generator of terms
    n, k, q = 1024, 1000, 0
    for m in count(1):
        r = n % k
        if r > q:
            q = r
            yield m
        n *= 1024
        k *= 1000
        q *= 1000


def A166374_gen(startvalue=1):
    return filter(
        lambda n: sum([int(n * e / p) for p, e in factorint(n).items()]) == totient(n),
        count(max(startvalue, 1)),
    )


def A350253(n):
    return (
        1
        if (m := n % 6) == 2 or m == 5
        else (fibonacci(n + 1) if m == 3 else fibonacci(n))
    )


def A195269(n):
    m, s = 1, "0" * n
    for i in count(1):
        m *= 3
        if s in str(m):
            return i


def A230891_gen():  # generator of terms
    yield from [0, 11]
    l, s, b = Counter("11"), 1, {3}
    while True:
        i = s
        while True:
            if i not in b:
                li, o = Counter(bin(i)[2:]), 0
                for d in (l + li).values():
                    if d % 2:
                        if o > 0:
                            break
                        o += 1
                else:
                    yield int(bin(i)[2:])
                    l = li
                    b.add(i)
                    while s in b:
                        b.remove(s)
                        s += 1
                    break
            i += 1


def A245562_gen():  # generator of terms
    yield 0
    for n in count(1):
        yield from (len(d) for d in split("0+", bin(n)[2:]) if d != "")


def A247648_gen(startvalue=1):
    return filter(lambda n: n % 2 and not "00" in bin(n), count(max(startvalue, 1)))


def A274086(n):
    return int((n * tan(n)).round())


def A274087(n):
    return int((n**2 * sin(n)).round())


def A274088(n):
    return int((n**2 * sin(sqrt(n))).round())


def A274090(n):
    return int((n**2 * cos(sqrt(n))).round())


def A274091(n):
    k, j = divmod(n, 2)
    return int((k**2 * sin(sqrt(k) + j * pi / 2)).round())


def A274092(n):
    k, j = divmod(n, 3)
    return int((k**2 * sin(sqrt(k) + j * pi / 2)).round())


def A274095(n):
    return int((n * sin(sqrt(n))).round())


def A274097(n):
    k, j = divmod(n, 3)
    return int((k * sin(sqrt(k) + j * pi / 2)).round())


def A317085(n):
    c = 1
    for d in partitions(n, m=n * 2 // 3):
        l = len(d)
        if l > 0:
            k = sorted(d.keys())
            for i in range(l // 2):
                if d[k[i]] != d[k[l - i - 1]]:
                    break
            else:
                c += 1
    return c


def A320485(n):
    return (lambda x: int(x) if x != "" else -1)(
        "".join(d if str(n).count(d) == 1 else "" for d in str(n))
    )


def A328095_gen(startvalue=0):
    return filter(
        lambda n: (sn := str(n)) in str(n * prod(int(d) for d in sn)),
        count(max(startvalue, 0)),
    )


def A337856(n):
    k, n1, n2, pset = 0, 10 ** (n - 1) // 2 - 18, 10**n // 2 - 18, set()
    while 50 * k**2 + 60 * k < n2:
        a, b = divmod(n1 - 30 * k, 50 * k + 30)
        m = max(k, a + int(b > 0))
        r = 50 * k * m + 30 * (k + m)
        while r < n2:
            pset.add(r)
            m += 1
            r += 50 * k + 30
        k += 1
    return len(pset)


def A345687(n):
    return pvariance(
        n**2 * u
        for u, v, w in (igcdex(x, y) for x in range(1, n + 1) for y in range(1, n + 1))
    )


def A003512(n):
    return 2 * n + int(isqrt(3 * n**2))


def A004720(n):
    l = len(str(n - 1))
    m = (10**l - 1) // 9
    k = n + l - 2 + int(n + l - 1 >= m)
    return 0 if k == m else int(str(k).replace("1", ""))


def A005487_gen():  # generator of terms
    blist, bset = [0, 4], {0, 4}
    yield from blist
    for i in count(0):
        n, flag = blist[-1] + 1, False
        while True:
            for j in range(i + 1, 0, -1):
                m = 2 * blist[j] - n
                if m in bset:
                    break
                if m < 0:
                    flag = True
                    break
            else:
                blist.append(n)
                bset.add(n)
                yield n
                break
            if flag:
                blist.append(n)
                bset.add(n)
                yield n
                break
            n += 1


def A006723_gen():  # generator of terms
    blist = [1] * 7
    yield from blist
    while True:
        blist = blist[1:] + [
            (blist[-1] * blist[-6] + blist[-2] * blist[-5] + blist[-3] * blist[-4])
            // blist[-7]
        ]
        yield blist[-1]


def A007487(n):
    return (
        n**2
        * (n**2 * (n**2 * (n**2 * (n * (2 * n + 10) + 15) - 14) + 10) - 3)
        // 20
    )


def A008559_gen():  # generator of terms
    b = 2
    while True:
        yield b
        b = int(bin(b)[2:])


def A027602(n):
    return n * (n * (3 * n + 9) + 15) + 9


def A029976_gen():
    return filter(isprime, pal_gen(8))


def A029997_gen():
    return filter(
        lambda n: gmpy2digits(n, 11) == gmpy2digits(n, 11)[::-1],
        (n**2 for n in count(0)),
    )


def A036967_gen(startvalue=1):
    return filter(
        lambda n: min(factorint(n).values(), default=4) >= 4, count(max(startvalue, 1))
    )


def A048543(n):
    k, m = 1, 2
    while True:
        if str(m).count("7") == n:
            return k
        k += 1
        m += 2 * k


def A048544(n):
    k, m = 1, 2
    while True:
        if str(m).count("7") == n:
            return m
        k += 1
        m += 2 * k


def A053165(n):
    return 1 if n <= 1 else prod(p ** (e % 4) for p, e in factorint(n).items())


def A054383_gen():  # generator of terms
    l = {}
    for d in permutations("123456789", 9):
        for i in range(8):
            s1, s2 = int("".join(d[: i + 1])), int("".join(d[i + 1 :]))
            q, r = divmod(s1, s2)
            if not r:
                if q in l:
                    l[q] += 1
                else:
                    l[q] = 1
    for i in count(1):
        if i in l:
            yield l[i]
        else:
            yield 0


def A055155(n):
    return sum(gcd(d, n // d) for d in divisors(n, generator=True))


def A058411_gen(startvalue=0):
    return filter(
        lambda i: i % 10 and max(str(i**2)) < "3", count(max(startvalue, 0))
    )


def A064834(n):
    x, y = str(n), 0
    lx2, r = divmod(len(x), 2)
    for a, b in zip(x[:lx2], x[: lx2 + r - 1 : -1]):
        y += abs(int(a) - int(b))
    return y


def A065714(n):
    return str(2**n).count("3")


def A065716(n):
    return str(2**n).count("5")


def A065717(n):
    return str(2**n).count("6")


def A065718(n):
    return str(2**n).count("7")


def A065744(n):
    return str(2**n).count("9")


def A073785(n):
    s, q = "", n
    while q >= 3 or q < 0:
        q, r = divmod(q, -3)
        if r < 0:
            q += 1
            r += 3
        s += str(r)
    return int(str(q) + s[::-1])


def A073786(n):
    s, q = "", n
    while q >= 5 or q < 0:
        q, r = divmod(q, -5)
        if r < 0:
            q += 1
            r += 5
        s += str(r)
    return int(str(q) + s[::-1])


def A073787(n):
    s, q = "", n
    while q >= 6 or q < 0:
        q, r = divmod(q, -6)
        if r < 0:
            q += 1
            r += 6
        s += str(r)
    return int(str(q) + s[::-1])


def A073788(n):
    s, q = "", n
    while q >= 7 or q < 0:
        q, r = divmod(q, -7)
        if r < 0:
            q += 1
            r += 7
        s += str(r)
    return int(str(q) + s[::-1])


def A073789(n):
    s, q = "", n
    while q >= 8 or q < 0:
        q, r = divmod(q, -8)
        if r < 0:
            q += 1
            r += 8
        s += str(r)
    return int(str(q) + s[::-1])


def A073790(n):
    s, q = "", n
    while q >= 9 or q < 0:
        q, r = divmod(q, -9)
        if r < 0:
            q += 1
            r += 9
        s += str(r)
    return int(str(q) + s[::-1])


def A066417(n):
    return (
        0
        if n == 1
        else divisor_sigma(2 * n - 1)
        + divisor_sigma(2 * n + 1)
        + divisor_sigma(n // 2 ** (k := multiplicity(2, n))) * 2 ** (k + 1)
        - 6 * n
        - 2
    )


def A073930_gen(startvalue=2):
    return filter(
        lambda n: divisor_sigma(2 * n - 1)
        + divisor_sigma(2 * n + 1)
        + divisor_sigma(n // 2 ** (k := multiplicity(2, n))) * 2 ** (k + 1)
        - 7 * n
        - 2
        == 0,
        count(max(startvalue, 2)),
    )


def A192268_gen(startvalue=2):
    return filter(
        lambda n: divisor_sigma(2 * n - 1)
        + divisor_sigma(2 * n + 1)
        + divisor_sigma(n // 2 ** (k := multiplicity(2, n))) * 2 ** (k + 1)
        - 7 * n
        - 2
        > 0,
        count(max(startvalue, 2)),
    )


def A082410(n):
    if n == 1:
        return 0
    s = bin(n - 1)[2:]
    m = len(s)
    i = s[::-1].find("1")
    return 1 - int(s[m - i - 2]) if m - i - 2 >= 0 else 1


def A111116_gen(startvalue=1):
    return filter(
        lambda n: len(set(str(n)) & set(str(n**4))) == 0, count(max(startvalue, 1))
    )


def A115927_gen():  # generator of terms
    l = {}
    for d in permutations("0123456789", 10):
        if d[0] != "0":
            for i in range(9):
                if d[i + +1] != "0":
                    q, r = divmod(int("".join(d[: i + 1])), int("".join(d[i + 1 :])))
                    if not r:
                        if q in l:
                            l[q] += 1
                        else:
                            l[q] = 1
    for i in count(1):
        if i in l:
            yield l[i]
        else:
            yield 0


def A235811_gen(startvalue=0):
    return filter(lambda n: len(set(str(n**3))) == 9, count(max(startvalue, 0)))


def A235809_gen(startvalue=0):
    return filter(lambda n: len(set(str(n**3))) == 7, count(max(startvalue, 0)))


def A137921(n):
    return len([d for d in divisors(n, generator=True) if n % (d + 1)])


def A153686_gen():  # generator of terms
    k10, k11 = 10, 11
    for k in count(1):
        if (k11 % k10) * k < k10:
            yield k
        k10 *= 10
        k11 *= 11


def A153670_gen():  # generator of terms
    k10, k11 = 100, 101
    for k in count(1):
        if (k11 % k10) * k < k10:
            yield k
        k10 *= 100
        k11 *= 101


def A153687_gen():  # generator of terms
    n, k, q = 11, 10, 0
    for m in count(1):
        r = n % k
        if r > q:
            q = r
            yield m
        n *= 11
        k *= 10
        q *= 10


def A177029_gen(startvalue=1):  # generator of terms
    for m in count(max(startvalue, 1)):
        n, c = 3, 0
        while n * (n + 1) <= 2 * m:
            if not 2 * (n * (n - 2) + m) % (n * (n - 1)):
                c += 1
                if c > 1:
                    break
            n += 1
        if c == 1:
            yield m


def A187824(n):
    k = 1
    while (n + 1) % k < 3:
        k += 1
    return k - 1


def A206709(n):
    c, b, b2, n10 = 0, 1, 2, 10**n
    while b <= n10:
        if isprime(b2):
            c += 1
        b += 1
        b2 += 2 * b - 1
    return c


def A219531(n):
    return (
        n
        * (
            n
            * (
                n
                * (
                    n
                    * (
                        n
                        * (
                            n
                            * (
                                n * (n * (n * (n * (n - 44) + 935) - 11550) + 94083)
                                - 497112
                            )
                            + 1870385
                        )
                        - 3920950
                    )
                    + 8550916
                )
                + 4429656
            )
            + 29400480
        )
        // 39916800
        + 1
    )


def A226561(n):
    return sum(totient(d) * d**n for d in divisors(n, generator=True))


def A228640(n):
    return sum(totient(d) * n ** (n // d) for d in divisors(n, generator=True))


def A242171_gen():  # generator of terms
    yield 1
    bell_list, blist, b = [1, 1], [1], 1
    while True:
        blist = list(accumulate([b] + blist))
        b = blist[-1]
        fs = primefactors(b)
        for p in fs:
            if all(n % p for n in bell_list):
                yield p
                break
        else:
            yield 1
        bell_list.append(b)


def A245563_gen():
    yield from chain(
        [0], (len(d) for n in count(1) for d in split("0+", bin(n)[:1:-1]) if d != "")
    )


def A246588(n):
    return (
        prod(bin(len(d)).count("1") for d in split("0+", bin(n)[2:]) if d)
        if n > 0
        else 1
    )


def A246595(n):
    return prod(len(d) ** 2 for d in split("0+", bin(n)[2:]) if d != "") if n > 0 else 1


def A246596(n):
    s, c = bin(n)[2:], [1, 1]
    for m in range(1, len(s)):
        c.append(c[-1] * (4 * m + 2) // (m + 2))
    return prod(c[len(d)] for d in split("0+", s)) if n > 0 else 1


def A247649_gen():  # generator of terms
    from sympy.abc import x

    f, g, blist = 1 / x**2 + 1 / x + 1 + x + x**2, 1, [1]
    yield 1
    for n in count(1):
        s = [int(d, 2) for d in bin(n)[2:].split("00") if d != ""]
        g = (g * f).expand(modulus=2)
        if len(s) == 1:
            blist.append(g.subs(x, 1))
            yield blist[-1]
        else:
            blist.append(prod(blist[d] for d in s))
            yield blist[-1]


def A225654_gen():  # generator of terms
    from sympy.abc import x

    f, g, blist, c = 1 / x**2 + 1 / x + 1 + x + x**2, 1, [1], 1
    yield c
    for n in count(1):
        s = [int(d, 2) for d in bin(n)[2:].split("00") if d != ""]
        g = (g * f).expand(modulus=2)
        if len(s) == 1:
            blist.append(g.subs(x, 1))
        else:
            blist.append(prod(blist[d] for d in s))
        c += blist[-1]
        yield c


def A254449(n):
    if n == 0:
        return 0
    i, m, s = 1, 1, "4" * n
    s2 = s + "4"
    while True:
        m *= i
        sn = str(m)
        if s in sn and s2 not in sn:
            return i
        i += 1


def A266142(n):
    return (
        4 * n
        if (n == 1 or n == 2)
        else sum(
            1
            for d in range(-3, 7)
            for i in range(n)
            if isprime((10**n - 1) // 3 + d * 10**i)
        )
    )


def A266146(n):
    return (
        4 * n
        if (n == 1 or n == 2)
        else sum(
            1
            for d in range(-7, 3)
            for i in range(n)
            if isprime(7 * (10**n - 1) // 9 + d * 10**i)
        )
    )


def A266148(n):
    return sum(
        1 for d in range(-9, 1) for i in range(n) if isprime(10**n - 1 + d * 10**i)
    )


def A289673_gen():
    return (
        -1 if s == ("1",) else int(("".join(s) + ("2212" if s[0] == "2" else "11"))[3:])
        for l in count(1)
        for s in product("12", repeat=l)
    )


def A305611(n):
    fs = factorint(n)
    return len(
        set(
            sum(d)
            for i in range(1, sum(fs.values()) + 1)
            for d in multiset_combinations(fs, i)
        )
    )


def A317088(n):
    if n == 0:
        return 1
    c = 0
    for d in partitions(n, k=isqrt(2 * n)):
        l = len(d)
        if l > 0 and l == max(d):
            v = set(d.values())
            if len(v) == max(v):
                c += 1
    return c


def A345688(n):
    return pvariance(
        n**2 * v
        for u, v, w in (igcdex(x, y) for x in range(1, n + 1) for y in range(1, n + 1))
    )


def A004721(n):
    l = len(str(n))
    m = 2 * (10**l - 1) // 9
    k = n + l - int(n + l < m)
    return 1 if k == m else int(str(k).replace("2", ""))


def A004722(n):
    l = len(str(n))
    m = (10**l - 1) // 3
    k = n + l - int(n + l < m)
    return 2 if k == m else int(str(k).replace("3", ""))


def A004724(n):
    l = len(str(n))
    m = 5 * (10**l - 1) // 9
    k = n + l - int(n + l < m)
    return 4 if k == m else int(str(k).replace("5", ""))


def A004731(n):
    if n <= 1:
        return 1
    a, b = factorial2(n - 2), factorial2(n - 1)
    return b // gcd(a, b)


def A011968_gen():  # generator of terms
    yield from [1, 2]
    blist, b = [1], 1
    while True:
        blist = list(accumulate([b] + blist))
        yield b + blist[-1]
        b = blist[-1]


def A014710(n):
    s = bin(n + 1)[2:]
    m = len(s)
    i = s[::-1].find("1")
    return 2 - int(s[m - i - 2]) if m - i - 2 >= 0 else 2


def A017713_gen():  # generator of terms
    m = [1] * 50
    while True:
        yield m[-1]
        for i in range(49):
            m[i + 1] += m[i]


def A017713(n):
    return comb(n, 49)


def A020462_gen():
    return filter(
        isprime, (int("".join(x)) for n in count(1) for x in product("35", repeat=n))
    )


@lru_cache(maxsize=None)
def A022825(n):
    if n <= 1:
        return n
    c, j = 0, 2
    k1 = n // j
    while k1 > 1:
        j2 = n // k1 + 1
        c += (j2 - j) * A022825(k1)
        j, k1 = j2, n // j2
    return c + n + 1 - j


def A030665(n):
    d, nd = 10, 10 * n
    while True:
        x = nextprime(nd)
        if x < nd + d:
            return int(x)
        d *= 10
        nd *= 10


def A050932(n):
    return (q := bernoulli(n).q) // gcd(q, n + 1)


def A053600_gen():  # generator of terms
    yield 2
    p = 2
    while True:
        m, ps = 1, str(p)
        s = int("1" + ps + "1")
        while not isprime(s):
            m += 1
            ms = str(m)
            s = int(ms + ps + ms[::-1])
        p = s
        yield p


def A054268_gen():
    return filter(
        lambda p: len(set(str(int(((q := nextprime(p)) - p - 1) * (q + p) // 2)))) == 1,
        (prime(n) for n in count(2)),
    )


def A061308_gen():  # generator of terms
    for n in count(2, 2):
        p = prevprime((n3 := n**3) // 2)
        if p + nextprime(p) == n3:
            yield p


def A061783_gen():
    return filter(
        lambda p: isprime(p + int(str(p)[::-1])), (prime(n) for n in count(1))
    )


@lru_cache(maxsize=None)
def A063985(n):  # based on second formula in A018805
    if n == 0:
        return 0
    c, j = 0, 2
    k1 = n // j
    while k1 > 1:
        j2 = n // k1 + 1
        c += (j2 - j) * (k1 * (k1 + 1) - 2 * A063985(k1) - 1)
        j, k1 = j2, n // j2
    return (2 * n + c - j) // 2


def A065847(n):
    return max(
        sum(
            1
            for t in multiset_permutations(s)
            if t[0] != "0" and isprime(int("".join(t), 6))
        )
        for s in combinations_with_replacement("012345", n)
    )


def A069862(n):
    nk, kr, r = n + 1, 1, 1 if n > 1 else 0
    while r:
        nk += 1
        kr = (kr + 1) % n
        r = (r * (10 ** len(str(nk)) % n) + kr) % n
    return nk - n


def A074989(n):
    a = integer_nthroot(n, 3)[0]
    return min(n - a**3, (a + 1) ** 3 - n)


def A082491_gen():  # generator of terms
    m, x = 1, 1
    for n in count(0):
        x, m = x * n**2 + m, -(n + 1) * m
        yield x


def A087666(n):
    c, x = 0, n
    a, b = divmod(x, 3)
    while b != 0:
        x *= a
        c += 1
        a, b = divmod(x, 3)
    return c


def A088658(n):
    return 4 * (n - 1) ** 2 + 4 * sum(
        totient(i) * (n - i) * (2 * n - i) for i in range(2, n)
    )


def A091049(n):
    k = 1
    while True:
        m1 = k
        for i in range(n + 1):
            m2 = int(str(m1), 1 + max(int(d) for d in str(m1)))
            if m1 == m2:
                if i == n:
                    return k
                else:
                    break
            m1 = m2
        k += 1


def A094577_gen():  # generator of terms
    yield 1
    blist, b = [1], 1
    for n in count(2):
        blist = list(accumulate([b] + blist))
        b = blist[-1]
        blist = list(accumulate([b] + blist))
        b = blist[-1]
        yield blist[-n]


def A094519_gen(startvalue=1):  # generator of terms
    for n in count(max(startvalue, 1)):
        for i in range(1, len(d := divisors(n))):
            di = d[i]
            for j in range(i):
                if n % (di + d[j]) == 0:
                    yield n
                    break
            else:
                continue
            break


def A095149_gen():  # generator of terms
    yield from [1] * 3
    blist = [1]
    while True:
        blist = list(accumulate([blist[-1]] + blist))
        yield blist[-1]
        yield from blist


def A097227_gen():  # generator of terms
    ptuple = (2, 3, 5, 7, 11, 13, 17, 19, 23)
    for l in count(1):
        for d in combinations_with_replacement(range(1, 10), l):
            if (n := prod(ptuple[i - 1] for i in d)) < 10 ** l and tuple(
                sorted((int(x) for x in str(n)))
            ) == d:
                yield n


def A102487(n):
    return int(str(n), 12)


def A102491(n):
    return int(str(n), 20)


def A007091(n):
    return int(gmpy2digits(n, 5))


def A131535(n):
    s, t, m, k, u = "1" * n, "1" * (n + 1), 0, 1, "1"
    while s not in u or t in u:
        m += 1
        k *= 2
        u = str(k)
    return m


def A131544(n):
    m, s = 1, "9" * n
    for i in count(1):
        m *= 3
        if s in str(m):
            return i


def A131546(n):
    str7 = "7" * n
    x, exponent = 3, 1
    while not str7 in str(x):
        exponent += 1
        x *= 3
    return exponent


def A131552(n):
    m, s = 1, "1" * n
    for i in count(1):
        m *= 3
        if s in str(m):
            return i


def A153695_gen():  # generator of terms
    m10, m9, q = 10, 9, 0
    for m in count(1):
        r = m10 % m9
        if r > q:
            q = r
            yield m
        m10 *= 10
        m9 *= 9
        q *= 9


def A153745_gen():  # generator of terms
    for l in count(1):
        if not is_prime(l):
            fs = divisors(l)
            a = isqrt(10 ** (l - 1)) + ((l - 1) % 2)
            for n in range(a, isqrt(10**l - 1) + 1):
                for g in fs:
                    if not is_square(
                        sum(int(str(n**2)[h : h + g]) for h in range(0, l, g))
                    ):
                        break
                else:
                    yield n


def A155146_gen():  # generator of terms
    n3, m = 0, 0
    for n in count(1):
        m += 6 * (n - 1)
        n3 += m + 1
        if len(set(str(n3))) == 3:
            yield n


def A159065(n):
    return (
        n - 1
        if n <= 2
        else 2 * n
        - 3
        + 3 * sum(totient(i) * (n - i) * i for i in range(2, (n + 1) // 2))
        + sum(totient(i) * (n - i) * (2 * n - i) for i in range((n + 1) // 2, n))
    )


def A163573_gen():
    return (
        4 * q - 3
        for q in (prime(i) for i in count(1))
        if isprime(4 * q - 3)
        and isprime(2 * q - 1)
        and (not (4 * q - 1) % 3)
        and isprime((4 * q - 1) // 3)
    )


def A175047(n):
    return int(
        "".join(
            d + "0" if "0" in d else d
            for d in split("(0+)|(1+)", bin(n)[2:])
            if d != "" and d != None
        ),
        2,
    )


def A188068(n):
    return int(isqrt(3 * n**2) - isqrt(3 * (n - 1) ** 2)) - 1


def A201053(n):
    return (
        a**3
        if 2 * n < (a := integer_nthroot(n, 3)[0]) ** 3 + (a + 1) ** 3
        else (a + 1) ** 3
    )


def A211264(n):
    return (lambda m: sum(n // k for k in range(1, m + 1)) - m * (m + 1) // 2)(isqrt(n))


def A212529(n):
    s, q = "", -n
    while q >= 2 or q < 0:
        q, r = divmod(q, -2)
        if r < 0:
            q += 1
            r += 2
        s += str(r)
    return int(str(q) + s[::-1])


def A219327_gen(startvalue=1):  # generator of terms
    for n in count(max(startvalue, 1)):
        s = [int(d) for d in str(n)]
        m = len(s)
        if n == abs(Matrix(m, m, lambda i, j: s[(i - j) % m]).det()):
            yield n


def A230892_gen():  # generator of terms
    yield from [0, 3]
    l, s, b = Counter("11"), 1, {3}
    while True:
        i = s
        while True:
            if i not in b:
                li, o = Counter(bin(i)[2:]), 0
                for d in (l + li).values():
                    if d % 2:
                        if o > 0:
                            break
                        o += 1
                else:
                    yield i
                    l = li
                    b.add(i)
                    while s in b:
                        b.remove(s)
                        s += 1
                    break
            i += 1


def A244112(n):
    return int(
        "".join([str(str(n).count(d)) + d for d in "9876543210" if str(n).count(d) > 0])
    )


def A249915_gen():  # generator of terms
    for l in count(0):
        for a in product("23456", repeat=l):
            for b in ("2", "4", "5", "6"):
                s = "".join(a) + b
                if "2" in s and "6" in s:
                    n = int(s)
                    if {"2", "6"} <= set(str(n**2)) <= {"2", "3", "4", "5", "6"}:
                        yield n


def A287055_gen():  # generator of terms
    a = 1
    for n in count(1):
        b = prod(p**e - 1 for p, e in factorint(n + 1).items())
        if a == b:
            yield n
        a, n = b, n + 1


def A296369_gen(startvalue=1):
    return filter(lambda n: pow(2, n + 1, n) == n - 1, count(max(startvalue, 1)))


def A324043(n):
    return (
        0
        if n == 1
        else -2 * (n - 1) ** 2
        + sum(
            totient(i) * (n + 1 - i) * (7 * i - 2 * n - 2) for i in range(2, n // 2 + 1)
        )
        + sum(
            totient(i) * (n + 1 - i) * (2 * n + 2 - i) for i in range(n // 2 + 1, n + 1)
        )
    )


def A335567(n):
    return (n - (m := divisor_count(n))) * (n - m + 1) // 2


def A341715(n):
    m, k = n, n
    while not isprime(m):
        k += 1
        m = int(str(m) + str(k))
    return m


def A345689(n):
    return pvariance(
        n**2 * abs(u)
        for u, v, w in (igcdex(x, y) for x in range(1, n + 1) for y in range(1, n + 1))
    )


def A003221_gen():  # generator terms
    m, x = -1, 0
    for n in count(0):
        x, m = x * n + m * (n * (n - 1) // 2 - 1), -m
        yield x


def A004723(n):
    l = len(str(n))
    m = 4 * (10**l - 1) // 9
    k = n + l - int(n + l < m)
    return 3 if k == m else int(str(k).replace("4", ""))


def A004725(n):
    l = len(str(n))
    m = 2 * (10**l - 1) // 3
    k = n + l - int(n + l < m)
    return 5 if k == m else int(str(k).replace("6", ""))


def A004726(n):
    l = len(str(n))
    m = 7 * (10**l - 1) // 9
    k = n + l - int(n + l < m)
    return 6 if k == m else int(str(k).replace("7", ""))


def A004727(n):
    l = len(str(n))
    m = 8 * (10**l - 1) // 9
    k = n + l - int(n + l < m)
    return 7 if k == m else int(str(k).replace("8", ""))


def A007464_gen():  # generator of terms
    blist = [1, 1]
    yield from blist
    for n in count(1):
        blist.append(sum(gcd(blist[i], blist[n - i]) for i in range(n + 1)))
        yield blist[-1]


def A022488_gen():  # generator of terms
    yield 2
    l = "2"
    while True:
        l = "".join(
            d[0] + str(len(d))
            for d in split("(0+|1+|2+|3+|4+|5+|6+|7+|8+|9+)", l[::-1])
            if d != ""
        )
        yield int(l)


def A047898_gen():  # generator of terms
    l = 6
    while True:
        yield l
        l *= sum(int(d) for d in str(l))


def A047901_gen():  # generator of terms
    l = 9
    while True:
        yield l
        l *= sum(int(d) for d in str(l))


def A059168_helper(w, dir):
    if dir == 1:
        for s in w:
            for t in range(int(s[-1]) + 1, 10):
                yield s + str(t)
    else:
        for s in w:
            for t in range(0, int(s[-1])):
                yield s + str(t)


def A059168_gen():  # generator of terms
    for l in count(0):
        for d in "123456789":
            x = d
            for i in range(1, l + 1):
                x = A059168_helper(x, (-1) ** i)
            yield from (int(p) for p in x if isprime(int(p)))
            if l > 0:
                y = d
                for i in range(1, l + 1):
                    y = A059168_helper(y, (-1) ** (i + 1))
                yield from (int(p) for p in y if isprime(int(p)))


def A061246_gen():
    return (
        int(i + "".join(j) + k)
        for l in count(0)
        for i in "149"
        for j in product("0149", repeat=l)
        for k in "19"
        if isprime(int(i + "".join(j) + k))
    )


def A063565(n):
    s, k, k2 = str(n), 1, 2
    while True:
        if s in str(k2):
            return k
        k += 1
        k2 *= 2


def A064169(n):
    return (lambda x: x.p - x.q)(harmonic(n))


def A068187(n):
    if n == 1:
        return 1
    pf = factorint(n)
    return (
        0
        if max(pf) > 7
        else int(
            "".join(
                sorted(
                    "".join(str(a) * (n * b) for a, b in pf.items())
                    .replace("222", "8")
                    .replace("22", "4")
                    .replace("33", "9")
                )
            )
        )
    )


def A072961_gen():
    return (int("".join(a)) for l in count(1) for a in product("25", repeat=l))


def A081134(n):
    kmin, kmax = 0, 1
    while 3**kmax <= n:
        kmax *= 2
    while True:
        kmid = (kmax + kmin) // 2
        if 3**kmid > n:
            kmax = kmid
        else:
            kmin = kmid
        if kmax - kmin <= 1:
            break
    return min(n - 3**kmin, 3 * 3**kmin - n)


@lru_cache(maxsize=None)
def A082544(n):
    if n == 0:
        return 0
    c, j = 1, 2
    k1 = n // j
    while k1 > 1:
        j2 = n // k1 + 1
        c += (j2 - j) * A082544(k1)
        j, k1 = j2, n // j2
    return n * (n**4 - 1) - c + j


def A090709_gen():
    return filter(isprime, (int(gmpy2digits(d, 6)) for d in count(0) if is_prime(d)))


def A091627(n):
    m = isqrt(n)
    return 0 if n == 0 else sum(n // k for k in range(1, m + 1)) - m * (m - 1) // 2 - 1


def A094593(n):
    p = prime(n)
    return 1 if n == 3 else (p - 1) // n_order(3, p)


def A118600_gen():
    return palbase_gen(9)


def A118599_gen():
    return palbase_gen(8)


def A118598_gen():
    return palbase_gen(7)


def A118597_gen():
    return palbase_gen(6)


def A118596_gen():
    return palbase_gen(5)


def A118595_gen():
    return palbase_gen(4)


def A118594_gen():
    return palbase_gen(3)


def A123098(n):
    return prod(1 if ~(n - 1) & k else prime(k + 1) for k in range(n))


def A131536(n):
    s, t, m, k, u = "2" * n, "2" * (n + 1), 0, 1, "1"
    while s not in u or t in u:
        m += 1
        k *= 2
        u = str(k)
    return m


def A145551_gen(startvalue=1):
    return filter(
        lambda n: not n ** divisor_sigma(n, 0) % divisor_sigma(n, 1) ** 2,
        count(max(startvalue, 1)),
    )


def A169639(n):
    return sum(ord(s) - 96 for s in unidecode(num2words(n, lang="fr")) if s.isalpha())


def A189718_gen():  # generator of terms
    blist = [0]
    yield 0
    while True:
        x = [1 - d for d in blist] * 2
        blist.extend(x)
        yield from x


def A241100(n):
    for i in range(1, 10):
        x = i * (10**n - 1) // 9
        for j in range(n - 1, -1, -1):
            for k in range(i, -1, -1):
                if j < n - 1 or k < i:
                    y = x - k * (10**j)
                    if isprime(y):
                        return y
        for j in range(n):
            for k in range(1, 9 - i + 1):
                y = x + k * (10**j)
                if isprime(y):
                    return y


def A266141(n):
    return 4 if n == 1 else sum(1 for d in "1379" if isprime(int("2" * (n - 1) + d)))


def A266144(n):
    return (
        4
        if n == 1
        else sum(1 for d in [-4, -2, 2, 4] if isprime(5 * (10**n - 1) // 9 + d))
    )


def A266145(n):
    return (
        4
        if n == 1
        else sum(1 for d in [-5, -3, 1, 3] if isprime(2 * (10**n - 1) // 3 + d))
    )


def A266147(n):
    return (
        4
        if n == 1
        else sum(1 for d in [-7, -5, -1, 1] if isprime(8 * (10**n - 1) // 9 + d))
    )


def A276740_gen():  # generator of terms
    yield from [1, 2, 4]
    yield from filter(lambda n: pow(3, n, n) == 5, count(5))


def A277289_gen():  # generator of terms
    yield from [1, 2, 4, 5]
    yield from filter(lambda n: pow(3, n, n) == n - 7, count(6))


def A277288_gen():  # generator of terms
    yield from [1, 2]
    yield from filter(lambda n: pow(3, n, n) == n - 5, count(3))


def A277340_gen():  # generator of terms
    yield from [1, 2, 4, 7, 10]
    yield from filter(lambda n: pow(3, n, n) == n - 11, count(11))


def A288104(n):
    ndict = {}
    for i in range(n):
        m = pow(i, 9, n)
        if m in ndict:
            ndict[m] += 1
        else:
            ndict[m] = 1
    count = 0
    for i in ndict:
        ni = ndict[i]
        for j in ndict:
            k = (i + j) % n
            if k in ndict:
                count += ni * ndict[j] * ndict[k]
    return count


def A288105(n):
    ndict = {}
    for i in range(n):
        m = pow(i, 10, n)
        if m in ndict:
            ndict[m] += 1
        else:
            ndict[m] = 1
    count = 0
    for i in ndict:
        ni = ndict[i]
        for j in ndict:
            k = (i + j) % n
            if k in ndict:
                count += ni * ndict[j] * ndict[k]
    return count


def A289677(n):
    c, k, r, n2, cs, ts = (
        0,
        1 + (n - 1) // 3,
        2 ** ((n - 1) % 3),
        2 ** (n - 1),
        set(),
        set(),
    )
    for i in range(2**k):
        j, l = int(bin(i)[2:], 8) * r, n2
        traj = set([(l, j)])
        while True:
            if j >= l:
                j = j * 16 + 13
                l *= 2
            else:
                j *= 4
                l //= 2
            if l == 0:
                ts |= traj
                break
            j %= 2 * l
            if (l, j) in traj:
                c += 1
                cs |= traj
                break
            if (l, j) in cs:
                c += 1
                break
            if (l, j) in ts:
                break
            traj.add((l, j))
    return c


def A307371_gen():  # generator of terms
    blist = [0, 1, 98, 99, 100, 9998]
    yield from blist
    while True:
        blist = blist[1:] + [101 * blist[-3] - 100 * blist[-6]]
        yield blist[-1]


def A307437(n):
    for k in count(1):
        if not reduced_totient(k) % (2 * n):
            return k


def A324042(n):
    return 2 * (
        2 * n**2
        - n
        + 1
        + 2
        * sum(totient(i) * (n + 1 - 2 * i) * (n + 1 - i) for i in range(2, n // 2 + 1))
    )


def A342632(n):
    return 2 * sum(t for t in sieve.totientrange(1, 2**n + 1)) - 1


@lru_cache(maxsize=None)
def A343978(n):
    if n == 0:
        return 0
    c, j, k1 = 1, 2, n // 2
    while k1 > 1:
        j2 = n // k1 + 1
        c += (j2 - j) * A343978(k1)
        j, k1 = j2, n // j2
    return n * (n**5 - 1) - c + j


def A344866(n):
    return n * (n * (n * (2 * n - 11) + 23) - 21) + 7


def A345690(n):
    return pvariance(
        n**2 * abs(v)
        for u, v, w in (igcdex(x, y) for x in range(1, n + 1) for y in range(1, n + 1))
    )


def A004728(n):
    l = len(str(n))
    m = 10**l - 1
    k = n + l - int(n + l < m)
    return 8 if k == m else int(str(k).replace("9", ""))


def A014957_gen(startvalue=1):
    return filter(lambda n: n == 1 or pow(16, n, n) == 1, count(max(startvalue, 1)))


def A023002(n):
    return (
        n
        * (
            n**2
            * (n**2 * (n**2 * (n**2 * (n * (6 * n + 33) + 55) - 66) + 66) - 33)
            + 5
        )
        // 66
    )


def A160773_gen():  # generator of terms
    p3, p5, p7 = [1] * 3
    for k in count(0):
        if isprime(p3 + p5 + p7):
            yield k
        p3 *= 3
        p5 *= 5
        p7 *= 7


def A349682(n):
    return n * (n * (36 * n + 36) + 11) + 1


def A349466(n):
    return 24 * 24**n + 64 * 2 ** (4 * n) - 81 * 18**n - 6 * 12**n


def A029455_gen():  # generator of terms
    r = 0
    for n in count(1):
        r = r * 10 ** len(str(n)) + n
        if not (r % n):
            yield n


def A052045_gen(startvalue=1):
    return filter(
        lambda n: not str(n).count("0"), (n**3 for n in count(max(startvalue, 1)))
    )


def A055941(n):
    s = bin(n)[2:]
    return sum(s[i:].count("0") for i, d in enumerate(s, start=1) if d == "1")


def A058233_gen():  # generator of terms
    p, q, r = 2, 3, 2
    while True:
        if (r + 1) % q == 0:
            yield p
        r *= q
        p, q = q, nextprime(q)


def A077110(n):
    n2 = n**2
    a = integer_nthroot(n2, 3)[0]
    a2, a3 = a**3, (a + 1) ** 3
    return a3 if a3 + a2 - 2 * n2 < 0 else a2


def A081762_gen():
    return filter(
        lambda p: pow(2, p - 1, p * (p - 2)) == 1, (prime(n) for n in count(2))
    )


def A082216(n):
    s = str(n)
    t = s[::-1]
    if s == t:
        return n
    for i in range(1, len(s)):
        if s[i:] == t[:-i]:
            return int(s + t[-i:])


def A085807(n):
    return Matrix(n, n, [abs(j - k) for j in range(n) for k in range(n)]).per()


def A090287(n):
    sn = str(n)
    if n in (231, 420, 759) or not (len(sn) % 2 or n % 11):
        return 0
    for i in count(1):
        for j in range(1, 10, 2):
            si = str(j) * i
            p = int(si + sn + si)
            if isprime(p):
                return p


def A099004_gen():  # generator of terms
    yield 1
    l, s, b1, b2 = 2, 3, set(), {1}
    while True:
        i = s
        while True:
            m = abs(i - l)
            if not (i in b1 or m in b2):
                yield i - l
                b1.add(i)
                b2.add(m)
                l = i
                while s in b1:
                    b1.remove(s)
                    s += 1
                break
            i += 1


def A110819_gen(startvalue=1):
    return filter(
        lambda n: (s := str(n)) != s[::-1]
        and primefactors(n) == primefactors(int(s[::-1])),
        count(max(startvalue, 1)),
    )


def A111163_gen():
    return filter(
        lambda n: not isprime(n // 2) and prevprime(n // 2) + nextprime(n // 2) == n,
        (n * (n + 1) // 2 for n in count(3)),
    )


def A111234_gen():
    return chain(
        (2,), (a + b // a for a, b in ((min(factorint(n)), n) for n in count(2)))
    )


def A124661_gen():  # generator of terms
    for n in count(1):
        p = prime(n)
        for k in range(1, n - 1):
            if prime(n - k) + prime(n + k) < 2 * p:
                break
        else:
            yield p


def A127962_gen():
    return (
        int(bin(p)[2:])
        for p in filter(isprime, ((2 ** prime(n) + 1) // 3 for n in count(2)))
    )


def A145642(n):
    return (
        1 if n <= 1 else prod(p ** (e % 3) for p, e in factorint(factorial(n)).items())
    )


def A160256_gen():  # generator of terms
    yield from [1, 2]
    l1, m, b = 2, 1, {1, 2}
    while True:
        i = m
        while True:
            if not i in b:
                yield i
                l1, m = i, l1 // gcd(l1, i)
                b.add(i)
                break
            i += m


def A165562_gen(startvalue=1):
    return filter(
        lambda n: isprime(n + sum(int(n * e / p) for p, e in factorint(n).items())),
        count(max(startvalue, 1)),
    )


@lru_cache(maxsize=None)
def A171503(n):  # based on second formula in A018805
    if n == 0:
        return 0
    c, j = 0, 2
    k1 = n // j
    while k1 > 1:
        j2 = n // k1 + 1
        c += (j2 - j) * (A171503(k1) - 1) // 2
        j, k1 = j2, n // j2
    return 2 * (n * (n - 1) - c + j) - 1


def A175499_gen():  # generator of terms
    yield 1
    bset, l, s, b = {1}, 2, 3, set()
    while True:
        i, j = s, s - l
        while True:
            if not (i in b or j in bset):
                yield j
                bset.add(j)
                b.add(i)
                l = i
                while s in b:
                    b.remove(s)
                    s += 1
                break
            i += 1
            j += 1


def A210503_gen(startvalue=2):  # generator of terms
    for n in count(max(startvalue, 2)):
        nd = sum(n * e // p for p, e in factorint(n).items())
        if is_square(nd**2 + n**2) and gcd(n, nd, isqrt(nd**2 + n**2)) == 1:
            yield n


def A235800(n):
    return 4 * (n // 2) + 3 if n % 2 else n // 2


def A241816(n):
    s = bin(n)[2:]
    for i in range(len(s) - 2, -1, -1):
        if s[i : i + 2] == "10":
            return int(s[:i] + "01" + s[i + 2 :], 2)
    else:
        return n


def A243103(n):
    y, pf = 1, set(primefactors(n))
    for m in range(2, n + 1):
        if set(primefactors(m)) <= pf:
            y *= m
    return y


def A257226_gen(startvalue=1):
    return filter(
        lambda n: any("9" in str(d) for d in divisors(n, generator=True)),
        count(max(startvalue, 1)),
    )


def A257225_gen(startvalue=1):
    return filter(
        lambda n: any("8" in str(d) for d in divisors(n, generator=True)),
        count(max(startvalue, 1)),
    )


def A257224_gen(startvalue=1):
    return filter(
        lambda n: any("7" in str(d) for d in divisors(n, generator=True)),
        count(max(startvalue, 1)),
    )


def A257223_gen(startvalue=1):
    return filter(
        lambda n: any("6" in str(d) for d in divisors(n, generator=True)),
        count(max(startvalue, 1)),
    )


def A257222_gen(startvalue=1):
    return filter(
        lambda n: any("5" in str(d) for d in divisors(n, generator=True)),
        count(max(startvalue, 1)),
    )


def A257221_gen(startvalue=1):
    return filter(
        lambda n: any("4" in str(d) for d in divisors(n, generator=True)),
        count(max(startvalue, 1)),
    )


def A257220_gen(startvalue=1):
    return filter(
        lambda n: any("3" in str(d) for d in divisors(n, generator=True)),
        count(max(startvalue, 1)),
    )


def A257219_gen(startvalue=1):
    return filter(
        lambda n: any("2" in str(d) for d in divisors(n, generator=True)),
        count(max(startvalue, 1)),
    )


def A257486_gen():  # generator of terms
    for l in count(0):
        for a in product("34567", repeat=l):
            for b in ("4", "5", "6"):
                s = "".join(a) + b
                if "3" in s and "7" in s:
                    n = int(s)
                    if {"3", "7"} <= set(str(n**2)) <= {"3", "4", "5", "6", "7"}:
                        yield n


def A258981_gen():
    return filter(
        lambda n: max(gmpy2digits(n, 3)) <= "1",
        (int(format(d, "b"), 4) for d in count(0)),
    )


def A263132_gen(startvalue=1):
    return filter(lambda m: not ~(4 * m - 1) & m, count(max(startvalue, 1)))


def A267769_gen():
    return (
        int(s, 9)
        for s in filter(lambda s: max(s) < "9", (str(i**2) for i in count(0)))
    )


def A271472(n):
    if n == 0:
        return 0
    else:
        s, q = "", n
        while q:
            q, r = c_divmod(q, -4)
            s += ("0000", "1000", "0011", "1011")[r]
        return int(s[::-1])


def A350087(n):
    a, b = lucas2(n + 1)
    return pow(b, a, a + b)


def A272170_gen():  # generator of terms
    a, b = 1, 1
    while True:
        a, b = b, a + b
        yield int(bin(b)[3])


def A272170(n):
    return int(bin(fibonacci(n))[3])


def A284597(n):
    count, starti, s, i = 0, 1, 0, 1
    while True:
        d = divisor_count(i)
        if d < s:
            if count == n:
                return starti
            starti = i
            count = 0
        s = d
        i += 1
        count += 1


def A298684_gen(startvalue=1):  # generator of terms
    b, a = fib2((sv := max(startvalue, 1)) + 1)
    for n in count(sv):
        if not (a % (n * (n + 1) * (n + 2) // (1 if n % 2 else 2))):
            yield n
        a, b = b, a + b


def A306360_gen(startvalue=1):  # generator of terms
    for k in count(max(startvalue, 1)):
        s = str(k)
        l, c = len(s), 0
        for i in range(l):
            c = (c + int(s[i]) ** l) % k
        if c == 0:
            yield k


def A319651(n):
    return int("".join(sorted(gmpy2digits(n, 3), reverse=True)), 3)


def A331761(n):
    return (n - 1) ** 2 + 2 * sum(
        totient(i) * (n + 1 - 2 * i) * (n + 1 - i) for i in range(2, n // 2 + 1)
    )


def A011772(n):
    plist = tuple(p**q for p, q in factorint(2 * n).items())
    return (
        2 * n - 1
        if len(plist) == 1
        else int(
            min(
                min(crt((m, 2 * n // m), (0, -1))[0], crt((2 * n // m, m), (0, -1))[0])
                for m in (
                    prod(d)
                    for l in range(1, len(plist) // 2 + 1)
                    for d in combinations(plist, l)
                )
            )
        )
    )


def A344590(n):
    m = A011772(n)
    return sum(1 for d in divisors(n) if A011772(d) == m)


def A345691(n):
    return pvariance(
        n**2 * (u**2 + v**2)
        for u, v, w in (igcdex(x, y) for x in range(1, n + 1) for y in range(1, n + 1))
    )


def A004730(n):
    a, b = factorial2(n), factorial2(n + 1)
    return a // gcd(a, b)


def A025281(n):
    return sum(p * e for p, e in factorint(factorial(n)).items())


def A029732_gen():
    return filter(isprime, pal_gen(16))


def A030292_gen(startvalue=0):
    return filter(lambda n: len(set(str(n**3))) <= 2, count(max(startvalue, 0)))


def A031749_gen(startvalue=1):
    return (
        n
        for n, d in filter(
            lambda x: isinstance(x[1], list) and min(x[1]) == 71,
            (
                (n, continued_fraction_periodic(0, 1, n)[-1])
                for n in count(max(startvalue, 1))
            ),
        )
    )


def A038529(n):
    return prime(n) - composite(n)


@lru_cache(maxsize=None)
def A046657(n):  # based on second formula in A018805
    if n == 0:
        return 0
    c, j = 0, 2
    k1 = n // j
    while k1 > 1:
        j2 = n // k1 + 1
        c += (j2 - j) * (4 * A046657(k1) - 1)
        j, k1 = j2, n // j2
    return (n * (n - 1) - c + j) // 4


def A048700(n):
    s = bin(n)[2:]
    return int(s + s[-2::-1], 2)


def A048890_gen():  # generator of terms
    for l in count(1):
        for e in "1689":
            for d in product("01689", repeat=l):
                s = e + "".join(d)
                p = int(s)
                if p > 0:
                    q = int(s[::-1].rstrip("0").translate("".maketrans("69", "96")))
                    if p != q and isprime(q) and isprime(p):
                        yield p


def A048943_gen(startvalue=1):
    return filter(
        lambda i: integer_nthroot(i, 4)[1] or not divisor_count(i) % 4,
        count(max(startvalue, 1)),
    )


def A053782_gen():  # generator of terms
    m, s, p = 4, 4, 5
    for n in count(1):
        if isprime(s):
            yield n
        m += 1
        if m == p:
            m += 1
            p = nextprime(p)
        s += m


def A055472_gen():
    return filter(isprime, (n * (n + 1) // 2 + 2 for n in count(0)))


def A059539(n):
    return integer_nthroot(3 * n**3, 3)[0]


def A064799(n):
    return prime(n) + composite(n)


def A068653_gen():  # generator of terms
    for l in count(1):
        for m in product(("1379" if l > 1 else "123579"), repeat=l):
            for d in "0123456789":
                s = "".join(m) + d
                n = int(s)
                if not isprime(n):
                    for k in range(len(s) - 1):
                        s = s[1:] + s[0]
                        if not isprime(int(s)):
                            break
                    else:
                        yield n


def A074200(n):
    a = lcm(range(1, n + 1))
    m = a
    while True:
        for k in range(n, 0, -1):
            if not isprime(m // k + 1):
                break
        else:
            return m
        m += a


def A074925_gen(startvalue=2):
    return filter(
        lambda i: prevprime(i**3 // 2) + nextprime(i**3 // 2) == i**3,
        count(max(startvalue + startvalue % 2, 2), 2),
    )


def A088104(n):
    return nextprime((p := prime(n)) * 10 ** (n - len(str(p))) - 1)


def A090693_gen():
    return (
        i
        for i, n in filter(
            lambda x: x[0] > 0 and isprime(x[1] + 2),
            enumerate(accumulate(range(10**5), lambda x, y: x + 2 * y - 3)),
        )
    )


def A091938(n):
    for i in range(n, -1, -1):
        q = 2**n
        for d in multiset_permutations("0" * (n - i) + "1" * i):
            p = q + int("".join(d), 2)
            if isprime(p):
                return p


def A099906(n):
    return comb(2 * n - 1, n - 1) % (n**2)


def A099908(n):
    return comb(2 * n - 1, n - 1) % (n**4)


@lru_cache(maxsize=None)
def A100613(n):  # based on second formula in A018805
    if n == 0:
        return 0
    c, j = 1, 2
    k1 = n // j
    while k1 > 1:
        j2 = n // k1 + 1
        c += (j2 - j) * (k1**2 - A100613(k1))
        j, k1 = j2, n // j2
    return n + c - j


def A104804_gen():  # generator of terms
    blist = [1, 3]
    yield from blist
    while True:
        i, j = isqrt_rem(blist[-1] ** 2 + blist[-2] ** 2)
        blist = blist[1:] + [int(i + int(4 * (j - i) >= 1))]
        yield blist[-1]


def A105870_gen():  # generator of terms
    a, b = 0, 1
    while True:
        yield a
        a, b = b, (a + b) % 7


def A107715_gen():
    return filter(isprime, (int(gmpy2digits(n, 4)) for n in count(0)))


def A116017_gen(startvalue=1):
    return filter(
        lambda n: len(set(str(n + sum(divisors(n))))) == 1, count(max(startvalue, 1))
    )


def A121943_gen():  # generator of terms
    b = 2
    for n in count(1):
        if not b % (n**2):
            yield n
        b = b * (4 * n + 2) // (n + 1)


def A163574_helper(n, b):
    if n == 1:
        t = list(range(1, b))
        for i in range(1, b):
            u = list(t)
            u.remove(i)
            yield i, u
    else:
        for d, v in A163574_helper(n - 1, b):
            for g in v:
                k = d * b + g
                if not k % n:
                    u = list(v)
                    u.remove(g)
                    yield k, u


def A163574(n):
    if n % 2:
        return 0
    for a, b in A163574_helper(n - 1, n):
        return a
    return 0


def A168294(n):
    s, t = [int(d) for d in str(n)], [int(d) for d in str(n + 1)]
    l, m = len(s), len(t)
    u = [0] * (l + m - 1)
    for i in range(l):
        for j in range(m):
            u[i + j] = (u[i + j] + s[i] * t[j]) % 10
    return int("".join(str(d) for d in u))


def A195527_gen(startvalue=1):  # generator of terms
    for m in count(max(startvalue, 1)):
        n, c = 3, 0
        while n * (n + 1) <= 2 * m:
            if not 2 * (n * (n - 2) + m) % (n * (n - 1)):
                c += 1
                if c > 2:
                    break
            n += 1
        if c == 2:
            yield m


def A195528_gen(startvalue=1):  # generator of terms
    for m in count(max(startvalue, 1)):
        n, c = 3, 0
        while n * (n + 1) <= 2 * m:
            if not 2 * (n * (n - 2) + m) % (n * (n - 1)):
                c += 1
                if c > 3:
                    break
            n += 1
        if c == 3:
            yield m


def A196368(n):
    return int(all(str(n)[i] != str(n)[i - 1] for i in range(1, len(str(n)))))


def A216822_gen(startvalue=1):
    return filter(
        lambda n: n == 1 or pow(2, n, n * (n + 1)) == 2, count(max(startvalue, 1))
    )


def A226459(n):
    return sum(totient(d) * d ** (d - 1) for d in divisors(n, generator=True))


def A241206(n):
    for i in range(9, 0, -1):
        x = i * (10**n - 1) // 9
        for j in range(n - 1, -1, -1):
            for k in range(9 - i, -1, -1):
                y = x + k * (10**j)
                if isprime(y):
                    return y
        for j in range(n):
            for k in range(1, i + 1):
                if j < n - 1 or k < i:
                    y = x - k * (10**j)
                    if isprime(y):
                        return y


def A247012_gen(startvalue=2):  # generator of terms
    for n in count(max(startvalue, 2)):
        if not isprime(n):
            m = int(str(n)[::-1])
            x = divisors(n)
            x.pop()
            y = divisor_sigma(n) - n
            while y < m:
                x, y = x[1:] + [y], 2 * y - x[0]
            if y == m:
                yield n


def A247219_gen(startvalue=2):
    return filter(lambda n: pow(2, n, n * n - 1) == 1, count(max(startvalue, 2)))


def A252022_gen():  # generator of terms
    l, s, b = [1], 2, set()
    yield 1
    while True:
        i = s
        while True:
            if i not in b:
                li = [int(d) for d in str(i)[::-1]]
                for x, y in zip(li, l):
                    if x + y > 9:
                        break
                else:
                    l = li
                    b.add(i)
                    yield i
                    while s in b:
                        b.remove(s)
                        s += 1
                    break
            i += 1


def A253046(n):
    q2, r2 = divmod(n, 2)
    if not r2 and isprime(q2):
        return 3 * nextprime(q2)
    else:
        q3, r3 = divmod(n, 3)
        if not r3 and isprime(q3):
            return 2 * prevprime(q3)
        return n


def A259089(n):
    s, k2 = "2" * n, 1
    for k in count(0):
        if s in str(k2):
            return k
        k2 *= 2


def A267763_gen():
    return (
        int(d, 3)
        for d in filter(lambda d: max(d) < "3", (str(i**2) for i in count(0)))
    )


def A269784_gen():  # generator of terms
    j = -5
    for i in count(0):
        if isprime(j):
            yield j
        j += 4 * (i + 1)


def A286262_gen(startvalue=0):
    return filter(lambda n: is_cubefree_string(bin(n)[2:]), count(max(startvalue, 0)))


def A291626_gen(startvalue=1):
    return filter(lambda k: min(str(k**2)) == "1", count(max(startvalue, 1)))


def A291630_gen(startvalue=1):
    return filter(lambda k: min(str(k**2)) == "5", count(max(startvalue, 1)))


def A291644_gen(startvalue=1):
    return filter(lambda k: min(str(k**3)) == "5", count(max(startvalue, 1)))


def A322131(n):
    return int("".join(str(int(d) * 2) for d in str(n)))


def A332584(n):
    r, m = n, n + 1
    while True:
        r = r * 10 ** (len(str(m))) + m
        if m % 2 == 0 and r % (m + 1) == 0:
            return m
        m += 1


def A338228(n):
    return n - divisor_count(isqrt(n // numbercore(n, 2)))


def A338231(n):
    return n * (n + 1) // 2 - divisor_sigma(isqrt(n // numbercore(n, 2)))


def A338233(n):
    return 0 if n <= 1 else n - 1 - divisor_count(isqrt(n // numbercore(n, 2)))


def A338234(n):
    return (
        0 if n <= 1 else n * (n - 1) // 2 - divisor_sigma(isqrt(n // numbercore(n, 2)))
    )


def A338236(n):
    return isqrt(n) - divisor_count(isqrt(n // numbercore(n, 2)))


def A344993(n):
    return 2 * n * (n + 1) + 2 * sum(
        totient(i) * (n + 1 - i) * (2 * n + 2 - i) for i in range(2, n + 1)
    )


def A345428(n):
    return sum(
        u + v
        for u, v, w in (igcdex(x, y) for x in range(1, n + 1) for y in range(1, n + 1))
    )


def A345434(n):
    return sum(
        u**2 + v**2
        for u, v, w in (igcdex(x, y) for x in range(1, n + 1) for y in range(1, n + 1))
    )


def A347306(n):
    if n == 1:
        return 1
    i, j, nset, m = 1, 2, {1}, 2
    while True:
        k = m
        i += 1
        while k == j or gcd(k, j) == 1 or k in nset:
            k += 1
        if k == n:
            return i
        j = k + 1
        nset.add(k)
        while m in nset:
            m += 1


def A347307_gen():  # generator of terms
    yield 1
    nset, m, c, j = {1}, 2, 0, 2
    while True:
        k = m
        while k == j or gcd(k, j) == 1 or k in nset:
            k += 1
        if k > c:
            c = k
            yield k
        j = k + 1
        nset.add(k)
        while m in nset:
            m += 1


def A348004_gen(startvalue=1):  # generator of terms
    for n in count(max(startvalue, 1)):
        pset = set()
        for d in udivisors(n, generator=True):
            u = prod(p**e - 1 for p, e in factorint(d).items())
            if u in pset:
                break
            pset.add(u)
        else:
            yield n


def A001962(n):
    return 3 * n + isqrt(5 * n**2)


@lru_cache(maxsize=None)
def A015634(n):
    if n == 0:
        return 0
    c, j = 1, 2
    k1 = n // j
    while k1 > 1:
        j2 = n // k1 + 1
        c += (j2 - j) * A015634(k1)
        j, k1 = j2, n // j2
    return n * (n + 1) * (n + 2) * (n + 3) // 24 - c + j - n


@lru_cache(maxsize=None)
def A025523(n):
    if n == 0:
        return 1
    c, j = 2, 2
    k1 = n // j
    while k1 > 1:
        j2 = n // k1 + 1
        c += (j2 - j) * A025523(k1)
        j, k1 = j2, n // j2
    return n + c - j


def A051572_gen():
    return accumulate(repeat(5), lambda x, _: divisor_sigma(x))


def A057436_gen():
    return (int("".join(d)) for l in count(1) for d in product("123456", repeat=l))


def A060984_gen():
    return accumulate(repeat(1), lambda x, _: x + isqrt(x) ** 2)


def A066058(n):
    if n > 0:
        for k in count(0):
            m = k
            for i in range(n):
                s1 = format(m, "b")
                s2 = s1[::-1]
                if s1 == s2:
                    break
                m += int(s2, 2)
            else:
                s1 = format(m, "b")
                if s1 == s1[::-1]:
                    return k
    else:
        return 0


def A066452(n):
    return len(
        [
            x
            for x in range(1, n)
            if all(
                [x % d for d in range(2, n) if (n % d) and (2 * n) % d in [d - 1, 0, 1]]
            )
        ]
    )


def A067872(n):
    y, x, n2 = n * (n + 2), 2 * n + 3, n**2
    m, r = divmod(y, n2)
    while r:
        y += x
        x += 2
        m, r = divmod(y, n2)
    return m


def A071220_gen():  # generator of terms
    for i in count(2):
        n = i**3
        m = n // 2
        if not isprime(m) and prevprime(m) + nextprime(m) == n:
            yield primepi(m)


def A071295(n):
    return bin(n)[1:].count("0") * bin(n).count("1")


def A078567(n):
    return (
        (m := isqrt(n - 1)) ** 2 * (1 + m) ** 2 // 4
        - m**2 * n
        + sum((n - 1) // i * (2 * n - i * (1 + (n - 1) // i)) for i in range(1, m + 1))
    )


def A082806_gen():
    return filter(
        lambda n: isprime(n) and isprime(sum(int(d) for d in str(n))), pal10_gen()
    )


def A085513(n):
    return num2words(n).count("e")


def A085831(n):
    return (lambda m, r: 2 * sum(r // k for k in range(1, m + 1)) - m * m)(
        isqrt(2**n), 2**n
    )


def A088754(n):
    p = prime(n)
    m = n - len(str(p))
    return primepi((p + 1) * 10**m) - primepi(p * 10**m)


def A113630(n):
    return (
        n * (n * (n * (n * (n * (n * (n * (9 * n + 8) + 7) + 6) + 5) + 4) + 3) + 2) + 1
    )


def A113963_gen():  # generator of terms
    bset, b = {1}, 1
    yield b
    while True:
        a = 1
        while a in bset or not (a + b) % (a - b):
            a += 1
        b = a
        yield b
        bset.add(b)


def A350034(n):
    return n // g if (g := gcd(n, 6)) > 1 else 5 * n + 1


def A350265(n):
    return hyperexpand(hyper((-n - 1, 1 - n, -n), (1, 3), -1))


def A115510_gen():  # generator of terms
    yield 1
    l1, s, b = 1, 2, set()
    while True:
        i = s
        while True:
            if i & l1 and not i in b:
                yield i
                l1 = i
                b.add(i)
                while s in b:
                    b.remove(s)
                    s += 1
                break
            i += 1


def A116018_gen(startvalue=1):
    return filter(
        lambda n: len(set(str(n + totient(n)))) == 1, count(max(startvalue, 1))
    )


def A125289_gen(startvalue=0):
    return filter(lambda n: len(set(str(n)) - {"0"}) == 1, count(max(startvalue, 0)))


def A138918_gen():
    return (
        a
        for a, b in filter(
            lambda x: not x[1], (divmod(prime(n) + 1, 18) for n in count(1))
        )
    )


def A161664(n):
    return (
        lambda m: n * (n + 1) // 2 + m * m - 2 * sum(n // k for k in range(1, m + 1))
    )(isqrt(n))


def A161886(n):
    return (lambda m: 2 * sum(n // k for k in range(1, m + 1)) + n - 1 - m * m)(
        isqrt(n)
    )


def A166623_gen():  # generator of terms
    for b in count(2):
        sublist = []
        for l in range(1, b + 2):
            for n in combinations_with_replacement(range(b), l):
                x = sum(d**d for d in n)
                if tuple(sorted(sympydigits(x, b)[1:])) == n:
                    sublist.append(x)
        yield from sorted(sublist)


def A189398(n):
    return prod(prime(i) ** int(d) for i, d in enumerate(str(n), start=1))


def A191610_gen():
    return chain((0,), accumulate(multiplicity(5, n) for n in count(5, 5)))


def A191871(n):
    return 0 if n == 0 else (n // 2 ** multiplicity(2, n)) ** 2


if sys.version_info >= (3, 10):

    def A192085(n):
        return (n**3).bit_count()

else:

    def A192085(n):
        return bin(n**3).count("1")


def A192293_gen(startvalue=1):
    return filter(
        lambda n: 3 * n == sum(antidivisors(sum(antidivisors(n)))),
        count(max(startvalue, 1)),
    )


def A206578(n):
    m = 1
    while True:
        s = continued_fraction_periodic(0, 1, m)[-1]
        if isinstance(s, list) and s.count(1) == n:
            return m
        m += 1


def A212526(n):
    s, q = "", -n
    while q >= 4 or q < 0:
        q, r = divmod(q, -4)
        if r < 0:
            q += 1
            r += 4
        s += str(r)
    return int(str(q) + s[::-1])


def A217465_gen(startvalue=1):
    return filter(
        lambda n: pow(2, n, n * (n + 1)) == 2 and not isprime(n),
        count(max(startvalue, 1)),
    )


def A219326_gen(startvalue=1):
    for n in count(max(startvalue, 1)):
        s = [int(d) for d in str(n)][::-1]
        m = len(s)
        if n == Matrix(m, m, lambda i, j: s[(i - j) % m]).det():
            yield n


def A236174(n):
    p = prime(n)
    for b in range(2, 11):
        x, y, z = p, 0, 1
        while x >= b:
            x, r = divmod(x, b)
            y += r * z
            z *= 10
        y += x * z
        if isprime(y):
            return y


if sys.version_info >= (3, 10):

    def A245788(n):
        return n * n.bit_count()

else:

    def A245788(n):
        return n * bin(n).count("1")


def A246029(n):
    return (
        prod(prime(len(d)) for d in split("0+", bin(n)[2:]) if d != "") if n > 0 else 1
    )


def A246593(n):
    s = bin(n)[2:]
    s2 = s.rstrip("0")
    s3 = s2.lstrip("1")
    return (
        int(s2[: -len(s3)] + "1" + s3[1:-1] + "0" + s[len(s2) :], 2)
        if (len(s3) > 0 and n > 1)
        else n
    )


def A246824_gen():
    return (
        a
        for a, b in ((n, prime(n) + 1) for n in count(3))
        if (
            not (isprime(b**2 - 1) and isprime(b**2 + 1))
            and (min(factorint(b**2 + 1)) > min(factorint(b**2 - 1)) >= b - 1)
        )
    )


def A247248(n):
    if n == 1:
        return 1
    else:
        x, k, kr = 1, 0, 0
        while (x + kr) % n:
            x, kr = (2 * x) % n, (kr + 1) % n
            k += 1
        return k


def A247647_gen():
    return (int(bin(n)[2:]) for n in count(1) if n % 2 and not "00" in bin(n))


def A248909(n):
    return prod((1 if (p - 1) % 6 else p) ** e for p, e in factorint(n).items())


def A259091(n):
    s, k, k2 = str(n) * 2, 0, 1
    while True:
        if s in str(k2):
            return k
        k += 1
        k2 *= 2


def A259092(n):
    s, k, k2 = str(n) * 3, 0, 1
    while True:
        if s in str(k2):
            return k
        k += 1
        k2 *= 2


def A261018_gen():  # generator of terms
    a = 1
    for i in count(0):
        b, s = 1, format(a, "b")
        while format(b, "b") in s:
            b += 1
        a += b
        s = format(a, "b")
        yield b


def A264596(n):
    return sorted(format(i, "b")[::-1] for i in range(n + 1)).index(
        format(n, "b")[::-1]
    )


def A267490_gen():
    return (
        int(s, 8)
        for s in (str(i**2) for i in count(0))
        if max(s) < "8" and isprime(int(s, 8))
    )


def A268412_gen(startvalue=0):
    return (
        i
        for i in count(max(startvalue, 0))
        if not len(list(filter(bool, format(i, "b").split("0")))) % 2
    )


def A268415_gen(startvalue=0):
    return (
        i
        for i in count(max(startvalue, 0))
        if len(list(filter(bool, format(i, "b").split("0")))) % 2
    )


def A275256_gen():  # generator of terms
    for m in count(2):
        n, c = 3, 0
        while (n * (n + 1)) <= 2 * m:
            if not 2 * (n * (n - 2) + m) % (n * (n - 1)):
                c += 1
                if c >= 6:
                    break
            n += 1
        if c >= 6:
            yield m


def A275600_gen():
    return (
        n
        for n in (int(gmpy2digits(m, 3), 6) for m in range(10**6))
        if max(gmpy2digits(n, 5)) <= "2" and max(gmpy2digits(n, 4)) <= "2"
    )


def A276854(n):
    return n + isqrt(5 * n**2)


def A289676(n):
    c, k, r, n2, cs, ts = (
        0,
        1 + (n - 1) // 3,
        2 ** ((n - 1) % 3),
        2 ** (n - 1),
        set(),
        set(),
    )
    for i in range(2**k):
        j, l = int(bin(i)[2:], 8) * r, n2
        traj = set([(l, j)])
        while True:
            if j >= l:
                j = j * 16 + 13
                l *= 2
            else:
                j *= 4
                l //= 2
            if l == 0:
                c += 1
                ts |= traj
                break
            j %= 2 * l
            if (l, j) in traj:
                cs |= traj
                break
            if (l, j) in cs:
                break
            if (l, j) in ts:
                c += 1
                break
            traj.add((l, j))
    return c


def A291625_gen(startvalue=1):
    return (k for k in count(max(startvalue, 1)) if "0" in str(k**2))


def A301273_gen():  # generator of terms
    mu = Fraction(0)
    for i in count(1):
        mu += (prime(i) - mu) / i
        yield mu.numerator


def A301273(n):
    return (p := sum(prime(i) for i in range(1, n + 1))) // gcd(p, n)


def A301274_gen():  # generator of terms
    mu = Fraction(0)
    for i in count(1):
        mu += (prime(i) - mu) / i
        yield mu.denominator


def A301274(n):
    return n // gcd(n, sum(prime(i) for i in range(1, n + 1)))


def A301275_gen():  # generator of terms
    yield 0
    mu, variance = Fraction(prime(1)), Fraction(0)
    for i in count(2):
        datapoint = prime(i)
        newmu = mu + (datapoint - mu) / i
        variance = (variance * (i - 2) + (datapoint - mu) * (datapoint - newmu)) / (
            i - 1
        )
        mu = newmu
        yield variance.numerator


def A301276_gen():  # generator of terms
    yield 1
    mu, variance = Fraction(prime(1)), Fraction(0)
    for i in count(2):
        datapoint = prime(i)
        newmu = mu + (datapoint - mu) / i
        variance = (variance * (i - 2) + (datapoint - mu) * (datapoint - newmu)) / (
            i - 1
        )
        mu = newmu
        yield variance.denominator


@lru_cache(maxsize=None)
def A304176_helper(n, i):
    return (
        1
        if n == 0 or i == 1
        else A304176_helper(n, i - 1) + A304176_helper(n - i, min(i, n - i))
    )


def A304176(n):
    return A304176_helper(n**3 - n, n)


def A306612(n):
    plist, x = [prime(i) for i in range(1, n + 1)], 3
    rlist = [-x % p for p in plist]
    while True:
        for i in range(n - 1):
            if rlist[i] >= rlist[i + 1]:
                break
        else:
            return x
        for i in range(n):
            rlist[i] = (rlist[i] - 1) % plist[i]
        x += 1


def A308190(n):
    c, x = 0, n
    while x != 5:
        y = min(factorint(x))
        x = y + x // y
        c += 1
    return c


def A317058_helper(n, p, q):  # compute (-n + sum_{k=1,n} k^p) mod q
    c = (-n) % q
    for k in range(1, n + 1):
        c = (c + pow(k, p, q)) % q
    return c


def A317058(n):
    k = 2
    while isprime(k) or A317058_helper(n, k - 1, k):
        k += 1
    return k


def A320037(n):
    return int(
        "".join(
            d + "0" if "1" in d else d + "1"
            for d in split("(0+)|(1+)", bin(n)[2:])
            if d != "" and d != None
        ),
        2,
    )


def A320038(n):
    return int(
        "".join(
            "0" + d if "1" in d else "1" + d
            for d in split("(0+)|(1+)", bin(n)[2:])
            if d != "" and d != None
        ),
        2,
    )


def A321005_gen():  # generator of terms
    plist = [2]
    for n in count(0):
        c, p = 0, plist[-1]
        for j in range(n):
            pj = plist[j]
            for i in range(j):
                if (plist[i] * pj) % p == 1:
                    c += 1
        yield c
        plist.append(nextprime(p))


def A321801(n):
    return int(
        "0"
        + "".join(
            d if len(d) == 1 else ""
            for d in split("(0+)|(1+)|(2+)|(3+)|(4+)|(5+)|(6+)|(7+)|(8+)|(9+)", str(n))
            if d != "" and d != None
        )
    )


def A321802(n):
    return (lambda x: int(x) if x != "" else -1)(
        "".join(
            d if len(d) == 1 else ""
            for d in split("(0+)|(1+)|(2+)|(3+)|(4+)|(5+)|(6+)|(7+)|(8+)|(9+)", str(n))
            if d != "" and d != None
        )
    )


def A323832_helper(n):
    x = 2 * n
    y = A321801(x)
    while x != y:
        x, y = y, A321801(y)
    return x


def A323832(n):
    mset, m, c = set(), n, 0
    while True:
        if m == 1 or m == 0 or m == 5:
            return c
        m = A323832_helper(m)
        if m in mset:
            return -1
        mset.add(m)
        c += 1


def A325148_gen(startvalue=0):  # generator of terms
    if startvalue == 0:
        yield 0
    j = isqrt(startvalue)
    if j * j < startvalue:
        j += 1
    for n in count(max(j, 0)):
        n2 = n**2
        for m in divisors(n2):
            if m > n:
                break
            if m == int(str(n2 // m)[::-1]):
                yield n2
                break


def A338434(n):
    m = integer_nthroot(n, 2)[0]
    return m * (m + 1) // 2 - divisor_sigma(
        integer_nthroot(n // numbercore(n, 2), 2)[0]
    )


def A342068(n):
    k, a, b, c = 2, 0, primepi(n), primepi(2 * n)
    while a + c <= 2 * b:
        k += 1
        a, b, c = b, c, primepi(k * n)
    return k


def A345422(n):
    return igcdex(11, prime(n))[0]


def A345692(n):
    zlist = [
        z
        for z in (igcdex(x, y) for x in range(1, n + 1) for y in range(1, n + 1))
        if z[2] == 1
    ]
    return pvariance(len(zlist) * u for u, v, w in zlist)


def A346004(n):
    return ((n + 1) // 2) ** 2 if n % 2 else n


def A347042(n):
    fs = factorint(n, multiple=True)
    return sum(
        len(list(multiset_combinations(fs, d)))
        for d in divisors(len(fs), generator=True)
    )


def A347045(n):
    fs = factorint(n, multiple=True)
    q, r = divmod(len(fs), 2)
    return 1 if r else prod(fs[:q])


def A347046(n):
    fs = factorint(n, multiple=True)
    q, r = divmod(len(fs), 2)
    return 1 if r else prod(fs[q:])


def A008849_gen(startvalue=1):
    return filter(
        lambda n: is_square(
            prod((p ** (3 * q + 1) - 1) // (p - 1) for p, q in factorint(n).items())
        ),
        count(max(startvalue, 1)),
    )


def A011966_gen():  # generator of terms
    yield 1
    blist, b = [2, 3, 5], 5
    while True:
        blist = list(accumulate([b] + blist))
        b = blist[-1]
        yield blist[-4]


def A011969_gen():  # generator of terms
    yield from [1, 3]
    blist, b, b2 = [1], 1, 1
    while True:
        blist = list(accumulate([b] + blist))
        yield 2 * b + b2 + blist[-1]
        b2, b = b, blist[-1]


@lru_cache(maxsize=None)
def A015616(n):
    if n <= 1:
        return 0
    c, j = n * (n - 1) * (n - 2) // 6, 2
    k1 = n // j
    while k1 > 1:
        j2 = n // k1 + 1
        c -= (j2 - j) * A015616(k1)
        j, k1 = j2, n // j2
    return c


@lru_cache(maxsize=None)
def A015650(n):
    if n == 0:
        return 0
    c, j = n + 1, 2
    k1 = n // j
    while k1 > 1:
        j2 = n // k1 + 1
        c += (j2 - j) * A015650(k1)
        j, k1 = j2, n // j2
    return n * (n + 1) * (n + 2) * (n + 3) * (n + 4) // 120 - c + j


def A336643(n):
    return prod(primefactors(n)) // numbercore(n)


def A336644(n):
    return (n - prod(primefactors(n))) // numbercore(n)


def A350390(n):
    return n * numbercore(n) // prod(primefactors(n))


def A008833(n):
    return n // numbercore(n)


def A016070_gen(startvalue=1):
    return filter(
        lambda n: len(s := set(str(n**2))) == 2
        and s not in [{"0", "1"}, {"0", "4"}, {"0", "9"}],
        count(max(startvalue, 1)),
    )


def A017714(n):
    return comb(n, 50)


def A022519_gen():  # generator of terms
    b = 8
    while True:
        yield b
        b = int("".join(str(k) + str(len(list(g))) for k, g in groupby(str(b)[::-1])))


def A025502(n):
    m, tlist, s = 10**n, [1, 2], 0
    while tlist[-1] + tlist[-2] <= m:
        tlist.append(tlist[-1] + tlist[-2])
    for d in tlist[::-1]:
        if d <= m:
            s += 1
            m -= d
    return s


def A028820_gen():
    return chain(
        (0,),
        (
            n
            for n in (
                int("".join(i))
                for l in count(1)
                for i in combinations_with_replacement("123456789", l)
            )
            if is_square(n)
        ),
    )


def A030666(n):
    d, nd = 10, 10 * n
    while True:
        x = (isqrt(nd - 1) + 1) ** 2
        if x < nd + d:
            return int(x)
        d *= 10
        nd *= 10


def A046358_gen(startvalue=2):
    return (
        n
        for n in count(max(startvalue, 2))
        if not isprime(n)
        and not n % (m := sum(p * e for p, e in factorint(n).items()))
        and str(m) == str(m)[::-1]
    )


def A047972(n):
    return min((p := prime(n)) - (a := isqrt(p)) ** 2, (a + 1) ** 2 - p)


def A052072(n):
    a, b, c = 0, 0, 0
    for i in count(0):
        s = str(c)
        for d in set(s):
            if s.count(d) != n:
                break
        else:
            return c
        c += a + b + 1
        b += 2 * a + 3
        a += 3


def A052091_gen():  # generator of terms
    yield 2
    p = 2
    while True:
        m, ps = 1, str(p)
        s = int("1" + ps + "1")
        while not isprime(s):
            m += 1
            ms = str(m)
            if ms[0] in "268":
                ms = str(int(ms[0]) + 1) + "0" * (len(ms) - 1)
                m = int(ms)
            if ms[0] in "45":
                ms = "7" + "0" * (len(ms) - 1)
                m = int(ms)
            s = int(ms + ps + ms[::-1])
        p = s
        yield m


def A052092_gen():  # generator of terms
    yield 1
    l, p = 1, 2
    while True:
        m, ps = 1, str(p)
        s = int("1" + ps + "1")
        while not isprime(s):
            m += 1
            ms = str(m)
            if ms[0] in "268":
                ms = str(int(ms[0]) + 1) + "0" * (len(ms) - 1)
                m = int(ms)
            if ms[0] in "45":
                ms = "7" + "0" * (len(ms) - 1)
                m = int(ms)
            s = int(ms + ps + ms[::-1])
        p = s
        l += 2 * len(ms)
        yield l


def A063095(n):
    c, p = 0, 2
    for i in range(n):
        q = nextprime(p)
        c, p = max(c, q - p), q
    return c


def A063527_gen():  # generator of terms
    for g in count(1):
        for n in product("123456789", repeat=g):
            s = "".join(n)
            m = int(s)
            if not any([m % int(d) for d in s]):
                for i in range(len(s) - 1):
                    if m % int(s[i : i + 2]):
                        break
                else:
                    yield m


def A067563(n):
    return prime(n) * composite(n)


def A068084(n):
    u, v, t = 4 * (n + 1), (2 * (n + 1)) ** 2 - 1, 4 * n * (n + 1)
    while True:
        if not v % t:
            return v // 8
        v += u + 1
        u += 2


def A069706_gen():  # generator of terms
    yield from [2, 3, 5, 7]
    for i in count(5):
        p = prime(i)
        s = str(p)
        if isprime(int(s[-1] + s[1:-1] + s[0])):
            yield p


def A075075_gen():  # generator of terms
    yield from [1, 2]
    l1, m, b = 2, 2, {1, 2}
    while True:
        i = m
        while True:
            if not i in b:
                yield i
                l1, m = i, i // gcd(l1, i)
                b.add(i)
                break
            i += m


def A080478_gen():  # generator of terms
    yield 1
    a = 1
    while True:
        a += 1
        b = 2 * a * (a - 1) + 1
        while not isprime(b):
            b += 4 * (a + 1)
            a += 2
        yield a


def A091507(n):
    return prod(d for d in range(2, n) if n % d and 2 * n % d in [d - 1, 0, 1])


def A094685(n):
    i, j = isqrt_rem(n**3 if n % 2 else n)
    return int(i + int(4 * (j - i) >= 1))


def A100384(n):
    k, a = 2, [max(factorint(m + 2)) for m in range(n)]
    while True:
        for i in range(1, n):
            if a[i - 1] >= a[i]:
                break
        else:
            return k
        a = a[i:] + [max(factorint(k + j + n)) for j in range(i)]
        k += i


def A104301_gen():  # generator of terms
    for n in count(1):
        x = int(str((n + 1) ** 2) + str(n**2))
        if isprime(x):
            yield x


def A110713(n):
    return len(
        {prod(d) for d in combinations_with_replacement(list(range(1, n + 1)), n)}
    )


def A114065_gen(startvalue=1):
    return (
        n
        for n in count(max(startvalue, 1))
        if sorted(str(divisor_sigma(n))) == sorted(str(totient(n))) == sorted(str(n))
    )


def A117345_gen():  # generator of terms
    plist = [2, 3, 5, 7, 11, 13, 17, 19, 23]
    for k in count(1):
        if Matrix(plist).reshape(3, 3).det() == 0:
            yield k
        plist = plist[1:] + [nextprime(plist[-1])]


def A117960():
    return filter(
        lambda n: set(str(n)) <= {"1", "3", "5", "7", "9"},
        (m * (m + 1) // 2 for m in count(0)),
    )


def A119908_gen():  # generator of terms
    c, s = {}, 3
    for n in count(2):
        for p, e in factorint(4 * n - 2).items():
            if p in c:
                c[p] += e
            else:
                c[p] = e
        for p, e in factorint(n + 1).items():
            if c[p] == e:
                del c[p]
            else:
                c[p] -= e
        if n == s:
            c2 = [p for p, e in c.items() if e >= 2]
            yield 1 if c2 == [] else max(c2)
            s = 2 * s + 1


def A130334(n):
    k, Tn, Tm = n + 1, n * (n + 1) // 2, (n + 1) * (n + 2) // 2
    while gcd(Tn, Tm) != 1:
        k += 1
        Tm += k
    return k


@lru_cache(maxsize=None)
def A137243(n):
    if n == 0:
        return 0
    c, j = 0, 2
    k1 = n // j
    while k1 > 1:
        j2 = n // k1 + 1
        c += (j2 - j) * (A137243(k1) // 4 - 1)
        j, k1 = j2, n // j2
    return 4 * (n * (n - 1) - c + j)


def A155150_gen(startvalue=1):
    return filter(lambda n: len(set(str(n**4))) == 4, count(max(startvalue, 1)))


def A175795_gen(startvalue=1):
    return (
        n
        for n in count(max(startvalue, 1))
        if sorted(str(divisor_sigma(n))) == sorted(str(totient(n)))
    )


def A178029_gen(startvalue=1):
    return (
        n
        for n in count(max(startvalue, 1))
        if sum([d for d in range(2, n) if (n % d) and (2 * n) % d in [d - 1, 0, 1]])
        == sum(divisors(n))
    )


def A185704(n):
    p, k, m = 2, 73**n, 10
    q, m2 = p % k, m % k
    while True:
        p = nextprime(p)
        while p >= m:
            m *= 10
            m2 = m % k
        q = (q * m2 + p) % k
        if q == 0:
            return p


def A188187(n):
    return isqrt(5 * n**2) - isqrt(5 * (n - 1) ** 2) - 2


def A206585(n):
    i = 2
    while True:
        s = continued_fraction_periodic(0, 1, i)[-1]
        if isinstance(s, list) and s.count(5) == n:
            return i
        i += 1


def A209252(n):
    return len(
        [
            1
            for i in range(len(str(n)))
            for d in "0123456789"
            if d != str(n)[i] and isprime(int(str(n)[:i] + d + str(n)[i + 1 :]))
        ]
    )


def A214560(n):
    return bin(n * n)[2:].count("0")


def A214842_gen(startvalue=1):
    return (
        n
        for n in count(max(startvalue, 1))
        if not (
            sum([d for d in range(2, n, 2) if n % d and not 2 * n % d])
            + sum([d for d in range(3, n, 2) if n % d and 2 * n % d in [d - 1, 1]])
        )
        % n
    )


def A215199(n):
    l = len(str(3**n)) - 1
    l10, result = 10**l, 2 * 10**l
    while result >= 2 * l10:
        l += 1
        l102, result = l10, 20 * l10
        l10 *= 10
        q, qn = 2, 2**n
        while qn <= l10:
            s, sn = 2, 2**n
            while sn <= l10:
                if s != q:
                    a, b = crt([qn, sn], [0, 1])
                    if a <= l102:
                        a = b * (l102 // b) + a
                    while a < l10:
                        p, t = a // qn, (a - 1) // sn
                        if p != q and t != s and isprime(p) and isprime(t):
                            result = min(result, a - 1)
                        a += b
                s = nextprime(s)
                sn = s**n
            q = nextprime(q)
            qn = q**n
    return result


def A215659_gen():  # generator of terms
    for i in count(1):
        a, b = integer_nthroot(4 * primorial(i) + 1, 2)
        if b:
            yield (a + 1) // 2


def A218013_gen(startvalue=1):
    return (
        n
        for n in count(max(startvalue, 1))
        if not prod(int(d) for d in str(n**2) if d != "0") % n
    )


def A228410_gen():  # generator of terms
    yield 1
    l, s, b = Counter("1"), 2, set()
    while True:
        i = s
        while True:
            if i not in b:
                li, o = Counter(str(i)), 0
                for d in (l + li).values():
                    if d % 2:
                        if o > 0:
                            break
                        o += 1
                else:
                    yield i
                    l = li
                    b.add(i)
                    while s in b:
                        b.remove(s)
                        s += 1
                    break
            i += 1


def A228768(n):
    m = 1
    while True:
        m = nextprime(m)
        for b in range(2, n + 1):
            if not is_emirp(m, b):
                break
        else:
            return m


def A235807_gen(startvalue=0):
    return filter(lambda n: len(set(str(n**3))) == 5, count(max(startvalue, 0)))


def A236437_gen():
    return (p for n in count(1) if A236174(n) == (p := prime(n)))


def A240960_gen():
    return filter(
        lambda x: sum(divisors(x)) - totient(x)
        == divisor_count(x) ** len(primefactors(x)),
        count(1),
    )


def A242788_gen():
    return chain((1, 2, 4, 5, 6), (n for n in count(7) if pow(n, n, n - 3) == 3))


def A246198_gen(startvalue=2):  # generator of terms
    for n in count(max(startvalue, 2)):
        d = divisors(n)
        d.remove(n)
        s, dmax = sum(d), max(d)
        if not s % 2 and 2 * dmax <= s:
            d.remove(dmax)
            s2 = s / 2 - dmax
            for x in range(2 ** len(d)):
                if sum(Subset.unrank_binary(x, d).subset) == s2:
                    yield n
                    break


def A246591(n):
    if n <= 1:
        return n
    else:
        s = bin(n)[2:]
        l = len(s)
        y = 2**l - 1
        for i in combinations(range(l), 2):
            s2 = int(
                s[: i[0]] + s[i[1]] + s[i[0] + 1 : i[1]] + s[i[0]] + s[i[1] + 1 :], 2
            )
            if s2 < y:
                y = s2
        return y


def A246592(n):
    s = bin(n)[2:]
    for i in range(len(s) - 1):
        if s[i : i + 2] == "10":
            return int(s[:i] + "01" + s[i + 2 :], 2)
    else:
        return n


def A246594(n):
    s = bin(n)[2:]
    for i in range(len(s) - 1):
        if s[i : i + 2] == "01":
            return int(s[:i] + "10" + s[i + 2 :], 2)
    else:
        return n


def A246714_gen():  # generator of terms
    yield 1
    c = 1
    for n in count(2):
        c = c * (4 * n - 2) // (n + 1)
        yield c % prime(n)


def A349949(n):
    return sum(
        1
        for m in filter(
            lambda d: not (
                ((n - 1) % (d - 1) if d > 1 else True)
                and (n - 1) % (d + 1)
                and ((n + 1) % (d - 1) if d > 1 else True)
                and (n + 1) % (d + 1)
            ),
            divisors(n, generator=True),
        )
    )


def A246830_gen():  # generator of terms
    for n in count(0):
        for k in range(n):
            yield int(bin(n - k)[2:] + bin(n + k)[2:], 2)
        yield 2 * n


def A246830_T(n, k):
    return int(bin(n - k)[2:] + bin(n + k)[2:], 2)


def A246972(n):
    return int(str((n + 1) ** 2) + str(n**2))


def A247013_gen(startvalue=2):  # generator of terms
    for n in count(max(startvalue, 2)):
        m = int(str(n)[::-1])
        if n % 10 and not isprime(n):
            x = sorted(chain.from_iterable([p] * e for p, e in factorint(n).items()))
            y = sum(x)
            while y < m:
                x, y = x[1:] + [y], 2 * y - x[0]
            if y == m:
                yield n


def A247190(n):
    p, f, fv = prime(n), 1, {}
    for i in range(2, p):
        f = (f * i) % p
        if f in fv:
            return fv[f]
        else:
            fv[f] = i
    else:
        return 0


def A247220_gen(startvalue=0):
    return (i for i in count(max(startvalue, 0)) if pow(2, i, i * i + 1) == i * i)


def A247358_gen():
    return chain.from_iterable(
        sorted((b + 1) ** (n - b) for b in range(n)) for n in count(1)
    )


def A251240_gen():  # generator of terms
    l1, l2, s, b = 3, 2, 4, {}
    for n in count(4):
        i = s
        while True:
            if not i in b and gcd(i, l1) == 1 and gcd(i, l2) > 1:
                l2, l1, b[i] = l1, i, 1
                while s in b:
                    b.pop(s)
                    s += 1
                k, l = integer_nthroot(i, 2)
                if l and is_prime(k):
                    yield n
                break
            i += 1


def A251555_gen():  # generator of terms
    yield from [1, 3, 2]
    l1, l2, s, b = 2, 3, 4, set()
    while True:
        i = s
        while True:
            if not i in b and gcd(i, l1) == 1 and gcd(i, l2) > 1:
                yield i
                l2, l1 = l1, i
                b.add(i)
                while s in b:
                    b.remove(s)
                    s += 1
                break
            i += 1


def A253050_gen():  # generator of terms
    yield from [0, 1, 0]
    l1, l2, s, b = 2, 1, 3, set()
    while True:
        i = s
        while True:
            if not (i in b or i & l1) and i & l2:
                yield i & 1
                l2, l1 = l1, i
                b.add(i)
                while s in b:
                    b.remove(s)
                    s += 1
                break
            i += 1


def A253412(n):
    c, fs = 0, "0" + str(n) + "b"
    for i in range(2**n):
        s = "01" + format(i, fs) + "10"
        for j in range(n):
            if (
                s[j : j + 4] == "0100"
                or s[j + 1 : j + 5] == "0010"
                or s[j + 1 : j + 4] == "000"
                or s[j + 1 : j + 4] == "111"
            ):
                break
        else:
            c += 1
    return c


def A253574_gen(startvalue=1):
    return (
        n
        for n in count(max(startvalue, 1))
        if set(str(n)) & set(str(n**4)) == set() and isprime(n)
    )


def A253646_gen(startvalue=2):  # generator of terms
    if startvalue <= 2:
        yield 2
    for i in count(max(startvalue, 3), 2):
        if not "0" in str(i):
            m = i
            for k in range(5):
                m *= i
                if "0" in str(m):
                    break
            else:
                if isprime(i):
                    yield i


def A254334_gen():
    return (
        int("".join(format(x, "02d") for x in sympydigits(3**i, 60)[1:]))
        for i in count(0)
    )


def A256229(n):
    y = 1
    for d in reversed(str(n)):
        y = int(d) ** y
    return y


def A257763_gen(startvalue=1):
    return (
        n
        for n in count(max(startvalue, 1))
        if not "0" in str(n) and set(str(n)) == set(str(n**2))
    )


def A257893_gen(startvalue=1):  # generator of terms
    l = []
    for d in permutations("0123456789", 10):
        if d[0] != "0":
            d2 = int("".join(d))
            if d2 >= startvalue:
                d = d2
                r = d2 % 2
                while not r:
                    d2, r = divmod(d2, 2)
                l.append((d2, d))
    l.sort()
    yield from (b for a, b in l)


def A270807_gen():  # generator of terms
    b = 1
    while True:
        yield b
        b += b // (max(primefactors(b) + [1])) + 1


def A271713_gen():
    return ((n**2 + 5) // 3 for n in count(0) if not (n**2 + 5) % 3)


def A272653_gen():
    return (
        int(b + "".join(s), 2)
        for b in (bin(n)[2:] for n in count(1))
        for s in multiset_permutations(sorted(b))
    )


def A272679(n):
    if n == 0:
        return 0
    else:
        d, nd = 1, n
        while True:
            x = isqrt(nd - 1) + 1
            if x**2 < nd + d:
                return int(x)
            d *= 2
            nd *= 2


def A276466(n):
    return sum(Fraction(d, 10 ** len(str(d))) for d in divisors(n)).numerator


def A279204(n):
    return int(str(n) + str(n + 1) + str(n + 2) + str(n + 3))


def A289776(n):
    i = 1
    while len(divisors(i)) < n or not isprime(sum(divisors(i)[:n])):
        i += 1
    return i


def A291301(n):
    m = primorial(n)
    while not isprime(m):
        m = divisor_sigma(m) - 1
    return m


def A291302(n):
    m, c = primorial(n), 0
    while not isprime(m):
        m = divisor_sigma(m) - 1
        c += 1
    return c


def A291672_gen(startvalue=1):
    return (k for k in count(max(startvalue, 1)) if min(str(k**4)) == "4")


def A298463_gen():  # generator of terms
    m = 6
    for n in count(1):
        k = prevprime(m // 2)
        if k + nextprime(k) == m:
            yield n * (3 * n - 1) // 2
        m += 6 * n - 1


def A298464_gen():  # generator of terms
    m = 6
    for n in count(1):
        k = prevprime(m // 2)
        if k + nextprime(k) == m:
            yield k
        m += 6 * n - 1


def A298465_gen():  # generator of terms
    m = 8
    for n in count(1):
        k = prevprime(m // 2)
        if k + nextprime(k) == m:
            yield n * (5 * n - 3) // 2
        m += 10 * n - 3


def A298466_gen():  # generator of terms
    m = 8
    for n in count(1):
        k = prevprime(m // 2)
        if k + nextprime(k) == m:
            yield k
        n += 1
        m += 10 * n - 3


def A303260(n):
    return Matrix(n, n, lambda i, j: (j - i - 1) % n + (i == j)).det()


def A306582(n):
    plist, rlist, x = [prime(i) for i in range(1, n + 1)], [0] * n, 0
    while True:
        for i in range(n - 1):
            if rlist[i] >= rlist[i + 1]:
                break
        else:
            return x
        for i in range(n):
            rlist[i] = (rlist[i] + 1) % plist[i]
        x += 1


def A316434(n):
    pp = primepi(n)
    return 1 if n == 1 or n == 2 else A316434(pp) + A316434(n - pp)


def A317357(n):
    k = n + 1
    while isprime(k) or A317058_helper(n, k - 1, k):
        k += 1
    return k


def A317358(n):
    k = 2
    while A317058_helper(n, k - 1, k):
        k += 1
    return k


def A326806_gen(startvalue=0):  # generator of terms
    for n in count(max(startvalue, 0)):
        sn = str(n)
        if sn in str(n * sum(int(d) for d in sn)):
            yield n


def A333548_gen():  # generator of terms
    bset, y = {0}, 0
    for n in count(1):
        y -= n
        if y <= 0 or y in bset:
            y += 2 * n
        bset.add(y)
        if y == n + 1:
            yield y


def A340740(n):
    return sum(n % k for k in range(1, n // 2 + 1) if gcd(k, n) == 1)


def A341656(n):
    return divisor_count(prime(n) ** 4 - 1)


def A343590_helper(w, dir):
    if dir == 1:
        for s in w:
            for t in range(int(s[-1]) + 1, 10, 2):
                yield s + str(t)
    else:
        for s in w:
            for t in range(1 - int(s[-1]) % 2, int(s[-1]), 2):
                yield s + str(t)


def A343590_gen():  # generator of terms
    for l in count(0):
        for d in "123456789":
            x = d
            for i in range(1, l + 1):
                x = A343590_helper(x, (-1) ** i)
            yield from (int(p) for p in x if isprime(int(p)))
            if l > 0:
                y = d
                for i in range(1, l + 1):
                    y = A343590_helper(y, (-1) ** (i + 1))
                yield from (int(p) for p in y if isprime(int(p)))


def A343997(n):
    fs = factorint(2 * n)
    plist = [p ** fs[p] for p in fs]
    x = min(
        k
        for k in (crt(plist, d)[0] for d in product([0, -1], repeat=len(plist)))
        if k > 0
    )
    return x + x % 2


def A345926(n):
    fs = dict((primepi(a), b) for (a, b) in factorint(n).items())
    return len(
        set(sum(d) for d in multiset_combinations(fs, (sum(fs.values()) + 1) // 2))
    )


def A346005(n):
    return n if n % 3 == 0 else ((n + 2) // 3) ** 3 if n % 3 == 1 else (n + 1) ** 2 // 3


def A346007(n):
    i = (5 - n) % 5
    return comb(5, i + 1) * ((n + i) // 5) ** (i + 1)


def A346892_gen():
    return (
        1000 * n + d
        for n in count(0)
        for d in [38, 462, 538, 962]
        if (lambda x: x[0] == x[1] == x[2] != x[3])(str((1000 * n + d) ** 2))
    )


def A347043(n):
    fs = factorint(n, multiple=True)
    l = len(fs)
    return prod(fs[: (l + 1) // 2])


def A347044(n):
    fs = factorint(n, multiple=True)
    l = len(fs)
    return prod(fs[l // 2 :])


def A347594_gen():  # generator of terms
    b = 1
    for n in count(1):
        yield b
        m = b**2 + n**2
        b = (isqrt(m) + 1) ** 2 - m


def A347754_gen():  # generator of terms
    a = 1
    for n in count(1):
        m = a**2 + n**2
        k = isqrt(m) + 1
        a = k**2 - m
        yield k


def A347756_gen():  # generator of terms
    yield 1
    nset, m, j = {1}, 2, 2
    while True:
        k = m
        while k == j or gcd(k, j) == 1 or k in nset:
            k += 1
        j = k + 1
        nset.add(k)
        if k == m:
            yield k
        while m in nset:
            m += 1


def A348063(n):
    return sum(
        ff(n, n - k) * expand(ff(symbolx, k)).coeff(symbolx**2)
        for k in range(2, n + 1)
    )


def A348064(n):
    return sum(
        ff(n, n - k) * expand(ff(symbolx, k)).coeff(symbolx**3)
        for k in range(3, n + 1)
    )


def A348065(n):
    return sum(
        ff(n, n - k) * expand(ff(symbolx, k)).coeff(symbolx**4)
        for k in range(4, n + 1)
    )


def A348068(n):
    return sum(
        ff(n, n - k) * expand(ff(symbolx, k)).coeff(symbolx**5)
        for k in range(5, n + 1)
    )


@lru_cache(maxsize=None)
def A003318(n):
    if n == 0:
        return 1
    c, j = n + 1, 1
    k1 = (n - 1) // j
    while k1 > 1:
        j2 = (n - 1) // k1 + 1
        c += (j2 - j) * A003318(k1)
        j, k1 = j2, (n - 1) // j2
    return c - j


def A011970_gen():  # generator of terms
    yield from [1, 4, 8]
    blist, b, b2, b3 = [1, 2], 2, 1, 1
    while True:
        blist = list(accumulate([b] + blist))
        yield 3 * (b + b2) + b3 + blist[-1]
        b3, b2, b = b2, b, blist[-1]


def A011972_gen():  # generator of terms
    yield 1
    blist = [1]
    while True:
        b = blist[-1]
        blist = list(accumulate([b] + blist))
        yield from blist[1:]


def A014237(n):
    return 1 if n == 1 else prime(n) - composite(n - 1)


def A017764(n):
    return comb(n, 100)


def A017764_gen():  # generator of terms
    m = [1] * 101
    while True:
        yield m[-1]
        for i in range(100):
            m[i + 1] += m[i]


def A022797(n):
    return 3 if n == 1 else prime(n) + composite(n - 1)


def A028819_gen():
    return chain(
        (0,),
        (
            int(isqrt(n))
            for n in (
                int("".join(i))
                for l in count(1)
                for i in combinations_with_replacement("123456789", l)
            )
            if is_square(n)
        ),
    )


def A030056_gen():  # generator of terms
    b = 1
    for n in count(6):
        yield b
        b = b * (2 * n + 2) * (2 * n + 3) // ((n - 5) * (n + 8))


def A030056(n):
    return comb(2 * n + 1, n - 6)


def A030690(n):
    d, nd = 10, 10 * n**2
    while True:
        x = (integer_nthroot(nd - 1, 3)[0] + 1) ** 3
        if x < nd + d:
            return x
        d *= 10
        nd *= 10


def A046332_gen():
    return (x for x in pal10_gen() if sum(list(factorint(x).values())) == 6)


def A048332_gen():
    return chain((0,), (int(d * l, 7) for l in count(1) for d in "123456"))


def A048612(n):
    d = divisors((10**n - 1) // 9)
    l = len(d)
    return (d[l // 2] - d[(l - 1) // 2]) // 2


def A048703(n):
    s = bin(n - 1)[2:]
    if len(s) % 2:
        s = "0" + s
    t = [s[i : i + 2] for i in range(0, len(s), 2)]
    return int("".join(t + t[::-1]), 2)


def A050804_gen():
    return (
        2 * i
        for i in count(1)
        if not any(p % 4 == 1 or factorint(i)[p] % 2 for p in factorint(i))
    )


def A055268(n):
    return (11 * n + 4) * comb(n + 3, 3) // 4


def A055268_gen():  # generator of terms
    m = [11, 1, 1, 1, 1]
    while True:
        yield m[-1]
        for i in range(4):
            m[i + 1] += m[i]


def A057045(n):
    i, j = isqrt_rem(2 * lucas(n - 1))
    return int(i + int(4 * (j - i) >= 1))


def A057332_helper(w, dir):
    if dir == 1:
        for s in w:
            for t in range(int(s[-1]) + 1, 10):
                yield s + str(t)
    else:
        for s in w:
            for t in range(0, int(s[-1])):
                yield s + str(t)


def A057332(n):
    c = 0
    for d in "123456789":
        x = d
        for i in range(1, n + 1):
            x = A057332_helper(x, (-1) ** i)
        c += sum(1 for p in x if isprime(int(p + p[-2::-1])))
        if n > 0:
            y = d
            for i in range(1, n + 1):
                y = A057332_helper(y, (-1) ** (i + 1))
            c += sum(1 for p in y if isprime(int(p + p[-2::-1])))
    return c


def A057699_gen():  # generator of terms
    for l in count(1):
        blist = []
        for i in range(10 ** (l - 1), 10**l):
            if i % 10:
                p = int(str(i**3)[::-1])
                if isprime(p):
                    blist.append(p)
        yield from sorted(blist)


def A058009(n):
    k = n
    for _ in range(n):
        k = prime(k)
    return k


def A060358(n):
    return prevprime(lcm(range(1, n + 1)))


def A061906(n):
    return A050782(int(str(n).rstrip("0"))) if n > 0 else 1


def A069648(n):
    if n == 1:
        return 1
    else:
        m = 2
        while True:
            x = sum(int(d) for d in str(m**n))
            if x > 1 and not any(map(lambda x: x % n, factorint(x).values())):
                return m
            m += 1


def A071268(n):
    s = "".join(str(i) for i in range(1, n + 1))
    return (
        sum(int(d) for d in s)
        * factorial(len(s) - 1)
        * (10 ** len(s) - 1)
        // (9 * prod(factorial(d) for d in (s.count(w) for w in set(s))))
    )


def A070306_gen(startvalue=3):  # generator of terms
    for i in count(max(startvalue, 3)):
        n = i**3
        m = n // 3
        pm, nm = prevprime(m), nextprime(m)
        k = n - pm - nm
        if isprime(m):
            if m == k:
                yield i
        else:
            if nextprime(nm) == k or prevprime(pm) == k:
                yield i


def A076620(n):
    return (
        y := Poly(prod(symbolx + i for i in range(1, n + 1))).all_coeffs()[::-1]
    ).index(max(y))


def A078226_gen():  # generator of terms
    x = 1
    yield 1
    while True:
        y, x2 = x, 2 * x
        while True:
            y += x2
            s = str(y)
            for j in range(len(s) - 1, -1, -2):
                if not s[j] in ("1", "3", "5", "7", "9"):
                    break
            else:
                for k in range(len(s) - 2, -1, -2):
                    if not s[k] in ("0", "2", "4", "6", "8"):
                        break
                else:
                    yield y
                    x = y
                    break


def A078227_gen():  # generator of terms
    x = 2
    yield 2
    while True:
        y = x
        while True:
            y += x
            s = str(y)
            for j in range(len(s) - 1, -1, -2):
                if not s[j] in ("0", "2", "4", "6", "8"):
                    break
            else:
                for k in range(len(s) - 2, -1, -2):
                    if not s[k] in ("1", "3", "5", "7", "9"):
                        break
                else:
                    yield y
                    x = y
                    break


def A078242(n):
    if n > 0:
        for i in range(1, 2**n):
            x = 3 * int(bin(i)[2:])
            if not x % n:
                return x
    return 0


def A080719(n):
    return int("".join((format(int(d), "b") for d in str(n))), 2)


def A082232_gen():
    return filter(
        lambda n: not n % sum(int(d) for d in str(n)), islice(pal10_gen(), 1, None)
    )


def A087669(n):
    c, x = 0, 2 * n + 1
    a, b = divmod(x, n)
    while b != 0:
        x *= a
        c += 1
        a, b = divmod(x, n)
    return c


def A091626(n):
    m = isqrt(n)
    return 1 if n == 0 else n + sum(n // k for k in range(1, m + 1)) - m * (m - 1) // 2


def A097344_gen():  # generator of terms
    yield 1
    tlist = [Fraction(1, 1)]
    for i in count(1):
        for j in range(len(tlist)):
            tlist[j] *= Fraction(i, i - j)
        tlist += [Fraction(1, (i + 1) ** 2)]
        yield sum(tlist).numerator


def A350346_gen():  # generator of terms
    yield 0
    for n in count(1):
        s = bin(n)[2:]
        c, l = 0, len(s)
        for i in range(l):
            c += int(s[l - i - 1])
            if 2 * c <= i:
                break
        else:
            yield int(s)


def A036991_gen(startvalue=0):  # generator of terms
    if startvalue <= 0:
        yield 0
    for n in count(max(startvalue, 1)):
        s = bin(n)[2:]
        c, l = 0, len(s)
        for i in range(l):
            c += int(s[l - i - 1])
            if 2 * c <= i:
                break
        else:
            yield n


def A100580_gen():
    return filter(isprime, (int(bin(n)[2:]) for n in pal_gen(b=2)))


def A104242_gen():
    return filter(isprime, (int(str(n**2) + str((n + 1) ** 2)) for n in count(1)))


def A104265(n):
    m, a = integer_nthroot((10**n - 1) // 9, 2)
    if not a:
        m += 1
    k = m**2
    while "0" in str(k):
        m += 1
        k += 2 * m - 1
    return k


def A110765(n):
    return prod(prime(i) for i, d in enumerate(bin(n)[2:], start=1) if int(d))


def A119861_gen():  # generator of terms
    yield 0
    c, s = {}, 3
    for n in count(2):
        for p, e in factorint(4 * n - 2).items():
            if p in c:
                c[p] += e
            else:
                c[p] = e
        for p, e in factorint(n + 1).items():
            if c[p] == e:
                del c[p]
            else:
                c[p] -= e
        if n == s:
            yield len(c)
            s = 2 * s + 1


def A120623_gen():  # generator of terms
    b = 1
    for n in count(1):
        if b % n and not (3 * b) % n:
            yield n
        b = b * (4 * n + 2) // (n + 2)


def A125094(n):
    return (
        n
        * (
            n**2
            * (
                n**2
                * (
                    n**2
                    * (n**2 * (n**2 * (n * (210 * n + 1365) + 2730) - 5005) + 8580)
                    - 9009
                )
                + 4550
            )
            - 691
        )
        // 2730
    )


def A125095(n):
    return (
        n**2
        * (
            n**2
            * (n**2 * (n**2 * (n**2 * (n * (2 * n + 12) + 22) - 33) + 44) - 33)
            + 10
        )
        // 24
    )


def A123346_gen():  # generator of terms
    yield 1
    blist = [1]
    while True:
        b = blist[-1]
        blist = list(accumulate([b] + blist))
        yield from reversed(blist)


def A130335(n):
    k, Tn, Tm = 1, n * (n + 1) // 2, (n + 1) * (n + 2) // 2
    while gcd(Tn, Tm) != 1:
        k += 1
        Tm += k + n
    return k


def A133421(n):
    return (
        n // 2
        if not n % 2
        else (n // 3 if not n % 3 else (n // 5 if not n % 5 else 7 * n + 1))
    )


def A138182(n):
    m, tlist = prime(n), [1, 2]
    while tlist[-1] + tlist[-2] <= m:
        tlist.append(tlist[-1] + tlist[-2])
    for d in tlist[::-1]:
        if d == m:
            return d
        elif d < m:
            m -= d


def A138290_gen(startvalue=1):  # generator of terms
    for n in count(max(startvalue, 1)):
        k2, n2 = 1, 2 ** (n + 1)
        for k in range(n):
            if isprime(n2 - k2 - 1):
                break
            k2 *= 2
        else:
            yield n


def A142994(n):
    return n * (n * (n * (n * (64 * n + 160) + 240) + 200) + 86) // 15 + 1


def A143010(n):
    return (
        n
        * (
            n
            * (
                n * (n * (n * (n * (n * (35 * n + 140) + 630) + 1400) + 2595) + 3020)
                + 2500
            )
            + 1200
        )
        // 288
        + 1
    )


@lru_cache(maxsize=None)
def A143270(n):  # based on second formula in A018805
    if n == 0:
        return 0
    c, j = 0, 2
    k1 = n // j
    while k1 > 1:
        j2 = n // k1 + 1
        c += (j2 - j) * (2 * A143270(k1) // k1 - 1)
        j, k1 = j2, n // j2
    return n * (n * (n - 1) - c + j) // 2


def A160827(n):
    return n * (n * (n * (3 * n + 12) + 30) + 36) + 17


def A169824_gen(startvalue=1):
    return (n for n in count(max(startvalue, 1)) if not n % int(str(n)[::-1]))


def A171865_gen():  # generator of terms
    n = 1
    for m in A181391_gen():
        if m == 0:
            yield n
        n += 1


def A171868_gen():  # generator of terms
    g = A171865_gen()
    m = next(g)
    for k in g:
        yield k - m
        m = k


def A171887_gen():  # generator of terms
    g = A171868_gen()
    n, c = 1, 0
    for k in g:
        if k > c:
            yield n
            c = k
        n += 1


def A171888_gen():  # generator of terms
    g, c = A171868_gen(), 0
    for k in g:
        if k > c:
            yield k
            c = k


def A176371_gen():
    return filter(
        lambda p: is_square(int(str(p)[::-1]) - 13), (prime(n) for n in count(1))
    )


def A177719(n):
    return 4 * (
        (n - 1) * (n - 2)
        + sum(totient(i) * (n - 2 * i) * (n - i) for i in range(2, n // 2 + 1))
    )


def A181134(n):
    return (
        n**2
        * (
            n**2
            * (
                n**2
                * (
                    n**2
                    * (n**2 * (n**2 * (n * (30 * n + 210) + 455) - 1001) + 2145)
                    - 3003
                )
                + 2275
            )
            - 691
        )
        // 420
    )


def A187338(n):
    return 3 * n + isqrt(2 * n**2)


def A187393(n):
    return 4 * n + isqrt(8 * n**2)


def A187946(n):
    return int(
        (isqrt(5 * (n + 5) ** 2) + n + 1) // 2 - (isqrt(5 * n**2) + n) // 2 - 6
    )


def A188374(n):
    return int(isqrt((n + 2) ** 2 // 2) - isqrt(n**2 // 2)) - 1


def A190402_gen(startvalue=2):
    return (
        n
        for n in count(max(startvalue, 2))
        if totient(int(sum([n * e / p for p, e in factorint(n).items()]))) == totient(n)
    )


def A192290_gen(startvalue=1):
    return (
        n
        for n in count(max(startvalue, 1))
        if antidivisor_sigma(n) != n and antidivisor_sigma(antidivisor_sigma(n)) == n
    )


def A211033(n):
    x, y, z = n // 3 + 1, (n - 1) // 3 + 1, (n - 2) // 3 + 1
    return (
        x**4
        + 4 * x**3 * y
        + 4 * x**3 * z
        + 4 * x**2 * y**2
        + 8 * x**2 * y * z
        + 4 * x**2 * z**2
        + y**4
        + 6 * y**2 * z**2
        + z**4
    )


def A211034(n):
    x, y, z = n // 3 + 1, (n - 1) // 3 + 1, (n - 2) // 3 + 1
    return (
        x**2 * y**2
        + 2 * x**2 * y * z
        + x**2 * z**2
        + 2 * x * y**3
        + 6 * x * y**2 * z
        + 6 * x * y * z**2
        + 2 * x * z**3
        + 2 * y**3 * z
        + 2 * y * z**3
    )


def A211158(n):
    return n * (n + 1) * (3 * n + 1 + 3 * n**2 - (-1) ** n * (2 * n + 1))


def A211349_gen():
    return (
        p for p in (prime(n) for n in count(1)) if p == 2 or pow(2, p, p - 1) == p - 3
    )


def A225671(n):
    xn, xd, k, p = 1, prime(n), n, prime(n)
    while xn < xd:
        k += 1
        po, p = p, prime(k)
        xn = xn * p + xd
        xd *= p
    return po


def A228122(n):
    k = 0
    while sum(factorint(k * (k + 1) + 41).values()) != n:
        k += 1
    return k


def A229269_gen(startvalue=1):
    return (
        n
        for n in count(max(startvalue, 1))
        if isprime(n - sum(int(n * e / p) for p, e in factorint(n).items()))
    )


def A229270_gen(startvalue=1):
    return (
        n
        for n in count(max(startvalue, 1))
        if isprime(sum(int(n * e / p) for p, e in factorint(n).items()) - n)
    )


def A229272_gen(startvalue=1):  # generator of terms
    for n in count(max(startvalue, 1)):
        np = sum(int(n * e / p) for p, e in factorint(n).items())
        if isprime(np + n) and isprime(np - n):
            yield n


def A229294(n):
    ndict = {}
    n2 = 2 * n
    for i in range(n2):
        i3 = pow(i, 2, n2)
        for j in range(i + 1):
            j3 = pow(j, 2, n2)
            m = (i3 + j3) % n2
            if m in ndict:
                if i == j:
                    ndict[m] += 1
                else:
                    ndict[m] += 2
            else:
                if i == j:
                    ndict[m] = 1
                else:
                    ndict[m] = 2
    count = 0
    for i in ndict:
        j = (n - i) % n2
        if j in ndict:
            count += ndict[i] * ndict[j]
    return count


def A232178(n):
    if n == 0:
        return 0
    t = n * (n + 1) // 2
    ds = divisors(t)
    l, m = divmod(len(ds), 2)
    if m:
        return 0
    for i in range(l - 1, -1, -1):
        x = ds[i]
        y = t // x
        a, b = divmod(y - x, 2)
        if not b:
            return a
    return -1


def A232179(n):
    if n == 0:
        return 0
    t = 2 * n**2
    ds = divisors(t)
    for i in range(len(ds) // 2 - 1, -1, -1):
        x = ds[i]
        y = t // x
        a, b = divmod(y - x, 2)
        if b:
            return a
    return -1


def A232444_gen():
    return chain(
        (2,),
        (
            n
            for n in (d**2 for d in count(1))
            if isprime(divisor_sigma(n)) and isprime(divisor_sigma(n**2))
        ),
    )


def A235801_gen(startvalue=0):
    return (n if n % 6 != 4 else 10 * (n // 6) + 7 for n in count(max(startvalue, 0)))


def A240923(n):
    return (m := Fraction(int(divisor_sigma(n)), n)).numerator - divisor_sigma(
        m.denominator
    )


def A241557_gen(startvalue=1):
    return filter(
        lambda n: not any(isprime(d) for d in antidivisors(n, generator=True)),
        count(max(startvalue, 1)),
    )


def A241107_gen():  # generator of terms
    blist = [0, 1, 1, 1, 1, -1]
    yield from blist
    while True:
        blist = blist[1:] + [
            (-blist[-1] * blist[-4] + blist[-2] * blist[-3]) // blist[-5]
        ]
        yield blist[-1]


def A242800_gen(startvalue=0):
    return (n for n in count(max(startvalue, 0)) if pow(n, n, n + 3) == n)


def A244411_gen(startvalue=1):  # generator of terms
    if startvalue <= 1:
        yield 1
    for n in count(max(startvalue, 2)):
        d = divisor_count(n)
        if d > 2:
            q, r = divmod(d, 2)
            s = str(n**q * (isqrt(n) if r else 1))
            if s == s[::-1]:
                yield n


def A246044_gen():  # generator of terms
    for n in count(1):
        p = prime(n)
        for x in permutations(str(p)):
            if x[0] != "0":
                p2 = int("".join(x))
                if p2 != p and isprime(p2):
                    break
        else:
            yield p


def A246519_gen():
    return (
        p
        for p in (prime(n) for n in count(1))
        if all(isprime(4 + p**z) for z in (1, 2, 3, 5))
    )


def A247165_gen(startvalue=0):
    return (n for n in count(max(startvalue, 0)) if n == 0 or pow(2, n, n * n + 1) == 1)


def A247452_gen():  # generator of terms
    yield from [1, 3]
    blist, b, n3 = [1], 1, 9
    while True:
        blist = list(accumulate([b] + blist))
        b = blist[-1]
        yield b * n3
        n3 *= 3


def A249153_gen():  # generator of terms
    yield 0
    n = 0
    for i in count(2, 2):
        n += multiplicity(2, i) * i
        yield n


def A249157_gen():
    return filter(lambda n: is_pal(n, 13), pal_gen(11))


def A249158_gen():
    return filter(lambda n: is_pal(n, 29), pal_gen(7))


def A249667_gen():  # generator of terms
    p = 2
    while True:
        q = next_prime(p)
        n1 = 2 * p + 1
        n2 = p + q + 1
        while n1 < p + q:
            if isprime(n1) and isprime(n2):
                yield n1 - p
            n1 += 2
            n2 += 2
        p = q


def A251393_gen():  # generator of terms
    yield from [1, 2]
    l1, l2, s, p2, b = 3, 2, 4, 4, {}
    for n in count(4):
        i = s
        while True:
            if not i in b and gcd(i, l1) == 1 and gcd(i, l2) > 1:
                l2, l1, b[i] = l1, i, 1
                while s in b:
                    b.pop(s)
                    s += 1
                if i == p2:
                    yield n
                    p2 *= 2
                break
            i += 1


def A251603_gen(startvalue=1):
    return (n for n in count(max(startvalue, 1)) if pow(n, n, n + 2) == 2)


def A252079_gen():  # generator of terms
    yield 1
    l, s, b = [1], 2, set()
    for n in count(2):
        i = s
        while True:
            if i not in b:
                li = [int(d) for d in str(i)[::-1]]
                for x, y in zip(li, l):
                    if x + y > 9:
                        break
                else:
                    l = li
                    b.add(i)
                    if i == n:
                        yield i
                    while s in b:
                        b.remove(s)
                        s += 1
                    break
            i += 1


def A252652(n):
    if n == 0:
        return 0
    f, i, s = 1, 0, re.compile("[0-9]*[1-9]0{" + str(n) + "}[1-9][0-9]*")
    while s.match(str(f)) == None:
        i += 1
        f *= i
    return i


def A252865_gen():  # generator of terms
    yield from [1, 2, 3]
    l1, l2, s, b = 3, 2, 4, set()
    while True:
        i = s
        while True:
            if max(factorint(i).values()) == 1:
                if not i in b and gcd(i, l1) == 1 and gcd(i, l2) > 1:
                    yield i
                    l2, l1 = l1, i
                    b.add(i)
                    while s in b:
                        b.remove(s)
                        s += 1
                    break
            else:
                b.add(i)
            i += 1


def A252868_gen():  # generator of terms
    yield from [1, 2, 3]
    l1, l2, s, b = 2, 1, 3, set()
    while True:
        i = s
        while True:
            if not (i in b or i & l1) and i & l2:
                yield A019565(i)
                l2, l1 = l1, i
                b.add(i)
                while s in b:
                    b.remove(s)
                    s += 1
                break
            i += 1


def A253941_gen():  # generator of terms
    for p in (prime(n) for n in count(1)):
        p2, x = p**2, 1
        for i in range(5):
            x *= p2
            q, r = divmod(x + 5, 6)
            if r or not isprime(q):
                break
        else:
            yield p


def A254732(n):
    k = n + 1
    while pow(k, 2, n):
        k += 1
    return k


def A254734(n):
    k = n + 1
    while pow(k, 4, n):
        k += 1
    return k


def A257345(n):
    if n > 0:
        for i in range(1, 2**n):
            x = int(format(i, "b"))
            if not x % n:
                return int(str(x), 2)
    return 0


def A257349_gen():
    return accumulate(repeat(16), lambda x, _: divisor_sigma(x))


def A257899_gen():  # generator of terms
    l = []
    for d in permutations("0123456789", 10):
        if d[0] != "0":
            d2 = int("".join(d))
            d = d2
            r = d2 % 3
            while not r:
                d2, r = divmod(d2, 3)
            l.append((d2, d))
    l.sort()
    yield from (b for a, b in l)


def A259831_gen(startvalue=2):  # generator of terms
    for n in count(max(startvalue, 2)):
        s = format(n, "0b")
        for l in range(1, len(s)):
            n1, n2 = int(s[:l], 2), int(s[l:], 2)
            if n2 > 0 and n == (divisor_sigma(n1) - n1) * (divisor_sigma(n2) - n2):
                yield n
                break


def A259832_gen(startvalue=2):  # generator of terms
    for n in count(max(startvalue, 2)):
        s, k = format(n, "0b"), divisor_sigma(n)
        for l in range(1, len(s)):
            n1, n2 = int(s[:l], 2), int(s[l:], 2)
            if n2 > 0 and k == (divisor_sigma(n1) - n1) * (divisor_sigma(n2) - n2):
                yield n
                break


def A262091_gen():  # generator of terms
    for m in count(2):
        for c in combinations_with_replacement(range(10), m + 1):
            n = sum(d**m for d in c)
            r = sum(int(q) ** m for q in str(n))
            rlist = sorted(int(d) for d in str(r))
            rlist = [0] * (m + 1 - len(rlist)) + rlist
            if n < r and rlist == list(c):
                yield n


def A262092_gen():  # generator of terms
    for m in count(2):
        for c in combinations_with_replacement(range(10), m + 1):
            n = sum(d**m for d in c)
            r = sum(int(q) ** m for q in str(n))
            rlist = sorted(int(d) for d in str(r))
            rlist = [0] * (m + 1 - len(rlist)) + rlist
            if n < r and rlist == list(c):
                yield r


def A262958_helper1(n):
    s = gmpy2digits(n, 3)
    m = len(s)
    for i in range(m):
        if s[i] == "0":
            return int(s[:i] + "1" * (m - i), 3)
    return n


def A262958_helper2(n):
    s = gmpy2digits(n, 4)
    m = len(s)
    for i in range(m):
        if s[i] == "0":
            return int(s[:i] + "1" * (m - i), 4)
        if s[i] == "2":
            return int(s[:i] + "3" + "1" * (m - i - 1), 4)
    return n


def A262958_gen():  # generator of terms
    n = 1
    while True:
        m = A262958_helper2(A262958_helper1(n))
        while m != n:
            n, m = m, A262958_helper2(A262958_helper1(m))
        yield m
        n += 1


def A263314_gen(startvalue=0):  # generator of terms
    for i in count(max(startvalue, 0)):
        s = str(i)
        for d in s:
            j = int(d)
            if j:
                for e in s:
                    if int(e) % j:
                        break
                else:
                    yield i
                    break


def A263856(n):
    return 1 + sorted(format(prime(i), "b")[::-1] for i in range(1, n + 1)).index(
        format(prime(n), "b")[::-1]
    )


def A267821_gen():
    return (
        int(d, 9)
        for d in (str(i**2) for i in count(1))
        if max(d) < "9" and isprime(int(d, 9))
    )


def A267875(n):
    return int((mpz(2) ** 74207281 - 1) // mpz(10) ** (44677235 - n) % 10)


def A268476_gen():
    return (
        p
        for p in (prime(i) for i in count(1))
        if not len(list(filter(bool, format(p, "b").split("0")))) % 2
    )


def A268477_gen():
    return (
        p
        for p in (prime(i) for i in count(1))
        if len(list(filter(bool, format(p, "b").split("0")))) % 2
    )


def A271497(n):
    return (
        int("".join(sorted(bin(n)[2:])), 2)
        + int("".join(sorted(bin(n)[2:], reverse=True)), 2)
        if n % 3
        else n // 3
    )


def A271591_gen():  # generator of terms
    a, b, c = 0, 1, 1
    while True:
        a, b, c = b, c, a + b + c
        yield int(bin(c)[3])


def A272363(n):
    return (
        1
        if n == 0
        else sum(
            1
            for p in multiset_partitions(list(range(1, 2 * n + 1)), n)
            if max(len(d) for d in p) == 2
            and len(set([sum(d) for d in p])) + len(set([abs(d[0] - d[1]) for d in p]))
            == 2 * n
        )
    )


def A272654_gen():
    return (
        int(b + "".join(s))
        for b in (bin(n)[2:] for n in count(1))
        for s in multiset_permutations(sorted(b))
    )


def A272655_gen():
    return (
        int(str(n) + "".join(s))
        for n in count(1)
        for s in multiset_permutations(sorted(str(n)))
    )


def A273245_gen():
    (
        int(m)
        for m in (bin(n)[2:] for n in count(1))
        if m != m[::-1] and m.rstrip("0") == m[::-1].lstrip("0")
    )


def A275111(n):
    p, q = prime(n), prime(n + 1)
    a = q - 1
    for i in range(p + 1, q):
        a = (a * igcdex(i, q)[0]) % q
    return a


def A276863(n):
    return 1 + isqrt(5 * n**2) - isqrt(5 * (n - 1) ** 2)


def A278585_gen():
    return (
        4 * q - 4
        for q in (prime(i) for i in count(1))
        if isprime(4 * q - 3)
        and isprime(2 * q - 1)
        and (not (4 * q - 1) % 3)
        and isprime((4 * q - 1) // 3)
    )


def A280934_gen():  # generator of terms
    yield from [1, 1, 4, 36]
    b = 36
    for i in count(4):
        b += 4 * divisor_count(i + 1) + 8
        yield b


@lru_cache(maxsize=None)
def A283207(n):
    return 2 if n <= 2 else A283207(n // A283207(n - 1)) + A283207(n // A283207(n - 2))


def A290323(n):
    f = factorint(n)
    m = f[2] if 2 in f else 0
    a, b = divmod(m, 3)
    c = 2 if m == 1 else 3 ** (b * (b + 1) % 5) * 5 ** (a - (b % 2))
    return c * prod(((d + 1) // 2) ** f[d] for d in f if d != 2)


def A290434_gen(startvalue=2):
    return (
        n
        for n in count(max(startvalue, 2))
        if sum(factorint(n).values()) == 2
        and isprime(1 + sum(factorint(n).keys()) * (3 - len(factorint(n))))
    )


def A298946(n):
    c = composite(n)
    return comb(2 * c - 1, c - 1) % c**4


def A301278(n):
    return (
        (Fraction(int(comb(2 * n, n))) / n - Fraction(4**n) / (n * (n + 1))).numerator
        if n > 0
        else 0
    )


def A301279(n):
    return (
        (
            Fraction(int(comb(2 * n, n))) / n - Fraction(4**n) / (n * (n + 1))
        ).denominator
        if n > 0
        else 1
    )


def A301336(n):
    return sum(2 * bin(i).count("1") - len(bin(i)) + 2 for i in range(n + 1))


def A306305(n):
    m, k = 0, n
    while True:
        s = str(k)
        for i in range(1, len(s)):
            if s[i] == s[i - 1]:
                return m
        m += 1
        k *= 2


@lru_cache(maxsize=None)
def A309288(n):
    if n <= 1:
        return n
    c, j = 0, 2
    k1 = n // j
    while k1 > 1:
        j2 = n // k1 + 1
        c += ((j2 - j) % 2) * (1 - 2 * (j % 2)) * A309288(k1)
        j, k1 = j2, n // j2
    return c + ((n + 1 - j) % 2) * (1 - 2 * (j % 2))


def A318935(n):
    s = bin(n)
    return (8 ** (len(s) - len(s.rstrip("0")) + 1) - 1) // 7


def A320039(n):
    return int(
        "".join(
            d + "1" for d in split("(0+)|(1+)", bin(n)[2:]) if d != "" and d != None
        ),
        2,
    )


def A320940(n):
    return sum(
        divisor_sigma(d) * (n // d) ** (n + 1) for d in divisors(n, generator=True)
    )


def A321440(n):
    if n == 0:
        return 1
    c = 0
    for i in range(n):
        mi = i * (i + 1) // 2 + n
        for j in range(i + 1, n + 1):
            k = mi - j * (j + 1) // 2
            if k < 0:
                break
            if not k % j:
                c += 1
    return c


def A321797(n):
    return int("0" + "".join(d if str(n).count(d) != 1 else "" for d in str(n)))


def A321800(n):
    return (lambda x: int(x) if x != "" else -1)(
        "".join(d if str(n).count(d) != 1 else "" for d in str(n))
    )


def A322781_gen():  # generator of terms
    for k in count(1):
        fk, fv = zip(*list(factorint(4 * k + 1).items()))
        if (
            sum(fv) == len(fk) == 2
            and fk[0] % 4 == fk[1] % 4 == 1
            and legendre_symbol(fk[0], fk[1]) == -1
        ):
            yield 4 * k + 1


def A323271_gen():  # generator of terms
    for k in count(1):
        fk, fv = zip(*list(factorint(4 * k + 1).items()))
        if (
            sum(fv) == len(fk) == 3
            and fk[0] % 4 == fk[1] % 4 == fk[2] % 4 == 1
            and legendre_symbol(fk[0], fk[1])
            == legendre_symbol(fk[0], fk[2])
            == legendre_symbol(fk[1], fk[2])
            == -1
        ):
            yield 4 * k + 1


def A325231_gen(startvalue=6):
    return (
        n
        for n in count(max(startvalue, 6))
        if ((not n % 2) and isprime(n // 2))
        or (bin(n)[2:4] == "11" and bin(n).count("1") == 2)
    )


def A325459(n):
    return (
        0
        if n == 0
        else (
            lambda m: 2 * (sum(n // k for k in range(1, m + 1)) - n) + (1 - m) * (1 + m)
        )(isqrt(n))
    )


def A331771(n):
    return 4 * (
        (n - 1) * (2 * n - 1)
        + sum(totient(i) * (n - i) * (2 * n - i) for i in range(2, n))
    )


def A332596(n):
    return (
        0
        if n == 1
        else (
            (n - 1) * (n - 4)
            - sum(
                totient(i) * (n + 1 - i) * (2 * n + 2 - 7 * i)
                for i in range(2, n // 2 + 1)
            )
            + sum(
                totient(i) * (n + 1 - i) * (2 * n + 2 - i)
                for i in range(n // 2 + 1, n + 1)
            )
        )
        // 2
    )


def A332867(n):
    m, k = int("".join(str(d) for d in range(1, n + 1))), 1
    i = n + k
    i2, l = i % m, len(str(i))
    t = 10**l
    t2, r = t % m, i % m
    while r != 0:
        k += 1
        i += 1
        i2 = (i2 + 1) % m
        if i >= t:
            l += 1
            t *= 10
            t2 = (10 * t2) % m
        r = (r * t2 + i2) % m
    return k


def A341701(n):
    k, m = n, n - 1
    while not isprime(k) and m > 0:
        k = int(str(k) + str(m))
        m -= 1
    return m + 1 if isprime(k) else -1


def A341702(n):
    k, m = n, n - 1
    while not isprime(k) and m > 0:
        k = int(str(k) + str(m))
        m -= 1
    return n - m - 1 if isprime(k) else -1


def A342410(n):
    if n == 0:
        return 0
    for i, d in enumerate(bin(n)[2:].split("0")[::-1]):
        if d != "":
            return int(d + "0" * i, 2)


def A343996(n):
    fs = factorint(2 * n)
    plist = [p ** fs[p] for p in fs]
    x = min(
        k
        for k in (crt(plist, d)[0] for d in product([0, -1], repeat=len(plist)))
        if k > 0
    )
    return x + 1 - x % 2


def A345427(n):
    return sum(
        v
        for u, v, w in (igcdex(x, y) for x in range(1, n + 1) for y in range(1, n + 1))
    )


def A345433(n):
    return sum(
        abs(v)
        for u, v, w in (igcdex(x, y) for x in range(1, n + 1) for y in range(1, n + 1))
    )


def A345694(n):
    zlist = [
        z
        for z in (igcdex(x, y) for x in range(1, n + 1) for y in range(1, n + 1))
        if z[2] == 1
    ]
    return pvariance(len(zlist) * abs(u) for u, v, w in zlist)


def A345882_helper(n):
    if n == 1:
        return {1}
    else:
        s = A345882_helper(n - 1)
        c = set(s)
        for x in s:
            for i in range(2, n + 1):
                c.add(i * x)
        return c


def A345882(n):
    return len(A345882_helper(n))


def A346006(n):
    i = (4 - n) % 4
    return comb(4, i + 1) * ((n + i) // 4) ** (i + 1)


def A347323(n):
    return int("".join("0" if d == "0" else str(n % int(d)) for d in str(n)))


def A347409(n):
    m, r = n, 0
    while m > 1:
        if m % 2:
            m = 3 * m + 1
        else:
            s = bin(m)[2:]
            c = len(s) - len(s.rstrip("0"))
            m //= 2**c
            r = max(r, c)
    return r


def A347607(n):
    return partition(n**n)


def A007356_gen(startvalue=0):
    return (k for k in count(max(startvalue, 0)) if "666" in str(2**k))


def A008349(n):
    return (
        n
        * (
            n
            * (n * (n * (n * (n * (n * (57 * n + 108) + 210) + 504) + 273) + 252) + 300)
            - 24
        )
        // 7
        + 1
    )


def A011967_gen():
    yield 4
    blist, b = [5, 7, 10, 15], 15
    while True:
        blist = list(accumulate([b] + blist))
        b = blist[-1]
        yield blist[-5]


def A018142(n):
    i, j = iroot_rem(10**n, 5)
    return int(i) + int(32 * j >= 10 * i * (4 * i * (2 * i * (i + 1) + 1) + 1) + 1)


def A023969(n):
    i, j = isqrt_rem(n)
    return int(4 * (j - i) >= 1)


def A027603(n):
    return n * (n * (4 * n + 18) + 42) + 36


def A036994_gen(startvalue=0):  # generator of terms
    for n in count(max(startvalue, 0)):
        s = bin(n)[2:]
        c, l = 0, len(s)
        for i in range(l):
            c += int(s[l - i - 1])
            if 2 * c <= i + 1:
                break
        else:
            yield n


def A028337_gen():
    return filter(is_pal, (n * (n + 1) for n in count(1)))


def A028553_gen():
    return filter(lambda n: is_pal(n * (n + 3)), count(0))


def A028554_gen():
    return filter(is_pal, (n * (n + 3) for n in count(0)))


def A030668(n):
    d, nd = 10, 10 * n
    while True:
        x = (integer_nthroot(nd - 1, 3)[0] + 1) ** 3
        if x < nd + d:
            return x
        d *= 10
        nd *= 10


def A031688_gen():
    (
        n
        for n, s in ((i, continued_fraction_periodic(0, 1, i)[-1]) for i in count(1))
        if isinstance(s, list) and len(s) % 2 and s[(len(s) - 1) // 2] == 100
    )


def A038129(n):
    return integer_nthroot(2 * n**3, 3)[0]


def A038585(n):
    return int(bin(n)[2:].replace("0", ""))


def A048340_gen():
    return chain(
        (0,), (int(d * l, 16) for l in range(1, 10) for d in "123456789abcdef")
    )


def A048343(n):
    y, plist = 0, []
    for i in range(10 ** (n - 1), 10**n):
        s1 = str(i)
        s2 = s1[::-1]
        if s1 != s2:
            p = i * int(s2)
            if not p in plist:
                sp = str(p)
                if sp == sp[::-1]:
                    plist.append(p)
                    y += 1
    return y


def A048344_gen(startvalue=1):  # generator of terms
    for n in count(max(startvalue, 1)):
        s = str(n)
        s2 = str(n)[::-1]
        if s != s2:
            s3 = str(n * int(s2))
            if s3 == s3[::-1]:
                yield n


def A048611(n):
    d = divisors((10**n - 1) // 9)
    l = len(d)
    return (d[l // 2] + d[(l - 1) // 2]) // 2


def A051256(n):
    return sum(0 if ~n & k else factorial(k + 1) for k in range(n + 1))


def A053095(n):
    return sum(
        1
        for d in multiset_permutations("".join(str(prime(m + 1)) for m in range(n)))
        if isprime(int("".join(d)))
    )


def A053872_gen():  # generator of terms
    m, s = 4, 4
    for n in count(1):
        if isprime(s):
            yield s
        m += 1
        if isprime(m):
            m += 1
        s += m


def A056582_gen():  # generator of terms
    n = 1
    for i in range(2, 201):
        m = i**i
        yield gcd(n, m)
        n *= m


def A057333_helper(w, dir):
    if dir == 1:
        for s in w:
            for t in range(int(s[-1]) + 1, 10):
                yield s + str(t)
    else:
        for s in w:
            for t in range(0, int(s[-1])):
                yield s + str(t)


def A057333(n):
    c = 0
    for d in "123456789":
        x = d
        for i in range(1, n):
            x = A057333_helper(x, (-1) ** i)
        c += sum(1 for p in x if isprime(int(p)))
        if n > 1:
            y = d
            for i in range(1, n):
                y = A057333_helper(y, (-1) ** (i + 1))
            c += sum(1 for p in y if isprime(int(p)))
    return c


def A057630_gen(startvalue=2):  # generator of terms
    dlist, p = tuple(str(d) * d for d in range(10)), max(nextprime(startvalue - 1), 2)
    while True:
        if isprime(int("".join(dlist[int(d)] for d in str(p)))):
            yield p
        p = nextprime(p)


def A058993_gen():  # generator of terms
    m = 5
    for k in count(1):
        if isprime(int(str(m)[::-1])):
            yield k
        m *= 5


def A059247(n):
    return n // gcd(
        n, (lambda m: 2 * sum(n // k for k in range(1, m + 1)) - m * m)(isqrt(n))
    )


def A062067_gen():  # generator of terms
    yield 1
    a = 1
    while True:
        a += 1
        b = 2 * a * (a - 1) + 1
        while not isprime(b):
            b += 4 * (a + 1)
            a += 2
        yield a**2


def A062550(n):
    return (lambda m: 2 * sum(2 * n // k for k in range(1, m + 1)) - m * m)(
        isqrt(2 * n)
    )


def A064940_gen():  # generator of terms
    p, d, n, r = 2, -1, 0, False
    while True:
        pn, k = p - n, d if r else -d
        if 0 < k <= pn:
            yield n + k - 1
        d += -pn if r else pn
        r, n, p = not r, p, nextprime(p)


def A068186(n):
    if n == 1:
        return 1
    pf = factorint(n)
    ps = sorted(pf.keys(), reverse=True)
    if ps[0] > 7:
        return 0
    s = ""
    for p in ps:
        s += str(p) * (n * pf[p])
    return int(s)


@lru_cache(maxsize=None)
def A064960(n):
    return (
        1 if n == 1 else composite(A064960(n - 1)) if n % 2 else prime(A064960(n - 1))
    )


def A068831_gen():
    return (
        p
        for p in (
            int("".join(d)) for l in range(1, 9) for d in product("13579", repeat=l)
        )
        if isprime(p)
        and set(str(nextprime(p, 1))) <= {"1", "3", "5", "7", "9"}
        and set(str(nextprime(p, 2))) <= {"1", "3", "5", "7", "9"}
        and set(str(nextprime(p, 3))) <= {"1", "3", "5", "7", "9"}
    )


def A073633_gen():  # generator of terms
    m = 1
    for n in count(1):
        m *= 3
        if m // 2**n % n == 0:
            yield n


def A073799(n):
    return 2 if n == 1 else prime(2**n)


def A073956_gen():
    return filter(
        lambda n: is_pal(sum(antidivisors(n, generator=True))),
        islice(pal10_gen(), 1, None),
    )


def A074100_gen():
    return (n**3 for n in count(1) if set(str(n**3)) <= set("12357"))


def A075904_gen(startvalue=0):
    return filter(lambda k: str(k) in str(k**4), count(max(startvalue, 0)))


def A075905_gen(startvalue=0):
    return filter(lambda k: str(k) in str(k**5), count(max(startvalue, 0)))


def A078431(n):
    return sum(
        1
        for p in permutations(range(1, n + 1))
        if (lambda x: isprime(x.p) and isprime(x.q))(continued_fraction_reduce(p))
    )


def A078432(n):
    return sum(
        1
        for p in permutations(range(1, n + 1))
        if isprime(continued_fraction_reduce(p).q)
    )


def A078433(n):
    return sum(
        1
        for p in permutations(range(1, n + 1))
        if isprime(continued_fraction_reduce(p).p)
    )


def A079475(n):
    s = str(n)
    l = len(s)
    if l % 2:
        s = s[:-1] + "1" + s[-1]
    return int("".join(s[i + 1] * int(s[i]) for i in range(0, l, 2)))


def A080343(n):
    i, j = isqrt_rem(2 * n)
    return int(4 * (j - i) >= 1)


def A082060_gen(startvalue=1):
    return (n for n in count(max(startvalue, 1)) if set(str(totient(n))) == set(str(n)))


def A082916_gen():  # generator of terms
    b = 1
    for n in count(0):
        if gcd(n, b) == 1:
            yield n
        b = b * (4 * n + 2) // (n + 1)


def A085300(n):
    p = prime(n)
    q = p
    while True:
        m = int(str(q)[::-1])
        if isprime(m):
            return m
        q *= p


def A349823(n):
    return (lambda f: sum(f[p] for p in f) * sum(p * f[p] for p in f))(factorint(n))


@lru_cache(maxsize=None)
def A091369(n):
    if n == 0:
        return 0
    c, j = 0, 2
    k1 = n // j
    while k1 > 1:
        j2 = n // k1 + 1
        c += (j2 - j) * (2 * A091369(k1) - (k1 * (k1 - 1) + 1))
        j, k1 = j2, n // j2
    return n * (n - 1) - (c - j) // 2


@lru_cache(maxsize=None)
def A092149(n):
    if n == 1:
        return 1
    c, j = n + 1, 2
    k1 = n // j
    while k1 > 1:
        j2 = n // k1 + 1
        c += (j2 - j) * A092149(k1)
        j, k1 = j2, n // j2
    return j - c


def A096485(n):
    return len(continued_fraction(sqrt((10**n - 1) // 9))[-1])


def A096687(n):
    if n > 0:
        for i in range(1, 2**n):
            q, r = divmod(8 * int(bin(i)[2:]), n)
            if not r:
                return q
    return 1


def A105093_gen():
    plist = [2, 3, 5, 7]
    while True:
        m = plist[0] + plist[3]
        if m == plist[1] + plist[2]:
            yield m
        plist = plist[1:] + [nextprime(plist[-1])]


def A113496(n):
    m = composite(n)
    k = m + 1
    while gcd(k, m) != 1 or isprime(k):
        k += 1
    return k


def A120389(n):
    compositepi(prime(n) ** 2)


def A055874(n):
    for m in count(1):
        if n % m:
            return m - 1


def A120624_gen():
    b = 1
    for n in count(1):
        if not b % (2 * n):
            yield n
        b = b * (4 * n + 2) // (n + 2)


def A127118(n):
    return 2 if n == 1 else prime(n) * composite(n - 1)


def A128438(n):
    return harmonic(n).q // n


def A130232_gen():  # generator of terms
    b, c = 0, 1
    while True:
        yield b
        b += c
        c += str(b).count("0")


def A344104_gen():  # generator of terms
    b, c = 10, 1
    while True:
        yield b
        b *= c
        c += str(b).count("0")


def A138173(n):
    d, nd = 1, n**2
    while True:
        x = integer_nthroot(nd - 1, 3)[0] + 1
        if x**3 < nd + d:
            return x
        d *= 10
        nd *= 10


def A147771(n):
    i, j = isqrt_rem(n**n)
    return int(i + int(4 * (j - i) >= 1))


def A151413(n):
    if n <= 2:
        return n
    else:
        l1, m, b = 2, 1, {1, 2}
        for j in count(3):
            i = m
            while True:
                if not i in b:
                    if i == n:
                        return j
                    l1, m = i, l1 // gcd(l1, i)
                    b.add(i)
                    break
                i += m


def A153823(n):
    return divisor_count(factorial(n)) - 1


def A155011_gen():  # generator of terms
    a, b, a2, b2 = 0, 1, 1, 3
    while True:
        if isprime(b) and isprime(b2):
            yield b
        a, b, a2, b2 = b, a + b, b2, a2 + b2 - 1


def A158796_gen():  # generator of terms
    for i in count(3):
        n = i**3
        m = n // 3
        pm, nm = prevprime(m), nextprime(m)
        k = n - pm - nm
        if isprime(m):
            if m == k:
                yield primepi(pm)
        else:
            if nextprime(nm) == k:
                yield primepi(pm)
            elif prevprime(pm) == k:
                yield primepi(pm) - 1


def A161501(n):
    s = bin(n)[2:]
    if s == s[::-1]:
        return n
    for i in range(1, len(s)):
        if s[i:] == s[-1 : i - 1 : -1]:
            return int(s + s[i - 1 :: -1], 2)


def A166923(n):
    return 1 + (prime(n) ** 2 - 1) % 9


def A167508(n):
    return len(set(re.sub("[^a-z]", "", unidecode(num2words(n, lang="fr")))))


def A173071_gen():  # generator of terms
    for l in count(1):
        for i in combinations("23456789", l):
            s = "1" + "".join(i)
            p = int(s + s[l - 1 :: -1])
            if is_prime(p):
                yield p


def A182577(n):
    m, tlist, s = factorial(n), [1, 2], 0
    while tlist[-1] + tlist[-2] <= m:
        tlist.append(tlist[-1] + tlist[-2])
    for d in tlist[::-1]:
        if d <= m:
            s += 1
            m -= d
    return s


def A185635_gen():  # generator of terms
    yield from [1, 2]
    l1, m, b = 2, 2, {1, 2}
    for n in count(3):
        i = m
        while True:
            if not i in b:
                if n == i:
                    yield i
                l1, m = i, i // gcd(l1, i)
                b.add(i)
                break
            i += m


@lru_cache(maxsize=None)
def A185670(n):  # based on second formula in A018805
    if n == 0:
        return 0
    c, j = 2, 2
    k1 = n // j
    while k1 > 1:
        j2 = n // k1 + 1
        c += (j2 - j) * (k1 * (k1 - 1) + 1 - 2 * A185670(k1))
        j, k1 = j2, n // j2
    return (c - j) // 2


def A187395(n):
    return 4 * n + isqrt(10 * n**2)


def A187396(n):
    return isqrt(10 * n**2) - 2 * n


def A188090(n):
    return int(isqrt(3 * (n + 5) ** 2) - isqrt(3 * n**2)) - 8


def A188221(n):
    return isqrt(5 * (n + 1) ** 2) - isqrt(5 * n**2) - 2


def A188383_gen(startvalue=1):
    return (
        n
        for n in count(max(startvalue, 1))
        if isqrt((n + 3) ** 2 // 2) - isqrt(n**2 // 2) == 3
    )


def A191647_gen(startvalue=3):
    return (
        n
        for n in count(max(startvalue, 3))
        if isprime(
            int(
                "".join(
                    [
                        str(d)
                        for d in range(2, n)
                        if n % d and 2 * n % d in [d - 1, 0, 1]
                    ]
                )
            )
        )
    )


def A350457(n):
    return (
        1
        if n == 0
        else max(
            prod(1 + symbolx ** prime(i) for i in range(1, n + 1)).as_poly().coeffs()
        )
    )


def A193890_gen():  # generator of terms
    for l in count(1):
        for d in product("0123", repeat=l):
            p = int("".join(d))
            if d[0] != "0" and d[-1] in ("1", "3") and isprime(p):
                for i in range(len(d)):
                    d2 = list(d)
                    d2[i] = str(3 * int(d[i]))
                    if not is_prime(int("".join(d2))):
                        break
                else:
                    yield p


def A194145(n):
    return isqrt(6 * n**2) - n


def A210205_gen():  # generator of terms
    for i in count(3):
        n = i**3
        p2 = prevprime(n // 3)
        p1, p3 = prevprime(p2), nextprime(p2)
        q = p1 + p2 + p3
        while q <= n:
            if q == n:
                yield p1
            p1, p2, p3 = p2, p3, nextprime(p3)
            q = p1 + p2 + p3


def A210546_gen():  # generator of terms
    for l in count(1):
        q = (10**l - 1) // 9
        for i in range(l):
            for p in [2, 3, 5, 7]:
                r = q + (p - 1) * 10**i
                s, t = str(r), str(r)[::-1]
                if s != t and isprime(r) and isprime(int(t)):
                    yield r


def A211203_gen():
    return (
        p
        for p in (prime(n) for n in count(1))
        if p == 2 or p == 3 or pow(2, 2 * p - 1, p - 1) == 2
    )


def A211889(n):
    if n == 1:
        return 1
    delta = primorial(primepi(n))
    p, d = prime(n), delta
    while True:
        q = p
        for _ in range(n):
            q += d
            if not isprime(q):
                break
        else:
            return d
        d += delta


def A212875_gen(startvalue=2):  # generator of terms
    for n in count(max(startvalue, 2)):
        if not isprime(n):
            x = sorted(chain.from_iterable([p] * e for p, e in factorint(n).items()))
            y = sum(x)
            while y < n:
                x, y = x[1:] + [y], 2 * y - x[0]
            if y == n:
                yield n


def A216384_gen(startvalue=1):  # generator of terms
    for n in count(max(startvalue, 1)):
        ndsum = nd = sum(int(n * e / p) for p, e in factorint(n).items())
        while ndsum <= n and nd > 1:
            nd = sum(int(nd * e / p) for p, e in factorint(nd).items())
            ndsum += nd
            if ndsum == n:
                yield n


def A217165(n):
    if n == 1:
        return 0
    else:
        l, y, x = tuple(str(d) * n for d in range(10)), 0, 1
        for m in count(1):
            s = str(x)
            for k in l:
                if k in s:
                    return m
            y, x = x, y + x


def A217166(n):
    if n == 1:
        return 0
    else:
        l, y, x = tuple(str(d) * n for d in range(10)), 2, 1
        for m in count(1):
            s = str(x)
            for k in l:
                if k in s:
                    return m
            y, x = x, y + x


def A217466_gen():
    return (p for p in (prime(n) for n in count(1)) if pow(2, p, p * (p + 1)) == 2)


def A227510_gen():
    return (
        int(n)
        for n in (str(x) for x in count(1))
        if not n.count("0") and str(prod(int(d) for d in n)) in n
    )


def A232111(n):
    return min(
        x
        for x in (
            sum(d[i] * Fraction(1, i + 1) for i in range(n))
            for d in product((1, -1), repeat=n)
        )
        if x >= 0
    ).numerator


def A232112(n):
    if n <= 1:
        return 1
    m = lcm(*range(2, n + 1))
    mtuple = tuple(m // i for i in range(2, n + 1))
    return m // gcd(
        m,
        min(
            abs(m + sum(d[i] * mtuple[i] for i in range(n - 1)))
            for d in product((-1, 1), repeat=n - 1)
        ),
    )


def A232175(n):
    n3 = n**3
    ds = divisors(n3)
    for i in range(len(ds) // 2 - 1, -1, -1):
        x = ds[i]
        y = n3 // x
        a, b = divmod(y - x, 2)
        if not b:
            return a
    return 0


def A235540_gen(startvalue=1):  # generator of terms
    for i in count(max(startvalue, 1)):
        if not is_prime(i):
            d = 2 * i * (2 * i + 1)
            n = (pow(4, i, d) - pow(2, i, d) + 8 * i * i - 2) % d
            if not n:
                yield i


def A235808_gen(startvalue=0):
    return filter(lambda n: len(set(str(n**3))) == 6, count(max(startvalue, 0)))


def A235810_gen(startvalue=0):
    return filter(lambda n: len(set(str(n**3))) == 8, count(max(startvalue, 0)))


def A236246_gen():  # generator of terms
    n = 1
    for m in A229037_gen():
        if m == 1:
            yield n
        n += 1


def A239103_gen():  # generator of terms
    for n in count(0):
        for k in range(n, -1, -1):
            c, d0 = 0, ["0"] * (n + k)
            for x in combinations(range(n + k), n):
                d = list(d0)
                for i in x:
                    d[i] = "1"
                if not "1011101" in "".join(d):
                    c += 1
            yield c


def A242473(n):
    return comb(2 * (p := prime(n)) - 1, p - 1) % (p**4)


def A242966_gen():
    return filter(
        lambda n: all(isprime(d) for d in antidivisors(n, generator=True)),
        (composite(n) for n in count(1)),
    )


def A244440_gen(startvalue=1):
    return (
        n
        for n in count(max(startvalue, 1))
        if max(set(s := str(totient(n) + n))) == "1" and s.count("1") == 1
    )


def A245576_gen():
    return (
        p
        for p in (prime(i) for i in count(1))
        if not (str(p).count("0") or str(p**2).count("0"))
    )


def A245802_gen(startvalue=1):
    return (
        n for n in count(max(startvalue, 1)) if not n % sum(int(d) for d in oct(n)[2:])
    )


def A246428_gen():
    return (
        int(n)
        for n in (str(prime(x)) for x in count(1))
        if isprime(int(str(sum([int(d) for d in n])) + n))
    )


def A246503_gen(startvalue=1):  # generator of terms
    if startvalue <= 1:
        yield 1
    for i in count(max(startvalue, 2)):
        d, n = i * i, 1
        for _ in range(i):
            n = (2 * n) % d
            if n == 1:
                yield i
                break


def A246520(n):
    return max(int(bin(n - k)[2:] + bin(n + k)[2:], 2) for k in range(n + 1))


def A246600(n):
    return sum(1 for d in divisors(n) if n | d == n)


def A246831(n):
    return int(bin(n)[2:] + bin(3 * n)[2:], 2)


def A246839_gen():  # generator of terms
    p5 = 0
    for n in count(5, 5):
        yield from [p5] * 5
        p5 += multiplicity(5, n) * n


def A247363(n):
    return sorted((b + 1) ** ((2 * n - 1) - b) for b in range(2 * n - 1))[n - 1]


def A247875_gen(startvalue=0):
    return (n for n in count(max(startvalue, 0)) if not n % 2 or "00" in bin(n))


def A249357_gen():  # generator of terms
    yield from [1, 2, 3]
    l1, l2 = 3, 2
    while True:
        i = l1 + l2
        while True:
            if gcd(i, l1) == 1 and gcd(i, l2) > 1:
                yield i
                l2, l1 = l1, i
                break
            i += 1


def A249515_gen():  # generator of terms
    yield 0
    for g in count(1):
        xp, ylist = [], []
        for i in range(9 * g, -1, -1):
            x = set(str(i))
            if not x in xp:
                xv = [int(d) for d in x]
                imin = int("".join(sorted(str(i))))
                if max(xv) * (g - len(x)) >= imin - sum(xv) and i - sum(xv) >= min(
                    xv
                ) * (g - len(x)):
                    xp.append(x)
                    for y in product(x, repeat=g):
                        if (
                            y[0] != "0"
                            and set(y) == x
                            and set(str(sum([int(d) for d in y]))) == x
                        ):
                            ylist.append(int("".join(y)))
        yield from sorted(ylist)


def A249751_gen(startvalue=3):
    return (n for n in count(max(startvalue, 3)) if n == 3 or pow(n, n, n - 2) == n - 4)


def A249902_gen():
    return chain(
        (2,),
        (
            n
            for n in (d**2 for d in count(1))
            if isprime(2 * n - 1) and isprime(divisor_sigma(n))
        ),
    )


def A251411_gen():  # generator of terms
    n = 1
    for m in A098550_gen():
        if m == n:
            yield n
        n += 1


def A251413_gen():  # generator of terms
    yield from [1, 3, 5]
    l1, l2, s, b = 5, 3, 7, {}
    while True:
        i = s
        while True:
            if not i in b and gcd(i, l1) == 1 and gcd(i, l2) > 1:
                yield i
                l2, l1, b[i] = l1, i, True
                while s in b:
                    b.pop(s)
                    s += 2
                break
            i += 2


def A251414_gen():  # generator of terms
    yield from [1, 2, 3]
    l1, l2, s, b = 5, 3, 7, {}
    while True:
        i = s
        while True:
            if not i in b and gcd(i, l1) == 1 and gcd(i, l2) > 1:
                yield (i + 1) // 2
                l2, l1, b[i] = l1, i, True
                while s in b:
                    b.pop(s)
                    s += 2
                break
            i += 2


def A251415_gen():  # generator of terms
    yield 1
    l1, l2, s, u, l, b = 3, 2, 4, 1, 1, {}
    for n in count(4):
        i = s
        while True:
            if not i in b and gcd(i, l1) == 1 and gcd(i, l2) > 1:
                l2, l1, b[i] = l1, i, 1
                while s in b:
                    b.pop(s)
                    s += 1
                if u * n < i * l:
                    yield i
                    u, l = i, n
                break
            i += 1


def A251554_gen():  # generator of terms
    yield from [1, 2, 5]
    l1, l2, s, b = 5, 2, 3, {5}
    while True:
        i = s
        while True:
            if not i in b and gcd(i, l1) == 1 and gcd(i, l2) > 1:
                yield i
                l2, l1 = l1, i
                b.add(i)
                while s in b:
                    b.remove(s)
                    s += 1
                break
            i += 1


def A251561(n):
    if n == 2:
        return 4
    q, r = divmod(n, 2)
    if r:
        if isprime(n):
            return 2 * n
        return n
    if isprime(q):
        return q
    return n


def A251862_gen(startvalue=0):
    return (n for n in count(max(startvalue, 0)) if pow(-3, n, n + 3) == 3)


def A253051_gen():  # generator of terms
    yield 1
    c, l1, l2, s, b = 1, 2, 1, 3, set()
    while True:
        i = s
        while True:
            if not (i in b or i & l1) and i & l2:
                if i & 1:
                    yield c
                    c = 0
                else:
                    c += 1
                l2, l1 = l1, i
                b.add(i)
                while s in b:
                    b.remove(s)
                    s += 1
                break
            i += 1


def A253147_gen():
    return filter(
        lambda n: n >= 256 and is_pal(intbase(sympydigits(n, 256)[-1:0:-1], 256)),
        pal10_gen(),
    )


def A253148_gen():
    return filter(lambda n: n >= 256 and is_pal(n, 256), pal10_gen())


def A253149_gen():
    return filter(
        lambda n: n >= 256 and isprime(intbase(sympydigits(n, 256)[-1:0:-1], 256)),
        (prime(n) for n in count(1)),
    )


def A254073(n):
    ndict = {}
    for i in range(n):
        m = pow(i, 3, n)
        if m in ndict:
            ndict[m] += 1
        else:
            ndict[m] = 1
    count = 0
    for i in ndict:
        ni = ndict[i]
        for j in ndict:
            k = (1 - i - j) % n
            if k in ndict:
                count += ni * ndict[j] * ndict[k]
    return count


def A254231_gen():  # generator of terms
    yield 1
    a, b, c, d = 0, 0, 1, 1
    while True:
        a, b, c = b, c, a + b + c
        d *= c
        yield d


def A254315(n):
    return len(
        set(
            x
            for l in (
                [d for d in str(p)] + [d for d in str(e) if d != "1"]
                for p, e in factorint(n).items()
            )
            for x in l
        )
    )


def A254756_gen():  # generator of terms
    for n in count(16):
        s = format(n, "x")
        for i in range(1, len(s)):
            if not (is_prime(int(s[i:], 16)) and is_prime(int(s[:-i], 16))):
                break
        else:
            yield n


def A255500(n):
    return (p := prime(n)) ** 4 * (p * (p * (p * (p * (p + 5) + 4) - 1) - 5) + 2) // 6


def A255501(n):
    return n**4 * (n * (n * (n * (n * (n + 5) + 4) - 1) - 5) + 2) // 6


def A256437_gen(startvalue=0):
    (
        i
        for i in count(max(startvalue, 0))
        if str(i**2 + int(str(i)[::-1]) ** 2)
        == str(i**2 + int(str(i)[::-1]) ** 2)[::-1]
    )


def A256481(n):
    if n in (6930, 50358, 56574, 72975):
        return 0
    if n == 0:
        return 2
    sn = str(n)
    for i in count(1):
        for j in range(1, 10, 2):
            si = str(j) * i
            p = int(sn + si)
            if isprime(p):
                return int(p)


def A256967_gen():  # generator of terms
    x, d, f1, f2 = 1, 1, 1, 0
    while True:
        for i in range(f1):
            yield x
            x += d
        d += 1
        f1, f2 = f1 + f2, f1


def A256968_gen():  # generator of terms
    count, bn, bd = 0, 1, 1
    for k in count(1):
        p = prime(k)
        bn *= p
        bd *= p - 1
        while bn >= count * bd:
            yield k
            count += 1


def A257341_gen():  # generator of terms
    m = 2
    for i in count(2):
        for j in range(1, i):
            x = Fraction(j, i)
            if x.denominator == i:
                yield int(m * x) % 2
                m *= 2


def A257552_gen():  # generator of terms
    p = 2
    while True:
        q = p**2 - 2
        if isprime(q):
            r = q**2 - 2
            if isprime(r):
                s = r**2 - 2
                if isprime(s):
                    yield p
        p = nextprime(p)


def A257831(n):
    return int("".join((format(int(d), "b") for d in str(n))))


def A257901_gen(startvalue=1):  # generator of terms
    l = []
    for d in permutations("0123456789", 10):
        if d[0] != "0":
            d2 = int("".join(d))
            if d2 >= startvalue:
                d = d2
                r = d2 % 5
                while not r:
                    d2, r = divmod(d2, 5)
                l.append((d2, d))
    l.sort()
    yield from (b for a, b in l)


def A258103(n):
    """requires 2 <= n <= 62"""
    c, sm, sq = (
        0,
        mpz("".join([gmpy2digits(i, n) for i in range(n - 1, -1, -1)]), n),
        mpz("".join(["1", "0"] + [gmpy2digits(i, n) for i in range(2, n)]), n),
    )
    m = isqrt(sq)
    sq = m * m
    m = 2 * m + 1
    while sq <= sm:
        if len(set(gmpy2digits(sq, n))) == n:
            c += 1
        sq += m
        m += 2
    return c


def A258774(n):
    return (lambda x: x * (x + 1) + 1)(divisor_sigma(n))


def A260373_gen():  # generator of terms
    yield 1
    g = 1
    for i in count(1):
        g *= i
        s = isqrt(g)
        t = s**2
        return t if g - t - s <= 0 else t + 2 * s + 1


def A260636_gen():  # generator of terms
    b = 3
    for n in count(1):
        yield b % n
        b = b * 3 * (3 * n + 2) * (3 * n + 1) // ((2 * n + 2) * (2 * n + 1))


def A260640_gen():  # generator of terms
    b = 3
    for n in count(1):
        if not b % n:
            yield n
        b = b * 3 * (3 * n + 2) * (3 * n + 1) // ((2 * n + 2) * (2 * n + 1))


def A260674_gen():
    return (p for p in (prime(n) for n in count(1)) if gcd(2**p + 1, 3**p + 1) > 1)


def A261011_gen(startvalue=1):
    return (
        n
        for n in count(max(startvalue, 1))
        if not n % (lambda x: x[0] + (0 if x[1] else 1))(integer_nthroot(n, 3))
    )


def A261328_gen():  # generator of terms
    bset = set()
    for i in count(1):
        c = i**3
        for d in divisors(c, generator=True):
            d2 = c // d
            if d >= d2:
                m, r = divmod(d + d2, 2)
                if not r:
                    n = m - d2
                    if n > 0 and (m, n) not in bset and is_square(c * m + d2 * n**2):
                        bset.add((m, n))
                        yield m


def A261296_gen():  # generator of terms
    bset = set()
    for i in count(1):
        c = i**3
        for d in divisors(c, generator=True):
            d2 = c // d
            if d >= d2:
                m, r = divmod(d + d2, 2)
                if not r:
                    n = m - d2
                    if n > 0 and (m, n) not in bset and is_square(c * m + d2 * n**2):
                        bset.add((m, n))
                        yield n


def A262069_gen():
    return filter(lambda n: is_pal(n, 60), pal10_gen())


def A264600(n):
    return sorted(str(i)[::-1] for i in range(n + 1)).index(str(n)[::-1])


def A266727_gen():  # generator of terms
    blist = [0, 1, 7]
    bset = set(blist)
    yield from blist
    for i in count(0):
        n, flag = blist[-1] + 1, False
        while True:
            for j in range(i + 2, 0, -1):
                m = 2 * blist[j] - n
                if m in bset:
                    break
                if m < 0:
                    flag = True
                    break
            else:
                blist.append(n)
                bset.add(n)
                yield n
                break
            if flag:
                blist.append(n)
                bset.add(n)
                yield n
                break
            n += 1


def A267310(n):
    m = sum(d * divisor_sigma(d) ** (n // d) for d in divisors(n, generator=True))
    return m // gcd(m, n)


def A267764_gen():
    return (int(d, 4) for d in (str(i**2) for i in range(10**6)) if max(d) < "4")


def A267768_gen():
    return (int(s, 8) for s in (str(i**2) for i in range(10**6)) if max(s) < "8")


def A268383_gen():  # generator of terms
    b = 0
    yield 0
    for i in count(1):
        b += 1 - len(list(filter(bool, format(i, "b").split("0")))) % 2
        yield b


def A268982(n):
    return n // gcd(
        n, sum(d * divisor_sigma(d) ** (n // d) for d in divisors(n, generator=True))
    )


def A269723_gen():  # generator of terms
    blist = [0]
    yield 0
    while True:
        x = blist + [1 - d for d in blist] * 2
        blist += x
        yield from x


def A271901(n):
    p = prime(n)
    i, a, b, c = 1, 1, 1, 2 % p
    while a != 1 or b != 1 or c != 1:
        i += 1
        a, b, c = b, c, (a + c) % p
    return i


def A272670_gen(startvalue=1):
    return (
        n
        for n in count(max(startvalue, 1))
        if bin(n)[2:] != bin(n)[:1:-1]
        and bin(n)[2:].rstrip("0") == bin(n)[:1:-1].lstrip("0")
    )


def A272680(n):
    if n == 0:
        return 0
    else:
        d, nd = 1, n
        while True:
            x = (isqrt(nd - 1) + 1) ** 2
            if x < nd + d:
                return int(x)
            d *= 2
            nd *= 2


def A272681(n):
    if n == 0:
        return 0
    else:
        d, nd = 1, n
        while True:
            x = (isqrt(nd - 1) + 1) ** 2
            if x < nd + d:
                return int(bin(x)[2:])
            d *= 2
            nd *= 2


def A273190(n):
    return isqrt(2 * n - 1) - isqrt(n - 1) if n > 0 else 0


def A273372_gen():
    return ((10 * n + m) ** 2 for n in count(0) for m in (1, 9))


def A274944_gen():
    return (
        j * 10 ** (i + 1) + 10 * (j**2 + k**2) + k
        for i in count(1)
        for j in range(1, 10)
        for k in range(10)
        if 10 ** (i - 1) <= j**2 + k**2 < 10**i
    )


def A274945_gen():
    return (
        j * 10 ** (i + 1) + 10 * (j**2 + k**2) + k
        for i in count(1)
        for j in range(1, 10)
        for k in range(10)
        if j**2 + k**2 < 10**i
    )


def A274962_gen():
    return chain(
        (2,),
        (
            n
            for n, s in ((d**2, divisor_sigma(d**2)) for d in count(1))
            if isprime(s) and isprime(s + 2)
        ),
    )


def A274963_gen():
    return (
        n
        for n, s in ((d**2, divisor_sigma(d**2)) for d in count(1))
        if isprime(s) and isprime(s - 2)
    )


def A274967_gen(startvalue=3):  # generator of terms
    for n in count(max(startvalue + 1 - startvalue % 2, 3), 2):
        if not isprime(n):
            k = 3
            while k * (k + 1) <= 2 * n:
                if not (2 * (k * (k - 2) + n)) % (k * (k - 1)):
                    break
                k += 1
            else:
                yield n


def A274968_gen(startvalue=4):  # generator of terms
    for n in count(max(startvalue + startvalue % 2, 4), 2):
        k = 3
        while k * (k + 1) <= 2 * n:
            if not (2 * (k * (k - 2) + n)) % (k * (k - 1)):
                break
            k += 1
        else:
            yield n


def A277624_gen(startvalue=2):  # generator of terms
    for n in count(max(startvalue, 2)):
        if not is_prime(n):
            for p in primefactors(n):
                if isqrt(p) * p > n:
                    yield n
                    break


def A279610(n):
    return int(
        "".join(str(d) for d in range((n - 1) * (n - 2) // 2 + 1, n * (n - 1) // 2 + 2))
    )


def A280879_gen():  # generator of terms
    t = 1
    for n in count(1):
        n += 1
        h = totient(n)
        t2 = t + h
        if n % 2 and n % 6 != 3 and 2 * (n * (h * n - 2 * t2 + 1) + t2) < 1:
            yield n
        t = t2


def A286415_gen():  # generator of terms
    for l in count(1):
        for d in "123456789":
            for w in product("1379", repeat=l):
                s = d + "".join(w)
                n = int(s)
                for i in range(l):
                    if not isprime(int(s)):
                        break
                    s = s[-1] + s[:-1]
                else:
                    if not isprime(int(s)):
                        yield n


def A286900(n):
    m = nextprime(n)
    return (m + n) * (m - n + 1) // 2


def A287198_gen(startvalue=2):  # generator of terms
    for n in count(max(startvalue, 2)):
        s = str(n)
        if not is_prime(n) and "0" not in s:
            k = n
            for i in range(len(s) - 1):
                s = s[1:] + s[0]
                m = mpz(s)
                if is_prime(m) or gcd(k, m) > 1:
                    break
                k *= m
            else:
                yield n


def A287653_gen():  # generator of terms
    pq, qr, rs, s = 6, 15, 35, 7
    while True:
        n = pq + qr + rs
        if isprime(n):
            yield n
        t = nextprime(s)
        pq, qr, rs, s = qr, rs, s * t, t


def A296104_gen(startvalue=2):
    return (n for n in count(max(startvalue, 2)) if pow(2, n, n - 1) == 3 % (n - 1))


@lru_cache(maxsize=None)
def A298406(n):
    if n <= 2:
        return 1
    c, j = 2 * A298406(n - 1) - A298406(n - 3), 2
    k1 = n // j
    while k1 > 1:
        j2 = n // k1 + 1
        c += (j2 - j) * A298406(k1)
        j, k1 = j2, n // j2
    return c + n - j + 1


@lru_cache(maxsize=None)
def A298407(n):
    if n <= 2:
        return n + 1
    c, j = 2 * A298407(n - 1) - A298407(n - 3), 2
    k1 = n // j
    while k1 > 1:
        j2 = n // k1 + 1
        c += (j2 - j) * A298407(k1)
        j, k1 = j2, n // j2
    return c + 2 * (n - j + 1)


@lru_cache(maxsize=None)
def A298408(n):
    if n <= 2:
        return 1
    c, j = 2 * A298408(n - 1) - A298408(n - 3), 2
    k1 = n // j
    while k1 > 1:
        j2 = n // k1 + 1
        c += (j2 * (j2 - 1) - j * (j - 1)) * A298408(k1) // 2
        j, k1 = j2, n // j2
    return c + (n * (n + 1) - j * (j - 1)) // 2


@lru_cache(maxsize=None)
def A298409(n):
    if n <= 2:
        return n + 1
    c, j = 2 * A298409(n - 1) - A298409(n - 3), 2
    k1 = n // j
    while k1 > 1:
        j2 = n // k1 + 1
        c += (j2 * (j2 - 1) - j * (j - 1)) * A298409(k1) // 2
        j, k1 = j2, n // j2
    return c + 2 * (n * (n + 1) - j * (j - 1)) // 2


def A300062_gen():  # generator of terms
    yield 1
    s, j = 1, 1
    for i in count(2):
        j, si = j + 1, str(i)
        while si not in str(s + j):
            j += 1
        yield j
        s += j


def A300078(n):
    zr, zc, c = Fraction(0, 1), Fraction(0, 1), 0
    cr, cc = Fraction(-5, 4) - Fraction(1, 10 ** (2 * n)), Fraction(1, 10**n)
    zr2, zc2 = zr**2, zc**2
    while zr2 + zc2 <= 4:
        zr, zc = zr2 - zc2 + cr, 2 * zr * zc + cc
        zr2, zc2 = zr**2, zc**2
        c += 1
    return c


def A301912_gen():  # generator of terms
    n = 0
    for k in count(0):
        if n % 10 ** (len(str(k))) == k:
            yield k
        n += (k + 1) ** 3


def A269266(n):
    return pow(2, n, 31)


def A308194(n):
    c, x = 0, n
    while x != 5:
        d = divisors(x)
        l = len(d)
        x = d[(l - 1) // 2] + d[l // 2]
        c += 1
    return c


def A308736_gen():  # generator of terms
    mlist = [False] * 4
    for n in count(3, 2):
        if mlist[0] and mlist[1] and mlist[2] and mlist[3]:
            yield n
        n += 2
        f = factorint(n + 6)
        mlist = mlist[1:] + [(len(f), sum(f.values())) == (2, 3)]


def A319302_gen(startvalue=1):  # generator of terms
    for n in count(max(startvalue, 1)):
        for d in split("1+", bin(n)[2:]):
            if isprime(len(d)):
                yield n
                break


def A319419(n):
    s = "".join(
        d[:-1] for d in split("(0+)|(1+)", bin(n)[2:]) if d not in {"", "0", "1", None}
    )
    return -1 if s == "" else int(s, 2)


def A320129(n):
    return (
        1
        if n == 0
        else sum(
            1
            for p in multiset_partitions(list(range(1, 2 * n + 1)), n)
            if max(len(d) for d in p) == 2 and len(set(sum(d) for d in p)) == n
        )
    )


def A320261(n):
    return int(
        "".join(
            "1" + d for d in split("(0+)|(1+)", bin(n)[2:]) if d != "" and d != None
        ),
        2,
    )


def A321294(n):
    return sum(totient(d) * (n // d) ** (n + 1) for d in divisors(n, generator=True))


def A321441(n):
    if n == 0:
        return 1
    c = 0
    for i in range(n):
        mi = n + i * (i + 1) // 2
        for j in range(i, n):
            mj = mi + j * (j + 1) // 2
            for k in range(j + 1, n + 1):
                r = mj - k * k
                if r < 0:
                    break
                if not r % k:
                    c += 1
    return c


def A321536(n):
    return int(
        "".join(
            d + d[0]
            for d in split("(0+)|(1+)|(2+)|(3+)|(4+)|(5+)|(6+)|(7+)|(8+)|(9+)", str(n))
            if d != "" and d != None
        )
    )


def A321537(n):
    return int(
        "0"
        + "".join(
            d[:-1]
            for d in split("(0+)|(1+)|(2+)|(3+)|(4+)|(5+)|(6+)|(7+)|(8+)|(9+)", str(n))
            if d != "" and d != None
        )
    )


def A323711_gen(startvalue=9):
    return (
        n
        for n in count(max(9, startvalue + (9 - startvalue % 9) % 9, 9))
        if sorted(str(n)) == sorted(str(2 * n)) == sorted(str(3 * n))
    )


def A323835(n):
    mset, m, c = set(), n, 0
    while True:
        if m == 0 or m == 1:
            return c
        m = int(
            "0" + "".join(d if str(2 * m).count(d) == 1 else "" for d in str(2 * m))
        )
        if m in mset:
            return -1
        mset.add(m)
        c += 1


def A325230_gen(startvalue=2):
    return (
        n
        for n, m in ((n, factorint(n)) for n in count(max(startvalue, 2)))
        if len(m) == 2 and m[min(m)] == 1
    )


def A327171(n):
    return totient(n) * numbercore(n)


def A328330(n):
    c, m = 1, sum((6, 2, 5, 5, 4, 5, 6, 3, 7, 6)[int(d)] for d in str(n))
    while m != n:
        c += 1
        n, m = m, sum((6, 2, 5, 5, 4, 5, 6, 3, 7, 6)[int(d)] for d in str(m))
    return c


def A331889_T(n, k):
    if k == 1:
        return n * (n + 1) // 2
    if n == 1:
        return int(factorial(k))
    if k == 2:
        return n * (n + 1) * (2 * n + 1) // 3
    nk = n * k
    nktuple = tuple(range(1, nk + 1))
    nkset = set(nktuple)
    count = int(factorial(nk))
    for firsttuple in combinations(nktuple, n):
        nexttupleset = nkset - set(firsttuple)
        for s in permutations(sorted(nexttupleset), nk - 2 * n):
            llist = sorted(nexttupleset - set(s), reverse=True)
            t = list(firsttuple)
            for i in range(0, k - 2):
                itn = i * n
                for j in range(n):
                    t[j] *= s[itn + j]
            t.sort()
            v = 0
            for i in range(n):
                v += llist[i] * t[i]
            if v < count:
                count = v
    return count


def A332300(n):
    x = abs(bernoulli(2 * n).p)
    return 1 if x == 1 else min(primefactors(x))


def A332597(n):
    return (
        8
        if n == 1
        else 4 * (n - 1) * (8 * n - 1)
        + 8 * sum(totient(i) * (n + 1 - i) * (n + i + 1) for i in range(2, n // 2 + 1))
        + 8
        * sum(
            totient(i) * (n + 1 - i) * (2 * n + 2 - i) for i in range(n // 2 + 1, n + 1)
        )
    )


def A332598(n):
    return (
        22 * n - 17
        if n <= 2
        else 4 * (n - 1) * (3 * n - 1)
        + 12 * sum(totient(i) * (n + 1 - i) * i for i in range(2, n // 2 + 1))
        + 4
        * sum(
            totient(i) * (n + 1 - i) * (2 * n + 2 - i) for i in range(n // 2 + 1, n + 1)
        )
    )


def A332612(n):
    return sum(totient(i) * (n - i) * (2 * n - i) for i in range(2, n)) // 2


def A333072(n):
    f = 1
    for i in range(1, n + 1):
        f = lcm(f, i)
    f, glist = int(f), []
    for i in range(1, n + 1):
        glist.append(f // i)
    m = 1 if n < 2 else primorial(n, nth=False) // primorial(n // 2, nth=False)
    k = m
    while True:
        p, ki = 0, k
        for i in range(1, n + 1):
            p = (p + ki * glist[i - 1]) % f
            ki = (k * ki) % f
        if p == 0:
            return k
        k += m


def A333196(n):
    fs = factorint(harmonic(n).q)
    return (
        1
        if len(fs) == 0
        else prod(p ** (fs[p] // n + 1 if fs[p] % n else fs[p] // n) for p in fs)
    )


def A333269_gen(startvalue=1):
    return (n for n in count(max(startvalue, 1)) if n == 1 or pow(17, n, n) == 2)


@lru_cache(maxsize=None)
def A333450(n):
    c, j = 2 * (n + 1) - prime(n), 2
    k1 = n // j
    while k1 > 1:
        j2 = n // k1 + 1
        c += (j2 - j) * A333450(k1)
        j, k1 = j2, n // j2
    return 2 * j - c


def A333876(n):
    for i in range(n):
        q = 2**n - 1
        for d in multiset_permutations("0" * i + "1" * (n - 1 - i)):
            p = q - int("".join(d), 2)
            if isprime(p):
                return p


def A333877(n):
    for i in range(n - 1, -1, -1):
        q = 2**n - 1
        for d in multiset_permutations("0" * i + "1" * (n - 1 - i)):
            p = q - int("".join(d), 2)
            if isprime(p):
                return p


def A334045(n):
    m = n | (n - 1)
    return 2 ** (len(bin(m)) - 2) - 1 - m


def A334074(n):
    b = comb(2 * n, n)
    return sum(
        Fraction(1, p) for p in range(2, n + 1) if b % p != 0 and isprime(p)
    ).numerator


def A334075(n):
    b = comb(2 * n, n)
    return sum(
        Fraction(1, p) for p in range(2, n + 1) if b % p != 0 and isprime(p)
    ).denominator


def A336018(n):
    return len(bin(n**n // (2 ** ((len(bin(n)) - 3) * n)))) - 3


def A336614(n):
    c = 0
    for d in product((0, 1), repeat=n * n):
        M = Matrix(d).reshape(n, n)
        if M * M == M.T:
            c += 1
    return c


def A337175(n):
    return divisor_count(n) ** 2 // 4


def A337449_gen():  # generator of terms
    p, q = 2, 1
    for k in count(0):
        if p % sum(int(d) for d in str(p)) == 0:
            yield k
        p, q = q, p + q


def A338136(n):
    k, n2, m = 2, n**2, (n + 1) ** 2
    while True:
        nj = n2
        while nj < m:
            r = m % nj
            if r > 1 and is_power(r):
                return k
            nj *= n
        k += 1
        m *= n + 1


def A338267(n):
    p, q, r = prime(n) ** 2, prime(n + 1) ** 2, prime(n + 2) ** 2
    return (isqrt(4 * p * q - (p + q - r) ** 2) + 2) // 4


def A340013(n):
    f = factorial(n)
    return (nextprime(f) - prevprime(f)) // 2


def A340869_gen():  # generator of terms
    plist = [2, 3, 5, 7, 11, 13, 17, 19, 23]
    for k in count(1):
        d = Matrix(plist).reshape(3, 3).det()
        if d >= 0 and integer_nthroot(d, 2)[1]:
            yield k
        plist = plist[1:] + [nextprime(plist[-1])]


def A341319(n):
    return min(
        (d // 2 + 1) * (e // 2 + 1)
        for d, e in ((v, n**2 // v) for v in divisors(n**2) if v <= n)
    )


def A341578(n):
    c = min(
        (d // 2 + 1) * (n**2 // (2 * d) + 1)
        for d in divisors(n**2, generator=True)
        if d <= n
    )
    return c if n % 2 else min(c, (n // 2 + 1) ** 2 - 1)


def A341709(n):
    m, c = 1, 0
    while n > 0:
        n, b = divmod(n, 2)
        c += b * int(str(m)[::-1])
        m *= 2
    return c


def A341721(n):
    return min(
        (d + 2 - (d % 2)) * (e + 2 - (e % 2)) // 4 + int((d % 2) or (e % 2)) - 1
        for d, e in ((v, n // v) for v in divisors(n) if v * v <= n)
    )


def A342023(n):
    f = factorint(n)
    for p in f:
        if p <= f[p]:
            return 1
    return 0


def A342121(n):
    a, b = sorted([n, int(bin(n)[:1:-1], 2)])
    return b % a if n > 0 else 0


def A342122(n):
    return int(bin(n)[:1:-1], 2) % n if n > 0 else 0


def A342123(n):
    return n % int(bin(n)[:1:-1], 2) if n > 0 else 0


def A342126(n):
    s = bin(n)[2:]
    i = s.find("0")
    return n if i == -1 else (2**i - 1) * 2 ** (len(s) - i)


def A342260(n):
    k = 1
    while sympydigits(k**2, n).count(n - 1) != n:
        k += 1
    return k


def A342545(n):
    for a in range(1, n):
        p, q = integer_nthroot(a * n**n, 2)
        if q:
            return p
    l = 1
    while True:
        cmax = n ** (l + n + 1)
        for a in range(1, n):
            c = cmax
            for b in product(range(1, n), repeat=l):
                for d in multiset_permutations((0,) * n + b):
                    p, q = integer_nthroot(reduce(lambda c, y: c * n + y, [a] + d), 2)
                    if q:
                        c = min(c, p)
            if c < cmax:
                return c
        l += 1


def A342950_gen(startvalue=1):  # generator of terms
    for n in count(max(startvalue, 1)):
        if n % 10:
            m = n
            for p in (2, 3, 5, 7):
                q, r = divmod(m, p)
                while r == 0:
                    m = q
                    q, r = divmod(m, p)
            if m == 1:
                yield n


def A342996(n):
    return partition(primorial(n)) if n > 0 else 1


def A343206(n):
    return sum(stirling(n, i, signed=True) * bernoulli(i) for i in range(n + 1)).p


def A343675_helperf(w):
    for s in w:
        for t in range(int(s[-1]) + 1, 10, 2):
            yield s + str(t)


def A343675_helperg(w):
    for s in w:
        for t in range(1 - int(s[-1]) % 2, int(s[-1]), 2):
            yield s + str(t)


def A343675_gen():  # generator of terms
    yield from [2, 3, 5, 7]
    for l in count(1):
        for d in "1379":
            x = d
            for i in range(1, l + 1):
                x = A343675_helperg(x) if i % 2 else A343675_helperf(x)
            yield from (int(p + p[-2::-1]) for p in x if isprime(int(p + p[-2::-1])))
            y = d
            for i in range(1, l + 1):
                y = A343675_helperf(y) if i % 2 else A343675_helperg(y)
            yield from (int(p + p[-2::-1]) for p in y if isprime(int(p + p[-2::-1])))


def A343676(n):
    c = 0
    for d in "123456789":
        x = d
        for i in range(1, n):
            x = A343675_helperg(x) if i % 2 else A343675_helperf(x)
        c += sum(1 for p in x if isprime(int(p)))
        if n > 1:
            y = d
            for i in range(1, n):
                y = A343675_helperf(y) if i % 2 else A343675_helperg(y)
            c += sum(1 for p in y if isprime(int(p)))
    return c


def A343677(n):
    if n == 0:
        return 4
    c = 0
    for d in "1379":
        x = d
        for i in range(1, n + 1):
            x = A343675_helperg(x) if i % 2 else A343675_helperf(x)
        c += sum(1 for p in x if isprime(int(p + p[-2::-1])))
        y = d
        for i in range(1, n + 1):
            y = A343675_helperf(y) if i % 2 else A343675_helperg(y)
        c += sum(1 for p in y if isprime(int(p + p[-2::-1])))
    return c


def A343999(n):
    fs = factorint(2 * n)
    plist = [p ** fs[p] for p in fs]
    return int(
        min(
            k
            for k in (crt(plist, d)[0] for d in product([0, -1], repeat=len(plist)))
            if k > 0
        )
        % 2
    )


def A344589(n):
    m = A011772(n)
    return sum(1 for d in divisors(n) if A011772(d) < m)


def A345419(n):
    return igcdex(3, prime(n))[0]


def A345423(n):
    return sum(
        u
        for u, v, w in (igcdex(x, y) for x in range(1, n + 1) for y in range(1, n + 1))
        if w == 1
    )


def A345424(n):
    return sum(
        v
        for u, v, w in (igcdex(x, y) for x in range(1, n + 1) for y in range(1, n + 1))
        if w == 1
    )


def A345425(n):
    return sum(
        u + v
        for u, v, w in (igcdex(x, y) for x in range(1, n + 1) for y in range(1, n + 1))
        if w == 1
    )


def A345426(n):
    return sum(
        u
        for u, v, w in (igcdex(x, y) for x in range(1, n + 1) for y in range(1, n + 1))
    )


def A345430(n):
    return sum(
        abs(v)
        for u, v, w in (igcdex(x, y) for x in range(1, n + 1) for y in range(1, n + 1))
        if w == 1
    )


def A345431(n):
    return sum(
        u**2 + v**2
        for u, v, w in (igcdex(x, y) for x in range(1, n + 1) for y in range(1, n + 1))
        if w == 1
    )


def A345432(n):
    return sum(
        abs(u)
        for u, v, w in (igcdex(x, y) for x in range(1, n + 1) for y in range(1, n + 1))
    )


def A345695(n):
    zlist = [
        z
        for z in (igcdex(x, y) for x in range(1, n + 1) for y in range(1, n + 1))
        if z[2] == 1
    ]
    return pvariance(len(zlist) * abs(v) for u, v, w in zlist)


def A344005(n):
    if n == 1:
        return 1
    plist = tuple(p**q for p, q in factorint(n).items())
    return (
        n - 1
        if len(plist) == 1
        else int(
            min(
                min(crt((m, n // m), (0, -1))[0], crt((n // m, m), (0, -1))[0])
                for m in (
                    prod(d)
                    for l in range(1, len(plist) // 2 + 1)
                    for d in combinations(plist, l)
                )
            )
        )
    )


def A346598(n):
    return sum(1 for m in range(1, n * (n + 1) + 1) if A344005(m) == n)


def A346622(n):
    return (
        0
        if n <= 2
        else A346622(n - 1) + (1 if n % 2 and len(primefactors(n)) == 2 else 0)
    )


def A346623(n):
    return (
        0
        if n <= 2
        else A346623(n - 1) + (n if n % 2 and len(primefactors(n)) == 2 else 0)
    )


def A346942_gen():
    return (
        100 * n
        for n in count(99)
        if n % 10 and (lambda x: x[0] == x[1] == x[2] == x[3] != x[4])(str(n**2))
    )


def A347308_gen():  # generator of terms
    yield 1
    nset, m, c, j, i = {1}, 2, 0, 2, 1
    while True:
        i += 1
        k = m
        while k == j or gcd(k, j) == 1 or k in nset:
            k += 1
        if k > c:
            c = k
            yield i
        j = k + 1
        nset.add(k)
        while m in nset:
            m += 1


def A347319(n):
    return n * (n**2 * (2 * n - 3) + 3) + 1


def A350518(n):
    q = 2
    while True:
        a, b = integer_nthroot(q * (n + 1) - n, 2)
        if b and isprime(a):
            return q
        q = nextprime(q)


def A350517(n):
    p = 2
    while True:
        a, b = divmod(p**2 + n, n + 1)
        if not b and isprime(a):
            return p
        p = nextprime(p)


def A347755_gen():  # generator of terms
    yield 1
    nset, m, j = {1}, 2, 2
    while True:
        k = m
        while k == j or gcd(k, j) == 1 or k in nset:
            k += 1
        j = k + 1
        nset.add(k)
        yield m
        while m in nset:
            m += 1


def A347757_gen():  # generator of terms
    yield 1
    nset, m, j, i = {1}, 2, 2, 1
    while True:
        i += 1
        k = m
        while k == j or gcd(k, j) == 1 or k in nset:
            k += 1
        j = k + 1
        nset.add(k)
        if k == m:
            yield i
        while m in nset:
            m += 1


def A348295(n):
    return sum(-1 if (isqrt(2 * k * k) - k) % 2 else 1 for k in range(1, n + 1))


def A349190_gen():
    return filter(lambda n: prod(accumulate(int(d) for d in str(n))) == n, count(1))


def A004287(n):
    if n > 0:
        for i in range(1, 2**n):
            s = bin(i)[2:]
            if not int(s, 7) % n:
                return int(s)
    return 0


def A004288(n):
    if n > 0:
        for i in range(1, 2**n):
            s = bin(i)[2:]
            if not int(s, 8) % n:
                return int(s)
    return 0


def A010338_gen():
    (
        n
        for n, s in ((i, continued_fraction_periodic(0, 1, i)[-1]) for i in count(1))
        if isinstance(s, list) and len(s) == 7
    )


def A010902_gen():  # generator of terms
    a, b = 14, 23
    yield from [a, b]
    while True:
        c, d = divmod(b**2, a)
        a, b = b, c + (0 if 2 * d < a else 1)
        yield b


def A015945_gen(startvalue=2):
    return (
        n
        for n in count(max(startvalue + startvalue % 2, 2), 2)
        if pow(2, n, n) == n // 2 - 1
    )


def A023273_gen():
    return (
        p
        for p in (prime(n) for n in count(1))
        if isprime(2 * p + 3) and isprime(4 * p + 9) and isprime(8 * p + 21)
    )


def A023804_gen():
    return filter(
        lambda n: len(set(s := gmpy2digits(n, 9))) == len(s), range(0, 381367045)
    )


def A027580_gen():  # generator of terms
    for i in count(1, 2):
        s = str(5 * (i * (i + 4) + 6))
        if s == s[::-1]:
            yield int(s)


def A029735_gen():  # generator of terms
    j = 0
    for i in count(0):
        s = format(j, "x")
        if s == s[::-1]:
            yield i
        j += 3 * i * (i + 1) + 1


def A029736_gen():  # generator of terms
    j = 0
    for i in count(0):
        s = format(j, "x")
        if s == s[::-1]:
            yield j
        j += 3 * i * (i + 1) + 1


def A030688(n):
    d, nd = 10, 10 * n**2
    while True:
        x = isqrt(nd - 1) + 1
        if not x % 10:
            x += 1
        x = x**2
        if x < nd + d:
            return x
        d *= 10
        nd *= 10


def A030697(n):
    d, nd = 10, 10 * n**3
    while True:
        x = integer_nthroot(nd - 1, 3)[0] + 1
        if not x % 10:
            x += 1
        x = x**3
        if x < nd + d:
            return x
        d *= 10
        nd *= 10


def A031598_gen():
    return (
        n
        for n, s in ((i, continued_fraction_periodic(0, 1, i)[-1]) for i in count(1))
        if isinstance(s, list) and len(s) % 2 == 0 and s[len(s) // 2 - 1] == 100
    )


def A031997_gen(startvalue=1):
    return (
        n
        for n in count(max(startvalue + 1 - startvalue % 2, 1), 2)
        if max(str(n**3)) <= "3"
    )


def A033861_gen():  # generator of terms
    x = 316
    while True:
        yield x
        x += int("".join(sorted(str(x))))


def A034874_gen():  # generator of terms
    a = 1
    for n in count(2):
        yield a
        a = n * int(str(a)[::-1])


def A035057_gen(startvalue=1):
    return (n for n in count(max(startvalue, 1)) if "1" not in str(2**n))


def A036433_gen(startvalue=1):  # generator of terms
    for i in count(max(startvalue, 1)):
        d = divisor_count(i)
        if d < 10 and str(d) in str(i):
            yield i


def A037255(n):
    return n * (n * (n * (n - 2) + 7) + 2) // 8


def A048055(startvalue=1):  # generator of terms
    for n in count(max(startvalue, 1)):
        s = sum(divisors(n))
        if not s % 2 and 2 * n <= s and (s - 2 * n) / 2 == sum(primefactors(n)):
            yield n


def A048335_gen():
    return chain((0,), (int(d * l, 11) for l in count(1) for d in "123456789a"))


def A048336_gen():
    return chain((0,), (int(d * l, 12) for l in count(1) for d in "123456789ab"))


def A048337_gen():
    return chain((0,), (int(d * l, 13) for l in count(1) for d in "123456789abc"))


def A048338_gen():
    return chain((0,), (int(d * l, 14) for l in count(1) for d in "123456789abcd"))


def A048339_gen():
    return chain((0,), (int(d * l, 15) for l in count(1) for d in "123456789abcde"))


def A048889_gen():
    return (
        m
        for m in (
            int(e + "".join(d))
            for l in count(1)
            for e in "1689"
            for d in product("01689", repeat=l)
        )
        if m % 10
        and not isprime(m)
        and isprime(int(str(m)[::-1].translate("".maketrans("69", "96"))))
    )


def A051640(n):
    m = 0
    while True:
        for b in range(2, n + 1):
            if b - 1 not in sympydigits(m, b)[1:]:
                break
        else:
            return m
        m += 1


def A052191(n):
    k = 0
    while True:
        k += n
        x = split("(0+|1+|2+|3+|4+|5+|6+|7+|8+|9+)", str(k))
        for d in x:
            if len(d) == 1:
                break
        else:
            return k


def A053547(n):
    s = int("".join(str(m) for m in range(n, 0, -1)))
    for i in count(1):
        s *= 10
        for j in range(1, 10**i, 2):
            x = s + j
            if isprime(x):
                return x


def A055227(n):
    return s if (f := factorial(n)) - (s := isqrt(f)) * (s + 1) <= 0 else s + 1


def A055227_gen():  # generator of terms
    yield 1
    g = 1
    for i in count(1):
        g *= i
        s = isqrt(g)
        yield s if g - s * (s + 1) <= 0 else s + 1


def A056825_gen():  # generator of terms
    nset = set()
    for n in count(1):
        cf = continued_fraction_periodic(0, 1, n)
        if len(cf) > 1:
            pal = tuple(cf[1][:-1])
            if pal not in nset:
                yield n
                nset.add(pal)


def A057683_gen(startvalue=0):
    return (
        n
        for n in count(max(startvalue, 0))
        if isprime(n**2 + n + 1)
        and isprime(n**3 + n + 1)
        and isprime(n**4 + n + 1)
    )


def A059000_gen():  # generator of terms
    for i in count(0):
        if i % 10:
            p = int(str(i**5)[::-1])
            if isprime(p):
                yield p


def A060474(n):
    return (n + 1) // gcd(n + 1, totient(n))


def A062936_gen(startvalue=1):  # generator of terms
    for n in count(max(startvalue, 1)):
        s = str(n * int(str(n)[::-1]))
        if s == s[::-1]:
            yield n


def A063569(n):
    m, k, s = 1, 6, str(n)
    while s not in str(k):
        m += 1
        k *= 6
    return m


def A063570(n):
    m, k, s = 1, 7, str(n)
    while s not in str(k):
        m += 1
        k *= 7
    return m


def A065914(n):
    pm = primorial(n)
    return primepi(3 * pm // 2 - 1) - primepi(pm // 2 - 1)


def A066713(n):
    m = 2**n
    return int("".join(sorted(str(m + int(str(m)[::-1])))))


def A067770_gen():  # generator of terms
    yield from [1, 1]
    c = 1
    for n in count(2):
        c = c * (4 * n - 2) // (n + 1)
        yield c % (n + 2)


def A071837_gen(startvalue=2):  # generator of terms
    for n in count(max(startvalue, 2)):
        fp, fe = zip(*factorint(n).items())
        if sum(fp) == sum(fe) and isprime(sum(fe)) and all([isprime(e) for e in fe]):
            yield n


def A073931_gen(startvalue=1):
    return filter(lambda n: antidivisor_sigma(n) == 2 * n, count(max(startvalue, 1)))


def A076634(n):
    y = Poly(prod(2 * symbolx + i for i in range(1, n + 1))).all_coeffs()[::-1]
    return y.index(max(y))


def A077441(n):
    if n > 0:
        k = 0
        while True:
            m = k
            for i in range(n):
                s = gmpy2digits(m, 4)
                if s == s[::-1]:
                    break
                m += int(s[::-1], 4)
            else:
                s = gmpy2digits(m, 4)
                if s == s[::-1]:
                    return k
            k += 1
    else:
        return 0


def A078266(n):
    s = "".join(str(i) for i in range(1, n + 1))
    return sum(int(d) for d in s) * (10 ** len(s) - 1) // (9 * len(s))


def A083178(n):
    return (
        1
        if n == 1
        else (2 * 10 ** ((n + 2) // 3) + (63 * (n % 3) ** 2 - 129 * (n % 3) - 2)) // 6
    )


def A083289(n):
    a, b = divmod(n, 2)
    c, d = 10**n, 10**a
    if b == 0:
        return nextprime(d) ** 2 - c
    k = 0
    while True:
        fs = factorint(c + k, multiple=True)
        if len(fs) == 2 and min(fs) >= d:
            return k
        k += 1


def A085647_gen(startvalue=2):
    return filter(
        lambda n: len(f := factorint(n)) == 2 == sum(f.values())
        and len(str((s := list(f.keys()))[0])) == len(str(s[1])),
        count(max(startvalue, 2)),
    )


def A087304(n):
    i, p = 2, prod(int(d) for d in str(n) if d != "0")
    while (max(str(i)) == "1" and str(i).count("1") == 1) or prod(
        int(d) for d in str(i * n) if d != "0"
    ) != p:
        i += 1
    return i * n


def A090392(n):
    return n * (n * (n * (n * (n * (n + 45) + 925) + 11475) + 92314) + 413640) // 720


def A090393(n):
    return (
        n
        * (
            n * (n * (n * (n * (n * (n + 63) + 1855) + 34125) + 438424) + 3980172)
            + 20946960
        )
        // 5040
    )


def A090394(n):
    return (
        n
        * (
            n
            * (
                n * (n * (n * (n * (n * (n + 84) + 3346) + 84840) + 1550689) + 21632436)
                + 224782284
            )
            + 1377648720
        )
        // 40320
    )


def A092679_gen(startvalue=0):
    return filter(
        lambda k: antidivisor_count(3 * 2**k) == 1, count(max(startvalue, 0))
    )


def A092680_gen():
    return filter(lambda n: antidivisor_count(n) == 1, (3 * 2**k for k in count(0)))


def A096357(n):
    return lcm(*antidivisors(n, generator=True))


def A097228_gen():
    return chain(
        (27, 38),
        (1000 * (10**k - 1) // 9 + d for k in count(0) for d in (127, 138, 289, 298)),
    )


def A104174(n):
    return (lambda x: x.p % x.q)(harmonic(n))


def A109350_gen(startvalue=3):
    return filter(lambda n: isprime(antidivisor_sigma(n)), count(max(startvalue, 3)))


def A110068_gen(startvalue=1):
    return (
        n
        for n in count(max(startvalue, 1))
        if nextprime(10 ** (n - 1)) - 10 ** (n - 1) == primepi(n)
    )


def A113484(n):
    for k in count(n + 1):
        if gcd(k, n) == 1 and not isprime(k):
            return k


def A116988(n):
    return sum(int(d) for d in str(factorial(10**n)))


def A117057_gen():
    return filter(
        lambda p: "0" not in (s := str(p)) and p % prod(int(d) for d in s) == 0,
        pal10_gen(),
    )


def A349325(n):
    x, c, n2, n3 = n, 1, 2 * n, 3 * n
    while x > 1:
        if x % 2:
            c += int(n3 > 3 * x >= n2)
            x = (3 * x + 1) // 2
        else:
            c += int(n < x < n2)
            x //= 2
    return c


def A350514(n):
    return (
        1
        if n == 0
        else max(
            prod(1 - symbolx ** prime(i) for i in range(1, n + 1)).as_poly().coeffs()
        )
    )


def A117769_gen():  # generator of terms
    a, b = 2, 1
    for i in count(0):
        if prod(int(d) for d in str(b)) in {0, 1, 2, 3, 5, 8, 21, 144}:
            yield b
        a, b = b, a + b


def A117770_gen():  # generator of terms
    yield 0
    a, b = 1, 1
    for i in count(0):
        if prod(int(d) for d in str(b)) in {0, 1, 2, 3, 5, 8, 21, 144}:
            yield b
        a, b = b, a + b


def A350278(n):
    for m in count(1):
        if A349325(m) == n:
            return m


def A350277_gen():  # generator of terms
    c = 0
    for n in count(1):
        m = A349325(n)
        if m > c:
            yield n
            c = m


def A127741_gen():  # generator of terms
    blist, b = [1], 1
    for n in count(1):
        blist = list(accumulate([b] + blist))
        b = blist[-1]
        yield blist[-2] * n


def A128437(n):
    return harmonic(n).p // n


def A132174(n):
    if n == 1:
        return 1
    if n == 2:
        return 5
    h, m = divmod(n - 3, 5)
    return (
        (382 * 2 ** (5 * h + m) - 10 * 2**m) // 31
        - 7 * h
        - m
        - (1 if m == 3 else (-1 if m == 4 else 2))
    )


def A136845_gen():  # generator of terms
    yield from [0, 1]
    for l in count(0):
        for a in ("1", "3", "5", "8"):
            for b in product("01358", repeat=l):
                for c in ("0", "1", "5"):
                    n = int("".join([a] + list(b) + [c]))
                    if set(str(n * n)) <= {"0", "1", "3", "5", "8"}:
                        yield n


def A137146_gen():
    return (
        n
        for n in (
            int("".join(d)) for l in range(1, 6) for d in product("5678", repeat=l)
        )
        if set(str(n**2)) <= set("5678")
    )


def A137401(n):
    ndict = {}
    for i in range(1, n):
        m = pow(i, 3, n)
        if m in ndict:
            ndict[m] += 1
        else:
            ndict[m] = 1
    count = 0
    for i in ndict:
        ni = ndict[i]
        for j in ndict:
            k = (i + j) % n
            if k in ndict:
                count += ni * ndict[j] * ndict[k]
    return count


def A138091_gen():  # generator of terms
    m = [
        6227020800,
        44068147200,
        181142438400,
        564307430400,
        1475073815040,
        3408641107200,
        7182564530400,
        14081919023520,
        26048741640120,
        45924510262992,
        77755456075656,
        127171611204708,
        201851662963039,
        312086923782438,
    ]
    for n in count(1):
        for i in range(13):
            m[i + 1] += m[i]
        if isprime(m[-1]):
            yield n


def A140868(n):
    f = lambda n: n + isqrt(2 * n**2)
    return f(f(n))


def A141263_gen():  # generator of terms
    p = 1
    while True:
        p = nextprime(p)
        ps = int(str(p)[::-1])
        if p <= ps and isprime(ps):
            yield p


@lru_cache(maxsize=None)
def A143443(n):
    if n == 0:
        return 0
    c, j = n, 2
    k1 = n // j
    while k1 > 1:
        j2 = n // k1 + 1
        c += (j2 - j) * A143443(k1) // k1
        j, k1 = j2, n // j2
    return n * (j - c)


def A145643(n):
    return (
        1
        if n <= 1
        else prod(p ** (e % 3) for p, e in factorint(prod(range(n, 0, -2))).items())
    )


def A155148_gen():  # generator of terms
    m = [24, -36, 14, -1, 0]
    for n in count(1):
        for i in range(4):
            m[i + 1] += m[i]
        if len(set(str(m[-1]))) == 2:
            yield n


def A155149_gen(startvalue=1):
    return (n for n in count(max(startvalue, 1)) if len(set(str(n**4))) == 3)


def A156200_gen():
    return (
        int("".join(d))
        for l in count(4)
        for d in product("0689", repeat=l)
        if d[0] != "0" and len(set(d)) == 4 and is_prime(int("".join(d)))
    )


def A157712(n):
    if n == 1:
        return 11
    if n == 2:
        return 0
    p = prime(n)
    l = p
    while True:
        for i in combinations(range(l), l - p):
            s = ["1"] * l
            for x in i:
                s[x] = "0"
            q = int("".join(s))
            if isprime(q):
                return q
        l += 1


def A158214_gen():  # generator of terms
    for i in count(2):
        if i % 6 == 1 or i % 6 == 5:
            i2 = i // 2
            l = i2
            flag = True
            while flag:
                dlist = "0" * (l - i2) + "1" * i2
                for d in multiset_permutations(dlist):
                    s = "".join(d)
                    n = int(s + "1" + s[::-1])
                    if isprime(n):
                        yield n
                        flag = False
                        break
                else:
                    l += 1


def A161502(n):
    s = bin(n)[2:]
    if s == s[::-1]:
        return 0
    for i in range(1, len(s)):
        if s[i:] == s[-1 : i - 1 : -1]:
            return i


def A161721_gen(startvalue=2):
    p = max(nextprime(startvalue - 1), 2)
    while True:
        q = int(str(p)[::-1])
        if is_pal(p * q) and isprime(q):
            yield p
        p = nextprime(p)


def A162555_gen():  # generator of terms
    bset, s = set(), 0
    for i in count(1):
        j, si = 1, str(i)
        while si not in str(s + j) or j in bset:
            j += 1
        yield j
        bset.add(j)
        s += j


@lru_cache(maxsize=None)
def A162943(n):
    if n == 0:
        return 2
    c, j = n, 2
    k1 = n // j
    while k1 > 1:
        j2 = n // k1 + 1
        c += (j2 - j) * (4 - len(bin(A162943(k1))))
        j, k1 = j2, n // j2
    return 2 ** (1 + c - j)


def A163498_gen():
    return (
        prime(n) for n in count(1) if isprime(int(bin(prime(n)).replace("1", "01"), 2))
    )


def A163499_gen():
    return (
        int(bin(prime(n)).replace("1", "01"), 2)
        for n in count(1)
        if isprime(int(bin(prime(n)).replace("1", "01"), 2))
    )


def A173207_gen():  # generator of terms
    a, b = 1, 2
    while True:
        if max(factorint(b).values()) == 2:
            yield b
        a, b = b, a + b


def A175017_gen(startvalue=2):  # generator of terms
    p = max(nextprime(startvalue - 1), 2)
    while True:
        s = str(p)
        if "13" in s and sum(int(d) for d in s) == 13:
            yield p
        p = nextprime(p)


def A175345_gen():  # generator of terms
    (c,) = 1
    for k in count(1):
        if is_square(c):
            yield k
        c += divisor_count(k)


def A180481(n):
    p = prime(n)
    q = nextprime(p)
    while True:
        if (
            isprime(p * (q - p) + q)
            and isprime(p * (q - p) - q)
            and isprime(q * (q - p) + p)
            and isprime(q * (q - p) - p)
        ):
            return q
        n += 1
        q = nextprime(q)


def A180484_gen():
    return (
        int(n)
        for n in (str(x) for x in count(1))
        if not (n.count("0") or int(n) ** 2 * len(n) % prod(int(d) for d in n) ** 2)
    )


def A181373(n):
    s, p, l = "", prime(n), 0
    for m in count(1):
        u = str(m)
        s += u
        l += len(u)
        t = s
        if not int(t) % p:
            for i in range(l - 1):
                t = t[1:] + t[0]
                if int(t) % p:
                    break
            else:
                return m


def A186774(n):
    if sum(int(d) for d in str(n)) == 1:
        return 0
    sn, k = str(n + 1), 1
    while sn not in str(k):
        k *= n
    return k


def A187394(n):
    return 4 * n - 1 - isqrt(8 * n**2)


def A188061_gen(startvalue=1):
    return (
        n
        for n in count(max(startvalue, 1))
        if pow(
            isqrt(n) if is_square(n) else n,
            int(divisor_sigma(n, 0)) // (1 if is_square(n) else 2),
            int(divisor_sigma(n, 1)),
        )
        == 1
    )


def A188082(n):
    return isqrt(3 * (n + 1) ** 2) - isqrt(3 * n**2) - 1


def A192273_gen(startvalue=3):  # generator of terms
    for n in count(max(startvalue, 3)):
        d = antidivisors(n)
        s = sum(d)
        if not s % 2 and max(d) <= s // 2:
            for x in range(1, 2 ** len(d)):
                if sum(Subset.unrank_binary(x, d).subset) == s // 2:
                    yield n
                    break


def A194152(n):
    return 5 * n + isqrt(20 * n**2)


def A198244_gen():  # generator of terms
    m = [
        3628800,
        -15966720,
        28828800,
        -27442800,
        14707440,
        -4379760,
        665808,
        -42240,
        682,
        0,
        1,
    ]
    for n in count(1):
        for i in range(10):
            m[i + 1] += m[i]
        if not isprime(n) and isprime(m[-1]):
            yield m[-1]


def A199303_gen():
    return (
        n
        for n in (
            int(t + "".join(s))
            for l in count(0)
            for t in "13"
            for s in product("013", repeat=l)
        )
        if isprime(n) and isprime(int(str(n)[::-1]))
    )


def A199328_gen():
    return (
        n
        for n in (
            int(t + "".join(s))
            for l in count(0)
            for t in "18"
            for s in product("018", repeat=l)
        )
        if isprime(n) and isprime(int(str(n)[::-1]))
    )


def A199302_gen():
    return (
        n
        for n in (
            int(t + "".join(s))
            for l in count(0)
            for t in "12"
            for s in product("012", repeat=l)
        )
        if isprime(n) and isprime(int(str(n)[::-1]))
    )


def A349862(n):
    return max(comb(n - 2 * k, k) for k in range(n // 3 + 1))


def A210698(n):
    if n % 3 == 0:
        return 11 * n**4 // 27
    elif n % 3 == 1:
        return (11 * n**4 - 8 * n**3 + 6 * n**2 + 4 * n + 14) // 27
    else:
        return (11 * n**4 - 16 * n**3 + 24 * n**2 + 32 * n + 8) // 27


def A211071(n):
    if n % 3 == 0:
        return 8 * n**4 // 27
    elif n % 3 == 1:
        return (8 * n**4 + 4 * n**3 - 3 * n**2 - 2 * n - 7) // 27
    else:
        return (8 * n**4 + 8 * n**3 - 12 * n**2 - 16 * n - 4) // 27


def A213239_gen(startvalue=1):
    return (
        n
        for n in count(max(startvalue, 1))
        if sum(
            sum(int(x) for x in str(d))
            for d in range(2, n)
            if n % d and 2 * n % d in [d - 1, 0, 1]
        )
        == sum(int(x) for x in str(n))
    )


def A350473(n):
    return fibonacci(n + 1) ** 3 - fibonacci(n - 1) ** 3


def A214648_gen():  # generator of terms
    s, c, d = 0, 0, -1
    while True:
        k = 2
        q = 4 * (k * (k * (k + c) + d)) // 3 + 1
        while not is_square(q):
            k += 1
            q = 4 * (k * (k * (k + c) + d)) // 3 + 1
        yield k
        s += k
        c, d = 3 * s, 3 * s**2 - 1


def A214697(n):
    k, a1, a2, m = 2, 36 * n, 36 * n**2 - 12, n * (72 * n + 144) + 81
    while int(round(sqrt(m))) ** 2 != m:
        k += 1
        m = k * (k * (12 * k + a1) + a2) + 9
    return k


def A216394(n):
    if n == 1:
        return 1
    c = 0
    for i in range(2 ** (n - 1) + 1, 2**n):
        s1, s2 = sorted(str(i)), sorted(str(totient(i)))
        if len(s1) == len(s2) and s1 == s2:
            c += 1
    return c


def A217175(n):
    if n == 1:
        return 0
    else:
        l, y, x = [str(d) * n for d in range(10)], 0, 1
        for m in count(1):
            s = str(x)
            for k in range(10):
                if l[k] in s:
                    return k
            y, x = x, y + x


def A217176(n):
    if n == 1:
        return 2
    else:
        l, y, x = [str(d) * n for d in range(10)], 2, 1
        for m in count(1):
            s = str(x)
            for k in range(10):
                if l[k] in s:
                    return k
            y, x = x, y + x


def A218035(n):
    return (
        4
        if n == 1
        else (n**3 - 9 * n**2 + 59 * n - 3) // 24
        if n % 2
        else (n**3 - 6 * n**2 + 32 * n + 48) // 48
    )


def A343098(n):
    return (
        1
        if n == 0
        else (
            n * (n * (n * (6 * n - 52) + 510) + 904)
            + 1491
            + (-1 if n % 2 else 1) * (n * (n * (42 - 4 * n) - 296) + 45)
        )
        // 768
    )


def A224252_gen(startvalue=1):
    return (
        n
        for n in count(max(startvalue, 1))
        if n != int(str(n)[::-1])
        and primefactors(n) == primefactors(int(str(n)[::-1]))
        and sorted(factorint(n).values())
        == sorted(factorint(int(str(n)[::-1])).values())
    )


def A253631_gen():
    return filter(
        lambda n: isprime(n) and is_pal(n**2), (int(bin(m)[2:]) for m in pal_gen(b=2))
    )


def A227491(n):
    return (
        2**n * (2**n * (526338 * n**2 - 2685555 * n + 4790367) - 5719932) // 8
        + 116340
    )


def A229134_gen():  # generator of terms
    for i in count(0):
        m, m2, j, k = 2, 4, 4 * i**2 + 1, 2 * i**2
        while k >= m2 + m:
            if is_square(j - m2):
                yield i**2
                break
            m2 += 2 * m + 1
            m += 1


def A229972_gen(startvalue=1):
    return (
        i
        for i in count(max(startvalue, 1))
        if not isprime(i) and (integer_nthroot(i, 3)[1] or divisor_count(i) % 3 == 2)
    )


def A236359_gen(startvalue=1):  # generator of terms
    for n in count(max(startvalue, 1)):
        d = divisors(n)
        d.pop()
        ld = len(d)
        if sum(d) >= n:
            s, j = d[0], 1
            for i in range(ld - 1):
                while s < n and j < ld:
                    s += d[j]
                    j += 1
                if s == n:
                    yield n
                    break
                j -= 1
                s -= d[i] + d[j]


def A236513(n):
    l, k, c = n - 1, 2**n, 0
    while True:
        for d in combinations(range(l - 1, -1, -1), l - n + 1):
            m = k - 1 - sum(2 ** (e) for e in d)
            if isprime(m):
                c += 1
                if c == n:
                    return m
        l += 1
        k *= 2


def A240924_gen():
    return (1 + (n * n - 1) % 9 for n in count(1, 2) if n % 3 and n % 5)


def A240983_gen():
    (2**p * p * p for p in (prime(n) for n in count(1)) if isprime(p + 2))


def A241989_gen(startvalue=1):
    return (
        n
        for n in count(max(startvalue, 1))
        if not n % sum(int(d, 16) for d in hex(n)[2:])
    )


def A242018_gen():  # generator of terms
    blist = [0, 0, 1]
    yield from blist
    while True:
        x = blist[len(blist) // 2 :]
        yield from x
        blist += x


def A242107_gen():  # generator of terms
    blist = [0, 1, 1, 1, 1, -1]
    yield from blist
    for n in count(6):
        blist = blist[1:] + [
            (-blist[-1] * blist[-4] + blist[-2] * blist[-3]) // blist[-5]
        ]
        yield blist[-1]


def A242108_gen():
    return (abs(n) for n in A242107_gen())


def A243102_gen(startvalue=1):
    return (
        int(n)
        for n in (str(x) for x in count(max(startvalue, 1)))
        if not n.count("0")
        and sorted(str(int(n) + prod(int(d) for d in n))) == sorted(n)
    )


def A243318_gen():  # generator of terms
    m = [
        3628800,
        -16692480,
        31651200,
        -31827600,
        18163440,
        -5826240,
        971232,
        -69720,
        1362,
        -2,
        -1,
    ]
    for n in count(1):
        for i in range(10):
            m[i + 1] += m[i]
        if isprime(m[-1]):
            yield n


def A244423_gen():
    return filter(
        lambda p: not isprime(p) and is_pal(divisor_prod(p)), islice(pal_gen(), 1, None)
    )


def A244428_gen(startvalue=1):
    return (
        i
        for i in count(max(startvalue, 1))
        if (integer_nthroot(i, 3)[1] or not divisor_sigma(i, 0) % 3)
        and integer_nthroot(int(divisor_sigma(i, 1)), 3)[1]
    )


def A007955(n):
    return divisor_prod(n)


def A244466_gen(startvalue=1):
    return (
        n
        for n in count(max(startvalue, 1))
        if n == 1
        or (
            not isprime(n)
            and max(factorint(totient(n)).values()) < 2
            and (-1) ** len(primefactors(totient(n))) == 1
        )
    )


def A244551_gen():  # generator of terms
    for p in pal_gen():
        l = len(str(p))
        for i in range(1, l * 9 + 1):
            n = p - i
            if n > 0:
                if sum((int(d) for d in str(n))) == i:
                    s = str(n - i)
                    if s == s[::-1]:
                        yield n


def A244915_gen():  # generator of terms
    yield 1
    bset, c = set(), 1
    while True:
        a, b = 1, 1 + c**2
        while not isprime(b) or b in bset:
            b += 2 * a + 1
            a += 1
        bset.add(b)
        yield a
        c = a


def A244959(n):
    if n > 0:
        for i in range(1, 2**n):
            x = int(bin(i)[2:], 8)
            if not x % n:
                return x
    return 0


def A245042_gen():
    return filter(
        isprime, ((k**2 + 4) // 5 for k in count(0) if (k**2 + 4) % 5 == 0)
    )


def A245045_gen():
    return filter(
        isprime, ((k**2 + 2) // 6 for k in count(0) if (k**2 + 2) % 6 == 0)
    )


def A245085(n):
    p, f, fv = prime(n), 1, {}
    for i in range(2, p):
        f = (f * i) % p
        if f in fv:
            return i - 1
        else:
            fv[f] = i
    return p - 1


def A245644_gen(startvalue=1):
    return (
        n
        for n in count(max(startvalue, 1))
        if not sum(divisors(n**3)) % divisor_count(n**3)
    )


def A245763_gen():
    return (
        int(n)
        for n in (str(prime(x)) for x in count(1))
        if isprime(int(str(sum(int(d) for d in n)) + n))
        and isprime(int(n + str(sum(int(d) for d in n))))
    )


def A245909(n):
    return len(primefactors(prime(n) ** 3 - 1))


def A246135_gen():  # generator of terms
    blist = []
    for n in range(1, 9):
        for m in range(n - 1, -1, -1):
            l = "".join(str(d) for d in range(n, m - 1, -1))
            p = int(l + l[-2::-1], 9)
            if isprime(p):
                blist.append(p)
        for m in range(n + 1, 9):
            l = "".join(str(d) for d in range(n, m + 1))
            p = int(l + l[-2::-1], 9)
            if isprime(p):
                blist.append(p)
    yield from sorted(blist)


def A246136_gen():  # generator of terms
    blist = []
    for n in range(1, 8):
        for m in range(n - 1, -1, -1):
            l = "".join(str(d) for d in range(n, m - 1, -1))
            p = int(l + l[-2::-1], 8)
            if isprime(p):
                blist.append(p)
        for m in range(n + 1, 8):
            l = "".join(str(d) for d in range(n, m + 1))
            p = int(l + l[-2::-1], 8)
            if isprime(p):
                blist.append(p)
    yield from sorted(blist)


def A246337_gen():
    return (
        n
        for n, s in ((n, hex(n)[2:]) for n in islice(pal_gen(16), 1, None))
        if "0" not in s
        and not ((n % sum(int(d, 16) for d in s)) or (n % prod(int(d, 16) for d in s)))
    )


def A246338_gen():
    return (
        n
        for n, s in ((n, oct(n)[2:]) for n in islice(pal_gen(8), 1, None))
        if "0" not in s
        and not ((n % sum(int(d, 8) for d in s)) or (n % prod(int(d, 8) for d in s)))
    )


def A246601(n):
    return sum(d for d in divisors(n, generator=True) if n | d == n)


def A246701(n):
    return max(
        int(bin(n + 1 - k)[2:] + bin(n + 1 + k)[2:], 2) for k in range(n + 2)
    ) - max(int(bin(n - k)[2:] + bin(n + k)[2:], 2) for k in range(n + 1))


def A092517(n):
    return divisor_count(n) * divisor_count(n + 1)


def A246817_gen():  # generator of terms
    p5 = 0
    for n in count(5, 5):
        yield p5
        p5 += multiplicity(5, n) * n


def A246874_gen():
    return (
        p
        for p in (prime(n) for n in count(1))
        if all(isprime(p - m * m) for m in range(2, 10, 2))
    )


def A246971_gen():  # generator of terms
    for n in count(0):
        for k in range(n, -1, -1):
            c, d0 = 0, ["0"] * (n + k)
            for x in combinations(range(n + k), n):
                d = list(d0)
                for i in x:
                    d[i] = "1"
                if not "0100010" in "".join(d):
                    c += 1
            yield c


def A247128_gen(startvalue=1):
    return (n for n in count(max(startvalue, 1)) if (n % 22) in {0, 5, 9, 13, 17})


def A247221_gen(startvalue=0):
    return (
        n for n in count(max(startvalue, 0)) if pow(2, n, 2 * n * n + 1) == 2 * n * n
    )


def A247348_gen():
    return (
        p
        for p in (5 * prime(n) + 4 for n in count(1))
        if not ((p - 1) % 2 or (p - 2) % 3 or (p - 3) % 4)
        and isprime(p)
        and isprime((p - 1) // 2)
        and isprime((p - 2) // 3)
        and isprime((p - 3) // 4)
    )


def A247855(n):
    return hermite(10, n)


def A247850(n):
    return hermite(5, n)


def A247854(n):
    return hermite(9, n)


def A247853(n):
    return hermite(8, n)


def A247852(n):
    return hermite(7, n)


def A247851(n):
    return hermite(6, n)


def A163323(n):
    return hermite(4, n)


def A163322(n):
    return hermite(3, n)


def A348634(n):
    return (
        n
        * (n - 2)
        * (n - 1)
        * (
            n * (n * (n * (n * (n * (n * (n - 17) + 167) - 965) + 3481) - 7581) + 9060)
            - 4608
        )
        // 120
    )


def A248323_gen(startvalue=1):
    return (
        n
        for n in count(max(startvalue, 1))
        if len(
            list(
                re.finditer(
                    "(?=" + str(n) + ")", "".join([str(d) for d in divisors(n)])
                )
            )
        )
        > 1
    )


def A248889_gen():
    return (n for n in pal10_gen() if is_pal(n, 18))


def A249517_gen():  # generator of terms
    yield 0
    for g in count(1):
        xp, ylist = [], []
        for i in range(9 * g, -1, -1):
            x = set(str(i))
            if not (("0" in x) or (x in xp)):
                xv = [int(d) for d in x]
                imin = int("".join(sorted(str(i))))
                if max(xv) * (g - len(x)) >= imin - sum(xv) and i - sum(xv) >= min(
                    xv
                ) * (g - len(x)):
                    xp.append(x)
                    for y in product(x, repeat=g):
                        if set(y) == x:
                            yd = [int(d) for d in y]
                            if set(str(sum(yd))) == x == set(str(prod(yd))):
                                ylist.append(int("".join(y)))
        yield from sorted(ylist)


def A249689_gen():  # generator of terms
    l1, l2, s, b = 2, 1, 3, set()
    for n in count(3):
        i = s
        while True:
            if not i in b and gcd(i, l1) == 1 and gcd(i, l2) == 1:
                l2, l1 = l1, i
                b.add(i)
                if l2 > l1 and n % 3 == 1:
                    yield (n - 1) // 3
                while s in b:
                    b.remove(s)
                    s += 1
                break
            i += 1


def A249780(n):
    return max(p := primefactors(2**n - 1)) * min(p)


def A249951_gen():  # generator of terms
    m = [362880, -1229760, 1607760, -1011480, 309816, -40752, 1584, -4, 1]
    for n in count(1):
        for i in range(8):
            m[i + 1] += m[i]
        if isprime(m[-1]):
            yield n


def A250127_gen():  # generator of terms
    yield 1
    l1, l2, s, u, l, b = 3, 2, 4, 1, 1, {}
    for n in count(4):
        i = s
        while True:
            if not i in b and gcd(i, l1) == 1 and gcd(i, l2) > 1:
                l2, l1, b[i] = l1, i, 1
                while s in b:
                    b.pop(s)
                    s += 1
                if u * n < i * l:
                    yield n
                    u, l = i, n
                break
            i += 1


def A250984_gen():  # generator of terms
    m = -1
    for i in count(3):
        if (v := A247190(i)) > m:
            yield v
            m = v


def A250985_gen():  # generator of terms
    m = -1
    for i in count(3):
        if (v := A247190(i)) > m:
            yield i
            m = v


def A251360_gen():  # generator of terms
    p = 3
    for n in count(2):
        q, fn = prime(n + 1), factorint(n)
        m = int("".join(str(d) * fn[d] for d in sorted(fn)))
        if p <= m < q:
            yield m
        p = q


def A251756_gen():  # generator of terms
    yield 0
    l, s, b = 0, 1, {}
    while True:
        i = s
        while True:
            if not i in b:
                m = gcd(i, l)
                if not (m == 1 or isprime(m)):
                    yield i
                    l, b[i] = i, True
                    while s in b:
                        b.pop(s)
                        s += 1
                    break
            i += 1


def A252606_gen(startvalue=0):
    return (n for n in count(max(startvalue, 0)) if pow(2, n, n + 2) == n)


def A253047(n):
    if n <= 2:
        return n
    if n == 3:
        return 7
    q2, r2 = divmod(n, 2)
    if r2:
        q3, r3 = divmod(n, 3)
        if r3:
            if isprime(n):
                m = primepi(n)
                if isprime(m):
                    return prime(2 * m)
                x, y = divmod(m, 2)
                if not y:
                    if isprime(x):
                        return prime(x)
            return n
        if isprime(q3):
            return 2 * prevprime(q3)
        return n
    if isprime(q2):
        return 3 * nextprime(q2)
    return n


def A253084_T(n, k):
    return int(not (~(n + k) & (n - k)) | (~n & k))


def A253264_gen():  # generator of terms
    p = 2
    while True:
        q = p**2 - 2
        if isprime(q):
            r = q**2 - 2
            if isprime(r):
                s = r**2 - 2
                if isprime(s) and isprime(s**2 - 2):
                    yield p
        p = nextprime(p)


def A253576_gen(startvalue=1):
    return (
        n
        for n in count(max(startvalue, 1))
        if set(str(n)) & set(str(n**7)) == set() and isprime(n)
    )


def A253577_gen(startvalue=1):
    return (
        n
        for n in count(max(startvalue, 1))
        if set(str(n)) & set(str(n**8)) == set() and isprime(n)
    )


def A253606_gen(startvalue=1):
    return (
        n for n in count(max(startvalue, 1)) if set(str(n)) & set(str(n**8)) == set()
    )


def A254232_gen():  # generator of terms
    yield 2
    a, b, c, d = 3, 0, 2, 2
    while True:
        a, b, c = b, c, a + b
        d *= c
        yield d


def A254687(n):
    y, x, n2 = 0, 2, 2 * n
    while x < n:
        if isprime(n2 - x) and isprime(n2 - 2 * x - 1):
            y += 1
        x = nextprime(x)
    return y


def A254688(n):
    y, x, n2 = 0, 2, 2 * n
    while x < n:
        if isprime(n2 - x) and isprime(n2 - 2 * x + 1):
            y += 1
        x = nextprime(x)
    return y


def A255132_gen():  # generator of terms
    yield from [1, 1]
    c, s = {}, 3
    for n in count(2):
        for p, e in factorint(4 * n - 2).items():
            if p in c:
                c[p] += e
            else:
                c[p] = e
        for p, e in factorint(n + 1).items():
            if c[p] == e:
                del c[p]
            else:
                c[p] -= e
        if n == s:
            c2 = prod(e + 1 for e in c.values())
            yield c2
            s = 2 * s + 1


def A255133_gen():  # generator of terms
    yield from [1, 1]
    c, s = {}, 3
    for n in count(2):
        for p, e in factorint(4 * n - 2).items():
            if p in c:
                c[p] += e
            else:
                c[p] = e
        for p, e in factorint(n + 1).items():
            if c[p] == e:
                del c[p]
            else:
                c[p] -= e
        if n == s:
            c2 = 2 ** len(c)
            yield c2
            s = 2 * s + 1


def A255194_gen():  # generator of terms
    p, p2 = 2, 3
    for n in count(1):
        if p2 - p > 6:
            for i in range(1, 7):
                fs = factorint(p + i)
                if len(fs) > 3 or sum(list(fs.values())) != 3:
                    break
            else:
                yield n
        p, p2 = p2, nextprime(p2)


def A255244_gen():  # generator of terms
    for n in count(1):
        s0 = s2 = 1
        for p, e in factorint(n).items():
            s0 *= e + 1
            s2 *= (p ** (2 * (e + 1)) - 1) // (p**2 - 1)
        q, r = divmod(s2, s0)
        if not (r or q % n):
            yield n


def A255245_gen():  # generator of terms
    for n in count(2):
        s0 = s2 = 1
        for p, e in factorint(n).items():
            s0 *= e + 1
            s2 *= (p ** (2 * (e + 1)) - 1) // (p**2 - 1)
        q, r = divmod(s2 - n**2, s0 - 1)
        if not (r or q % n):
            yield n


def A255484(n):
    return prod(0 if ~n & k else prime(k + 1) for k in range(n + 1))


def A256048(n):
    sn = str(n)
    for p in pal10_odd_range_gen(len(sn) + 2):
        if sn in str(p)[1:-1] and isprime(p):
            return p


def A256112_helper(n, b):
    if n == 1:
        t = list(range(b))
        for i in range(1, b):
            u = list(t)
            u.remove(i)
            yield i, u
    else:
        for d, v in A256112_helper(n - 1, b):
            for g in v:
                k = d * b + g
                if not k % n:
                    u = list(v)
                    u.remove(g)
                    yield k, u


def A256112_gen():
    return (a * k + b[0] for k in count(2) for a, b in A256112_helper(k - 1, k))


def A256480(n):
    sn = str(n)
    if not (n % 2 and n % 5):
        return 0
    for i in count(1):
        for j in range(1, 10):
            si = gmpy2digits(j, 10) * i
            p = int(si + sn)
            if isprime(p):
                return p


def A256635(n):
    k = 1
    while sum(int(d) for d in str(divisor_sigma(k))) != n:
        k += 1
    return k


def A257299_gen():  # generator of terms
    blist = []
    for n in permutations("123456789", 9):
        x = 0
        for d in n:
            q, r = divmod(x, int(d))
            if r:
                break
            x = int(d + str(q))
        else:
            blist.append(x)
    yield from sorted(blist)


def A257864_gen():  # generator of terms
    g, h = 105, 128
    for i in count(9, 2):
        g *= i
        if isprime(g - h):
            yield i


def A257342(n):
    m, y, t, = (
        2,
        Fraction(0, 1),
        10 ** (n + 1),
    )
    for i in count(2):
        for j in range(1, i):
            x = Fraction(j, i)
            if x.denominator == i:
                y += Fraction(int(m * x) % 2, m)
                m *= 2
        if m > 10000 * t:
            break
    return int(y * t) % 10


def A258574_gen():  # generator of terms
    a, b = 0, 2
    for n in count(0):
        if max(factorint(b).values()) <= 1:
            yield n
        a, b = b, a + b


def A258660_gen():  # generator of terms
    for l in count(1):
        if not isprime(l):
            fs = divisors(l)
            a, b = isqrt_rem(10 ** (l - 1))
            if b > 0:
                a += 1
            for n in range(a, isqrt(10**l - 1) + 1):
                n2 = n**2
                ns = str(n2)
                for g in fs:
                    y = 0
                    for h in range(0, l, g):
                        y += int(ns[h : h + g])
                    if not is_square(y):
                        break
                else:
                    yield n2


def A350329(n):
    a, b, c = 2**n, n * (n + 1), 2 ** (n + 1)
    while (x := divmod(c - a, b))[1] != 0:
        c *= 2
    return x[0]


def A350576(n):
    return n // (m := A055874(n)) - m


def A350509(n):
    return n // A055874(n)


def A259629_gen():  # generator of terms
    plist, p = [10, 15], 5
    yield from plist
    while True:
        r = nextprime(p)
        plist = [plist[-1] * 2 * r // p] + [d * r for d in plist]
        p = r
        yield from plist


def A259673(n):
    return divisor_sigma(n, prime(n))


def A259836_gen(startvalue=0):  # generator of terms
    for n in count(max(startvalue, 0)):
        m = n**3 + (n + 1) ** 3
        for x in divisors(m):
            x2 = x**2
            if x2 > m:
                break
            if x != (2 * n + 1) and m < x * x2 and is_square(12 * m // x - 3 * x2):
                yield n
                break


def A259877_gen():  # generator of terms
    yield 1
    a = 1
    for n in count(2):
        a = 6 * a // (n - 1) if n % 2 else a * n * (n + 1) // 6
        yield a


def A259981(n):
    b, c = A002808(n), 0
    for x in range(1, b):
        for y in range(1, b):
            if x != y:
                w = b * (x - y)
                for z in range(1, b):
                    if x != z:
                        if z * w == y * (x - z):
                            c += 1
    return c


def A260224_gen():
    return (
        int("".join(x))
        for n in count(1)
        for x in product("135", repeat=n)
        if is_prime(mpz("".join(x)))
    )


def A260351(n):  # assume 0 <= n <= 62
    r, c = set(gmpy2digits(d, n) for d in range(n)), 0
    dc = set(gmpy2digits(c, n))
    while len(dc) < n - 1 or "0" in dc:
        c += max(int(d, n) for d in r - dc)
        dc = set(gmpy2digits(c, n))
    return c


def A260374_gen():  # generator of terms
    yield 0
    g = 1
    for i in count(1):
        g *= i
        s = isqrt(g)
        t = g - s**2
        yield int(t if t - s <= 0 else 2 * s + 1 - t)


def A261010(n):
    return sum(int(d) for d in gmpy2digits(5**n, 3))


def A261182_gen():
    return (
        int("".join(d))
        for l in count(1)
        for d in product("279", repeat=l)
        if isprime(int("".join(d)))
    )


def A262963_helperf1(n):
    s = gmpy2digits(n, 3)
    m = len(s)
    for i in range(m):
        if s[i] == "0":
            return int(s[:i] + "1" * (m - i), 3)
    return n


def A262963_helperf2(n):
    s = gmpy2digits(n, 4)
    m = len(s)
    for i in range(m):
        if s[i] in ["0", "1"]:
            return int(s[:i] + "2" * (m - i), 4)
    return n


def A262963_gen():  # generator of terms
    n = 1
    while True:
        m = A262963_helperf2(A262963_helperf1(n))
        while m != n:
            n, m = m, A262963_helperf2(A262963_helperf1(m))
        yield m
        n += 1


def A263133_gen(startvalue=0):
    return (m for m in count(max(startvalue, 0)) if not ~(4 * m + 3) & m)


def A263299_gen():
    return (
        n
        for n in (int("1" * k + str(k * (k + 1) + 1) + "1" * k) for k in count(0))
        if isprime(n)
    )


def A265433(n):
    if n == 1:
        return 0
    if n == 3:
        return 1
    if (n % 3) == 0:
        return 0
    else:
        pmaxlist = (
            ["3" * (n // 3) + "2"]
            if (n % 3 == 2)
            else ["3" * (n // 3 - 1) + "22", "3" * (n // 3 - 1) + "4"]
        )
        return sum(
            1
            for p in pmaxlist
            for k in multiset_permutations(p)
            if isprime(int("".join(k)))
        )


def A267077(n):
    if n == 0:
        return 1
    u, v, t, w = max(8, 2 * n), max(4, n) ** 2 - 9, 4 * n * (n + 1), n**2
    while True:
        m, r = divmod(v, t)
        if not r and is_square(m * w + 1):
            return m
        v += u + 1
        u += 2


def A267765_gen():
    return (int(d, 5) for d in (str(i**2) for i in count(0)) if max(d) < "5")


def A267766_gen():
    return (int(d, 6) for d in (str(i**2) for i in count(0)) if max(d) < "6")


def A267819_gen():
    return (
        int(d, 5)
        for d in (str(i**2) for i in count(1))
        if max(d) < "5" and isprime(int(d, 5))
    )


def A267820_gen():
    return (
        int(d, 6)
        for d in (str(i**2) for i in count(1))
        if max(d) < "6" and isprime(int(d, 6))
    )


def A268083_gen():  # generator of terms
    b = 1
    for n in count(1):
        if len(factorint(n)) > 1 and gcd(b, n) == 1:
            yield n
        b = b * 2 * (2 * n + 1) // (n + 1)


def A268983_gen(startvalue=1):
    return (
        n
        for n in count(max(startvalue, 1))
        if not sum(
            d * pow(int(divisor_sigma(d)), n // d, n) % n
            for d in divisors(n, generator=True)
        )
        % n
    )


def A269483(n):
    return (
        n
        * (
            n**2
            * (n * (n**2 * (n**2 * (n * (n**2 * (n - 1) + 1) - 1) + 1) - 1) + 1)
            - 1
        )
        + 1
    )


def A269483_gen():  # generator of terms
    m = [
        479001600,
        -2674425600,
        6386688000,
        -8501915520,
        6889478400,
        -3482100720,
        1080164160,
        -194177280,
        17948256,
        -666714,
        5418,
        0,
        1,
    ]
    while True:
        yield m[-1]
        for i in range(12):
            m[i + 1] += m[i]


def A270225_gen():
    return (
        p
        for p in (prime(i) for i in count(2))
        if p % 8 not in {5, 7} and isprime(p + 2)
    )


def A270808_gen():  # generator of terms
    a = 1
    while True:
        b = a // (max(primefactors(a) + [1])) + 1
        yield b // 2
        a += b


if sys.version_info >= (3, 10):

    def A271499_gen(startvalue=1):
        return (n for n in count(max(startvalue, 1)) if n.bit_count().bit_count() != 1)

else:

    def A271499_gen(startvalue=1):
        return (
            n
            for n in count(max(startvalue, 1))
            if bin(bin(n).count("1")).count("1") != 1
        )


def A272328(n):
    m = totient(n)
    return sum(1 for k in range(1, n + 1) if m == totient(n + k))


def A274093_gen():
    return chain((0,), (i for n in count(1) for i in (-n if n % 2 else n,) * n))


def A274094_gen():
    return chain((0,), (i for n in count(1) for i in (n if n % 2 else -n,) * n))


def A274213_gen():  # generator of terms
    blist = [1, 2, 3]
    yield from blist
    while True:
        blist.append(blist[-blist[-3]] + 3)
        yield blist[-1]


def A275573_gen():  # generator of terms
    q = 0
    for i in count(1):
        q += Fraction(int(str(i)[::-1]), 10 ** len(str(i)))
        if q.denominator == 1:
            yield q + i * (i + 1) // 2


def A276399(n):
    a = factorial(n - 1)
    return a // gcd(n ** (n - 1) - 1, a)


def A276400(n):
    a = n ** (n - 1) - 1
    return a // gcd(factorial(n - 1), a)


def A276689(n):
    x = continued_fraction_periodic(0, 1, n)
    return min(x[1]) if len(x) > 1 else 0


def A276919(n):
    ndict = {}
    for i in range(n):
        i3 = pow(i, 3, n)
        for j in range(i + 1):
            j3 = pow(j, 3, n)
            m = (i3 + j3) % n
            if m in ndict:
                if i == j:
                    ndict[m] += 1
                else:
                    ndict[m] += 2
            else:
                if i == j:
                    ndict[m] = 1
                else:
                    ndict[m] = 2
    count = 0
    for i in ndict:
        j = (1 - i) % n
        if j in ndict:
            count += ndict[i] * ndict[j]
    return count


def A276920(n):
    ndict = {}
    for i in range(n):
        i3 = pow(i, 3, n)
        for j in range(i + 1):
            j3 = pow(j, 3, n)
            m = (i3 + j3) % n
            if m in ndict:
                if i == j:
                    ndict[m] += 1
                else:
                    ndict[m] += 2
            else:
                if i == j:
                    ndict[m] = 1
                else:
                    ndict[m] = 2
    count = 0
    for i in ndict:
        j = (-i) % n
        if j in ndict:
            count += ndict[i] * ndict[j]
    return count


def A277285_gen():
    return chain(
        (1,),
        (
            j
            for j in (i**2 for i in count(1))
            if pow(2, j, int(divisor_count(j))) == 1
        ),
    )


def A277685(n):  # output differs from sequence at n=14 due to multiple spellings.
    return ord(unidecode.unidecode(num2words(n, lang="pt")).lower()[0]) - 96


def A281363(n):
    m, q = 1, 4 * n**2 - 1
    p = pow(2, 2 * n, q)
    r = p
    while r != 1:
        m += 1
        r = (r * p) % q
    return m


def A282384_gen(startvalue=1):
    return (i for i in count(max(startvalue, 1)) if str(i + 1) in str(i**2))


def A286261_gen(startvalue=0):
    return (n for n in count(max(startvalue, 0)) if not is_cubefree_string(bin(n)[2:]))


def A286298(n):
    if n <= 1:
        return n
    a, b = divmod(n, 2)
    return A286298(a) + 1 + b + (-1) ** b * (a % 2)


def A286333_gen():  # generator of terms
    for l in count(0):
        for w in product("1379", repeat=l):
            for d in "0123456789":
                for t in "1379":
                    s = "".join(w) + d + t
                    n = int(s)
                    for i in range(l + 1):
                        if not isprime(int(s)):
                            break
                        s = s[1:] + s[0]
                    else:
                        if n > 10 and not isprime(int(s)):
                            yield n


def A286901(n):
    m = prevprime(n)
    return (m + n) * (n - m + 1) // 2


def A287550_gen():  # generator of terms
    p = 2
    q, r, s = p + 72, p + 144, p + 216
    while True:
        np = nextprime(p)
        if (
            np == q
            and isprime(r)
            and isprime(s)
            and nextprime(q) == r
            and nextprime(r) == s
        ):
            yield p
        p, q, r, s = np, np + 72, np + 144, np + 216


def A288184(n):
    d = 1
    while True:
        s = continued_fraction_periodic(0, 1, d)[-1]
        if isinstance(s, list) and len(s) == n:
            return d
        d += 2


def A288185(n):
    d = 2
    while True:
        s = continued_fraction_periodic(0, 1, d)[-1]
        if isinstance(s, list) and len(s) == n:
            return d
        d += 2


def A288939_gen(startvalue=0):
    return (
        n
        for n in count(max(startvalue, 0))
        if not isprime(n)
        and isprime(n * (n * (n * (n * (n * (n + 1) + 1) + 1) + 1) + 1) + 1)
    )


def A289660(n):
    return (
        0
        if n == 1
        else int("".join(map(lambda x: str(x[0]) * x[1], sorted(factorint(n).items()))))
        - n
    )


def A290126(n):
    i = 1
    while len(divisors(i)) < n or not isprime(sum(divisors(i)[-n:])):
        i += 1
    return i


def A290435_gen(startvalue=2):
    return (
        n
        for n in count(max(startvalue, 2))
        if sum(factorint(n).values()) == len(factorint(n)) == 2
        and isprime(1 + sum(factorint(n).keys()))
    )


def A291460_gen(startvalue=1):
    return (
        2 * x
        for x in count(max(startvalue // 2 + startvalue % 2, 1))
        if str(int(bin(x).rstrip("0"), 2)) in str(2 * x)
    )


def A292931_gen(startvalue=0):
    return (
        n for n in count(max(startvalue, 0)) if not sum(int(d) for d in str(3**n)) % 7
    )


def A296012_gen():  # generator of terms
    p = 2
    while True:
        k = (p - 2) // 3
        if not (isprime(k) or isprime(k + 2)):
            yield p
        p = nextprime(p)


def A297574(n):
    m = n + 1
    mn = m * n
    while pow(2, m, mn) != pow(2, n, mn):
        m += 1
        mn += n
    return m


def A033307_gen():
    return chain.from_iterable(sympydigits(m, 10)[1:] for m in count(1))


def A031076_gen():
    return chain.from_iterable(sympydigits(m, 9)[1:] for m in count(1))


def A054634_gen():
    return chain.from_iterable(sympydigits(m, 8)[1:] for m in count(0))


def A031035_gen():
    return (d for m in count(1) for d in sympydigits(m, 8)[1:])


def A030998_gen():
    return chain.from_iterable(sympydigits(m, 7)[1:] for m in count(0))


def A030548_gen():
    return chain.from_iterable(sympydigits(m, 6)[1:] for m in count(1))


def A031219_gen():
    return chain.from_iterable(sympydigits(m, 5)[1:] for m in count(1))


def A030373_gen():
    return chain.from_iterable(sympydigits(m, 4)[1:] for m in count(1))


def A054635_gen():
    return chain.from_iterable(sympydigits(m, 3)[1:] for m in count(0))


def A003137_gen():
    return (d for m in count(1) for d in sympydigits(m, 3)[1:])


def A030190_gen():
    return (int(d) for m in count(0) for d in bin(m)[2:])


def A298312_gen():  # generator of terms
    n, m = 1, 30
    while True:
        k = prevprime(m // 3)
        k2 = nextprime(k)
        if prevprime(k) + k + k2 == m or k + k2 + nextprime(k2) == m:
            yield n * (3 * n - 2)
        n += 1
        m += 18 * n + 3


def A298313_gen():  # generator of terms
    n, m = 1, 30
    while True:
        k = prevprime(m // 3)
        k2 = prevprime(k)
        k3 = nextprime(k)
        if k2 + k + k3 == m:
            yield k2
        elif k + k3 + nextprime(k3) == m:
            yield k
        n += 1
        m += 18 * n + 3


@lru_cache(maxsize=None)
def A298356(n):
    if n <= 2:
        return 1
    c, j = A298356(n - 1) + A298356(n - 2), 2
    k1 = n // j
    while k1 > 1:
        j2 = n // k1 + 1
        c += (j2 - j) * A298356(k1)
        j, k1 = j2, n // j2
    return c + n - j + 1


@lru_cache(maxsize=None)
def A298357(n):
    if n <= 2:
        return n + 1
    c, j = A298357(n - 1) + A298357(n - 2), 2
    k1 = n // j
    while k1 > 1:
        j2 = n // k1 + 1
        c += (j2 - j) * A298357(k1)
        j, k1 = j2, n // j2
    return c + 2 * (n - j + 1)


@lru_cache(maxsize=None)
def A298369(n):
    if n <= 2:
        return 1
    c, j = A298369(n - 1) + A298369(n - 2), 2
    k1 = n // j
    while k1 > 1:
        j2 = n // k1 + 1
        c += (j2 * (j2 - 1) - j * (j - 1)) * A298369(k1) // 2
        j, k1 = j2, n // j2
    return c + (n * (n + 1) - j * (j - 1)) // 2


@lru_cache(maxsize=None)
def A298370(n):
    if n <= 2:
        return n + 1
    c, j = A298370(n - 1) + A298370(n - 2), 2
    k1 = n // j
    while k1 > 1:
        j2 = n // k1 + 1
        c += (j2 * (j2 - 1) - j * (j - 1)) * A298370(k1) // 2
        j, k1 = j2, n // j2
    return c + 2 * (n * (n + 1) - j * (j - 1)) // 2


def A298827(n):
    return n_order(3, 3**n + 2)


def A301631(n):
    return (
        Fraction(comb(2 * n, n)) / (n + 1) - Fraction(4**n) / (n + 1) ** 2
    ).numerator


def A301861(n):
    return int(sum(mpz(d) for d in gmpy2digits(fac(fac(n)))))


def A301943(n):
    return sum(1 for i in range(1, 10 ** (n - 1) + 1) if isprime(100 * i**2 + 1))


def A302021_gen():  # generator of terms
    klist = [isprime(i**2 + 1) for i in range(6)]
    for k in count(0):
        i = isprime((k + 6) ** 2 + 1)
        if klist[0] and klist[2] and i:
            yield k
        klist = klist[1:] + [i]


def A302087_gen():  # generator of terms
    klist = [isprime(i**2 + 1) for i in range(6)]
    for k in count(0):
        i = isprime((k + 6) ** 2 + 1)
        if klist[0] and i:
            yield k
        klist = klist[1:] + [i]


def A302294(n):
    s = set()
    for i in range(1, (n + 3) // 2):
        for j in divisors(i):
            for k in divisors(n - i):
                if j != k:
                    s.add((min(j, k), max(j, k)))
    return 3 * divisor_count(n) + 2 * len(s) - 1


def A302552(n):
    return sum((6, 2, 5, 5, 4, 5, 6, 3, 7, 6)[int(d)] for d in str(prime(n)))


def A303108_gen():  # generator of terms
    blist = [2, 5]
    yield from blist
    for n in count(3):
        blist = [blist[1], 3 * (n - 1) * blist[-1] - (2 * n - 3) * (n - 2) * blist[-2]]
        yield blist[-1]


def A303109_gen():  # generator of terms
    blist = [0, 1]
    yield from blist
    for n in count(2):
        blist = [
            blist[1],
            (3 * n * (n - 1) + 1) * blist[-1] - (2 * n - 3) * (n - 1) ** 3 * blist[-2],
        ]
        yield blist[-1]


@lru_cache(maxsize=None)
def A304212_helper(n, i):
    return (
        1
        if n == 0 or i == 1
        else A304212_helper(n, i - 1) + A304212_helper(n - i, min(i, n - i))
    )


def A304212(n):
    return A304212_helper(n**3 - n**2, n**2)


def A305377(n):
    m, tlist, s = prime(n), [1, 2, 4], 0
    while tlist[-1] + tlist[-2] + tlist[-3] <= m:
        tlist.append(tlist[-1] + tlist[-2] + tlist[-3])
    for d in tlist[::-1]:
        s *= 2
        if d <= m:
            s += 1
            m -= d
    return s


def A305380(n):
    m, tlist, s = 2**n, [1, 2, 4], 0
    while tlist[-1] + tlist[-2] + tlist[-3] <= m:
        tlist.append(tlist[-1] + tlist[-2] + tlist[-3])
    for d in tlist[::-1]:
        s *= 2
        if d <= m:
            s += 1
            m -= d
    return s


def A305876(n):
    m, tlist, s = 2**n, [1, 2], 0
    while tlist[-1] + tlist[-2] <= m:
        tlist.append(tlist[-1] + tlist[-2])
    for d in tlist[::-1]:
        s *= 2
        if d <= m:
            s += 1
            m -= d
    return s


def A306392(n):
    return int(
        "".join("1" if d == "2" else ("2" if d == "1" else d) for d in str(2**n))
    )


def A306494(n):
    k = n
    for m in count(0):
        s = str(k)
        for i in range(1, len(s)):
            if s[i] == s[i - 1]:
                return m
        k *= 3


def A307535(n):
    r = 2**n
    m, k = 2**r + 1, 0
    w = m
    while not isprime(w):
        k += 1
        w += r
    return k


def A308395_gen():  # generator of terms
    w = 0
    for y in count(1):
        w += y
        z = 0
        for x in range(1, y + 1):
            z += x
            if is_square(8 * (w + z) + 1):
                yield y
                break


def A318358_gen():  # generator of terms
    yield 2
    bset, p, q = {2}, 2, 4
    while True:
        r = sorted(
            next(
                zip(*diop_quadratic(symbolx**2 + q - p * symboly - symbolx * symboly))
            )
        )
        for a in r[bisect.bisect_right(r, 0) :]:
            if a not in bset:
                yield a
                bset.add(a)
                break
        p += a
        q += a**2


def A320059(n):
    c1, c2 = 1, 1
    for p, a in factorint(n).items():
        c1 *= (p ** (2 * a + 1) - 1) // (p - 1)
        c2 *= (p ** (a + 1) - 1) // (p - 1)
    return c1 - c2


def A320262(n):
    return int(
        "".join(
            d + "0" for d in split("(0+)|(1+)", bin(n)[2:]) if d != "" and d != None
        ),
        2,
    )


def A320263(n):
    return int(
        "".join(
            "0" + d for d in split("(0+)|(1+)", bin(n)[2:]) if d != "" and d != None
        ),
        2,
    )


def A320890_gen():  # generator of terms
    b = 11
    yield b
    while True:
        a0, a1, s = 0, 0, ""
        for d in str(b):
            if d == "0":
                a0 += 1
                s += bin(a0)[2:]
            else:
                a1 += 1
                s += bin(a1)[2:]
        b = int(s)
        yield b


def A322183_gen():
    return (int(str(d), 2) for d in A320890_gen())


def A321210_gen():  # generator of terms
    for i in count(0):
        s = bin(i)[2:]
        s += s[-2::-1]
        p = int(s) + int("02" * (len(s) // 2) + "0")
        q = 6 * p + 1
        t = str(q)
        if t == t[::-1] and isprime(p) and isprime(q):
            yield q


def A321443(n):
    if n == 0:
        return 1
    c = 0
    for i in range(n):
        mi = i * (i + 1) + n
        for j in range(i + 1, n + 1):
            k = mi - j * j
            if k < 0:
                break
            if not k % j:
                c += 1
    return c


def A321803(n):
    return int(
        "0"
        + "".join(
            d if len(d) != 1 else ""
            for d in split("(0+)|(1+)|(2+)|(3+)|(4+)|(5+)|(6+)|(7+)|(8+)|(9+)", str(n))
            if d != "" and d != None
        )
    )


def A321804(n):
    return (lambda x: int(x) if x != "" else -1)(
        "".join(
            d if len(d) != 1 else ""
            for d in split("(0+)|(1+)|(2+)|(3+)|(4+)|(5+)|(6+)|(7+)|(8+)|(9+)", str(n))
            if d != "" and d != None
        )
    )


def A322609_gen(startvalue=1):
    return (
        k
        for k in count(max(startvalue, 1))
        if sum(
            d
            for d in divisors(k, generator=True)
            if max(factorint(d).values(), default=1) >= 2
        )
        == 2 * k
    )


def A323192_gen():  # generator of terms
    for k in count(0):
        n = isqrt(2 ** (2 * k + 1))
        if n * (n - 1) + 2 ** (len(bin(n)) - 2) - 2 ** (len(bin(n**2)) - 2) > 0:
            yield n


def A328291(n):
    if n > 9876543210 or n % 100 == 0:
        return 0
    k = 9876543210 // n
    m = k * n
    s = str(m)
    while len(set(s)) != len(s):
        k -= 1
        m -= n
        s = str(m)
    return k


@lru_cache(maxsize=None)
def A328967(n):
    if n == 0:
        return 1
    c, j = n - 1, 1
    k1 = (n - 1) // j
    while k1 > 1:
        j2 = (n - 1) // k1 + 1
        c += (j2 - j) * A328967(k1)
        j, k1 = j2, (n - 1) // j2
    return j - c


def A329792(n):
    if n % 10:
        m, s = 1, set("12345")
        while not set(str(m * n)) <= s:
            m += 1
        return m
    else:
        return -1


def A329793(n):
    if n % 10:
        m, s = n, set("12345")
        while not set(str(m)) <= s:
            m += n
        return m
    else:
        return -1


def A331759(n):
    return (2 * n + 1) ** 2 + sum(
        totient(i) * (2 * n + 2 - i) * (4 * n + 4 - i) for i in range(2, 2 * n + 2)
    )


def A331760(n):
    return (
        n**2
        + sum(
            totient(i) * (2 * n + 1 - i) * (4 * n + 2 - i) for i in range(2, 2 * n + 1)
        )
        // 4
    )


def A333034(n):
    return sum(int(d) for i in range(10 ** (n - 1), 10**n) for d in str(i**2))


def A333073(n):
    f = 1
    for i in range(1, n + 1):
        f = lcm(f, i)
    f = int(f)
    glist = []
    for i in range(1, n + 1):
        glist.append(f // i)
    m = 1 if n < 2 else primorial(n, nth=False) // primorial(n // 2, nth=False)
    k = m
    while True:
        p, ki = 0, -k
        for i in range(1, n + 1):
            p = (p + ki * glist[i - 1]) % f
            ki = (-k * ki) % f
        if p == 0:
            return k
        k += m


def A333074(n):
    f, g = int(factorial(n)), []
    for i in range(n + 1):
        g.append(int(f // factorial(i)))
    m = 1 if n < 2 else prod(primefactors(n))
    k = m
    while True:
        p, ki = 0, 1
        for i in range(n + 1):
            p = (p + ki * g[i]) % f
            ki = (-k * ki) % f
        if p == 0:
            return k
        k += m


def A333420_T(n, k):  # T(n,k) for A333420
    if k == 1:
        return int(factorial(n))
    if n == 1:
        return k * (k + 1) // 2
    if k % 2 == 0 or (k >= n - 1 and n % 2 == 1):
        return (k * (k * n + 1) // 2) ** n
    if k >= n - 1 and n % 2 == 0 and k % 2 == 1:
        return ((k**2 * (k * n + 1) ** 2 - 1) // 4) ** (n // 2)
    nk = n * k
    nktuple = tuple(range(1, nk + 1))
    nkset = set(nktuple)
    count = 0
    for firsttuple in combinations(nktuple, n):
        nexttupleset = nkset - set(firsttuple)
        for s in permutations(sorted(nexttupleset), nk - 2 * n):
            llist = sorted(nexttupleset - set(s), reverse=True)
            t = list(firsttuple)
            for i in range(0, k - 2):
                itn = i * n
                for j in range(n):
                    t[j] += s[itn + j]
            t.sort()
            w = 1
            for i in range(n):
                w *= llist[i] + t[i]
            if w > count:
                count = w
    return count


def A333446_T(n, k):  # T(n,k) for A333446
    c, l = 0, list(range(1, k * n + 1, k))
    lt = list(l)
    for i in range(n):
        for j in range(1, k):
            lt[i] *= l[i] + j
        c += lt[i]
    return c


def A333463(n):
    return sum(
        (2 * sum(d // k for k in range(1, isqrt(d) + 1)) - isqrt(d) ** 2)
        * totient(n // d)
        for d in divisors(n, generator=True)
    )


def A333577(n):
    if n == 2:
        return 0
    p = prime(n)
    q, r = nextprime(p), 10 ** len(str(p))
    return p * q * mod_inverse(q, r) % (q * r)


def A334841(n):
    return 2 * bin(n)[-1:1:-2].count("1") - (len(bin(n)) - 1) // 2 if n > 0 else 0


def A335233_gen():  # generator of terms
    f = 1
    for k in count(1):
        f *= k
        g = 1
        for i in range(1, k + 1):
            g += f
            if isprime(g):
                break
        else:
            yield k


def A335402_gen():
    return chain((0, 1, 2, 4), (prime(i) for i in count(3)))


def A336298(n):
    return prevprime(prime(n) // 2 + 1)


def A337106(n):
    return 0 if n <= 1 else divisor_count(factorial(n)) - 2


def A337174(n):
    return (divisor_count(n) + 1) ** 2 // 4


def A337988_gen(startvalue=1):  # generator of terms
    for n in count(max(startvalue, 1)):
        for d in divisors(n):
            if 2 * d * d >= n:
                break
            a, b = integer_nthroot(n - d * d, 2)
            if b and n % a == 0:
                yield n
                break


def A338577_gen():  # generator of terms
    p, q, r = 2, 3, 5
    while True:
        if (q - p) * (r - p) > p:
            yield p
        p, q, r = q, r, nextprime(r)


def A339485(n):
    c, primeset2 = n, set(prime(i) for i in range(1, n))
    primeset = primeset2 | {prime(n)}
    for l in range(2, n + 1):
        for d in combinations(primeset, l):
            a, b = divmod(sum(d), l)
            if b == 0 and a in primeset2:
                c += 1
    return c


@lru_cache(maxsize=None)
def A339507(n):
    pallist = set(i for i in range(1, n * (n + 1) // 2 + 1) if str(i) == str(i)[::-1])
    return (
        1
        if n == 0
        else A339507(n - 1)
        + sum(
            sum(d) + n in pallist
            for i in range(n)
            for d in combinations(range(1, n), i)
        )
    )


def A339573(n):
    return n * (n + 1) // 6 - 1


def A340667(n):
    return 0 if n == 0 else int(bin(n)[2:].replace("0", "0" * n), 2)


def A340835(n):
    if n == 0:
        return 0
    s = str(n)
    for i, x in enumerate(s):
        if x != "9":
            break
    else:
        return n
    s1, s2 = s[: i + 1], s[i + 1 :]
    if s2 == "":
        if s1[-1] == "0":
            return int(str(n + 1)[::-1])
        else:
            return int(s[::-1])
    if int(s2) <= 1:
        return int("1" + s2[-2::-1] + s1[::-1])
    else:
        return int("1" + "0" * (len(s2) - 1) + str(int(s1) + 1)[::-1])


def A340836(n):
    if n == 0:
        return 0
    s = bin(n)[2:]
    i = s.find("0")
    if i == -1:
        return n
    s1, s2 = s[: i + 1], s[i + 1 :]
    if s2 == "":
        return n + 1
    if int(s2) <= 1:
        return int("1" + s2[-2::-1] + s1[::-1], 2)
    else:
        return int("1" + "0" * (len(s2) - 1) + bin(int(s1, 2) + 1)[:1:-1], 2)


def A340868_gen():  # generator of terms
    p, q, r, s = 2, 3, 5, 7
    for k in count(1):
        if pow(p, q, r) == s % r:
            yield k
        p, q, r, s = q, r, s, nextprime(s)


def A340967(n):
    c, x = 0, n
    while x > 1:
        c += 1
        x = n % sum(p * e for p, e in factorint(x).items())
    return c


def A341280_gen():  # generator of terms
    k2, d = 3, 2
    for k in count(1):
        if d % k == 0:
            yield k
        if isprime(k):
            d -= k
        if isprime(k2):
            d += k2
        k2 += 2


def A341718(n):
    return int(str(2**n)[::-1]) - 1


def A341931(n):
    k, m, r = n, n - 1, n if isprime(n) else -1
    while m > 0:
        k = int(str(k) + str(m))
        if isprime(k):
            r = m
        m -= 1
    return r


def A341934_gen():  # generator of terms
    p, q, r, s = (
        2,
        3,
        5,
        7,
    )
    while True:
        if isprime(2 * q * (p - r) + r * s):
            yield p
        p, q, r, s = q, r, s, nextprime(s)


def A342024(n):
    f = factorint(n)
    for p in f:
        if primepi(p) < f[p]:
            return 1
    return 0


def A342040(n):
    s = bin(n)[2:]
    return int(s + s[-2::-1])


def A342131(n):
    return (3 * n + 1) // 2 if n % 2 else n // 2 + n // 4


def A342280(n):
    return 4 * n + 2 + isqrt(8 * n * (n + 1) + 2)


def A342281(n):
    return isqrt(8 * n * (n + 1) + 2)


def A342288_gen():  # generator of terms
    yield 2
    b = 2
    for n in count(1):
        b = b * 4 * (2 * n - 1) * (2 * n + 3) // ((n + 1) * (n + 3))
        yield b


def A342387_gen():  # generator of terms
    yield 20
    xlist, ylist, x, y = [4, 20, 39], [1, 6, 12], 39, 12
    while True:
        if len(str(x + 1)) == len(str(y + 1)) + 1:
            yield x
        x, y = 19 * xlist[-3] + 60 * ylist[-3] + 39, 6 * xlist[-3] + 19 * ylist[-3] + 12
        xlist, ylist = xlist[1:] + [x], ylist[1:] + [y]


def A342388_gen():  # generator of terms
    yield 6
    xlist, ylist, x, y = [4, 20, 39], [1, 6, 12], 39, 12
    while True:
        if len(str(x + 1)) == len(str(y + 1)) + 1:
            yield y
        x, y = 19 * xlist[-3] + 60 * ylist[-3] + 39, 6 * xlist[-3] + 19 * ylist[-3] + 12
        xlist, ylist = xlist[1:] + [x], ylist[1:] + [y]


def A342455(n):
    return primorial(n) ** 5 if n >= 1 else 1


@lru_cache(maxsize=None)
def A342600(n, m=None):  # A342600(n) = A342600(n,n)
    if m == None:
        m = n
    return (
        max(m, n)
        if m < 2 or n < 2
        else A342600(n - 1, m - 1) + A342600(n - 1, m - 2) + A342600(n - 2, m - 1)
    )


def A342810_gen(startvalue=1):
    return (
        n
        for n in count(max(startvalue, 1))
        if n == 1 or ((n % 9) + 1) * pow(10, n // 9, n) % n == 1
    )


def A342956(n):
    return (
        sum(factorint(sum(p * e for p, e in factorint(n).items())).values())
        if n > 1
        else 0
    )


def A343197_gen(startvalue=2):
    return (
        n
        for n in count(max(startvalue, 2))
        if isprime(
            sum(sum(p * e for p, e in factorint(i).items()) for i in range(2, n + 1))
        )
    )


@lru_cache(maxsize=None)
def A343511(n):
    return 1 + sum(A343511(d) ** 2 for d in divisors(n) if d < n)


def A343524_gen():  # generator of terms
    yield 0
    for l in count(1):
        for d in combinations("123456789", l):
            s = "".join(d)
            yield int(s + s[-2::-1])
        for d in combinations("123456789", l):
            s = "".join(d)
            yield int(s + s[::-1])


def A343728_gen():
    return (
        n
        for n in (2 * int(gmpy2digits(d, 5)) for d in count(0))
        if set(str(n**2)[:-1]) <= set("13579")
    )


def A343813(n):
    p = prime(n)
    pset = set(sieve.primerange(2, p + 1))
    return sum(1 for d in partitions(p) if len(set(d) & pset) > 0)


def A343943(n):
    fs = factorint(n)
    return len(
        set(sum(d) for d in multiset_combinations(fs, (sum(fs.values()) + 1) // 2))
    )


def A343995(n):
    plist = [p**q for p, q in factorint(2 * (2**n - 1)).items()]
    return min(
        k
        for k in (crt(plist, d)[0] for d in product([0, -1], repeat=len(plist)))
        if k > 0
    )


def A343998(n):
    fs = factorint(2 * n)
    plist = [p ** fs[p] for p in fs]
    return (
        1
        + min(
            k
            for k in (crt(plist, d)[0] for d in product([0, -1], repeat=len(plist)))
            if k > 0
        )
    ) // 2


def A344057(n):
    return 1 if n == 0 else 2 * n**2 * (2 * n - 1) * factorial(n - 1) ** 2


def A344983(n):
    return int((mpz(2) ** 77232917 - 1) // mpz(10) ** (46498849 - n) % 10)


def A344984(n):
    return int((mpz(2) ** 82589933 - 1) // mpz(10) ** (49724095 - n) % 10)


def A345421(n):
    return igcdex(7, prime(n))[0]


def A345429(n):
    return sum(
        abs(u)
        for u, v, w in (igcdex(x, y) for x in range(1, n + 1) for y in range(1, n + 1))
        if w == 1
    )


def A346120(n):
    s, k, f = str(n), 0, 1
    while s not in str(f):
        k += 1
        f *= k
    return k


def A346527(n):
    a, b, k, k2, m, r = -6 * (n + 1) ** 2, (n + 1) ** 4, 2, 4, 1, 0
    while 2 * m + a < 0 or m * (m + a) + b < 0:
        if isqrt(2 * m) - isqrt(m - 1) == n:
            r = m
        k += 1
        k2 += 2 * k - 1
        m = (k2 - 1) // 2
    return r


def A346621(n):
    return 0 if n <= 2 else A346621(n - 1) + (n if len(primefactors(n)) == 2 else 0)


def A346970(n):
    c, ps = 2, primorial(n)
    while True:
        m = ps // gcd(ps, c)
        if m == 1:
            return c
        p = max(primefactors(m))
        for a in range(p, c, p):
            if a * (c - a) % m == 0:
                return c
        c += 1


def A346971(n):
    c, nlist = 1, list(range(1, n + 1))
    while True:
        mlist = [m for m in nlist if c % m]
        if len(mlist) == 0:
            return c
        p = max(mlist)
        for a in range(p, c, p):
            for m in mlist:
                if a % m and (c - a) % m:
                    break
            else:
                return c
        c += 1


def A346988(n):
    k, kn = n + 1, 1
    while True:
        if pow(n, kn, k) == 1:
            return k
        k += 1
        kn += 1


def A347346(n):
    if n % 10 == 0:
        return 0
    s = str(n)
    if s == s[::-1]:
        return n
    for i in range(1, len(s)):
        if s[:-i] == s[-i - 1 :: -1]:
            return int(s[: -i - 1 : -1] + s)


def A347347(n):
    if n % 2 == 0:
        return 0
    s = bin(n)[2:]
    if s == s[::-1]:
        return n
    for i in range(1, len(s)):
        if s[:-i] == s[-i - 1 :: -1]:
            return int(s[: -i - 1 : -1] + s, 2)


def A347089(n):
    return gcd(
        divisor_count(n), sum(gcd(d, n // d) for d in divisors(n, generator=True))
    )


def A348296(n):
    c, k = 0, 0
    while c != n:
        k += 1
        c += -1 if (isqrt(2 * k * k) - k) % 2 else 1
    return k


def A348412_gen(startvalue=2):
    return (
        2 * n
        for n in count(max(startvalue // 2 + startvalue % 2, 1))
        if (lambda x, y: 2 * gcd(x, y * n) >= x)(divisor_sigma(n), divisor_sigma(n, 0))
    )


def A000075(n):
    return (
        0
        if n == 0
        else len(
            set(
                2 * x**2 + 3 * y**2
                for x in range(1 + isqrt(2 ** (n - 1)))
                for y in range(1 + isqrt((2**n - 2 * x**2) // 3))
                if 0 < 2 * x**2 + 3 * y**2 <= 2**n
            )
        )
    )


def A008506_gen():  # generator of terms
    m = [13, -65, 221, -494, 793, -923, 793, -494, 221, -65, 13, 0, 1]
    while True:
        yield m[-1]
        for i in range(12):
            m[i + 1] += m[i]


@lru_cache(maxsize=None)
def A015613(n):
    if n == 0:
        return 0
    c, j = 0, 2
    k1 = n // j
    while k1 > 1:
        j2 = n // k1 + 1
        c += (j2 - j) * (2 * (A015613(k1) + k1) - 1)
        j, k1 = j2, n // j2
    return (n * (n - 3) - c + j) // 2


def A015942_gen(startvalue=2):
    return (
        n
        for n in count(max(startvalue + startvalue % 2, 2), 2)
        if pow(2, n, n) == n // 2 + 1
    )


def A018166(n):
    i, j = iroot_rem(18**n, 5)
    return int(i) + int(32 * j >= 10 * i * (4 * i * (2 * i * (i + 1) + 1) + 1) + 1)


def A020418_gen():
    return (
        n
        for n, s in ((i, continued_fraction_periodic(0, 1, i)[-1]) for i in count(1))
        if isinstance(s, list) and len(s) == 79
    )


def A020430_gen():
    return (
        n
        for n, s in ((i, continued_fraction_periodic(0, 1, i)[-1]) for i in count(1))
        if isinstance(s, list) and len(s) == 91
    )


def A031557_gen():
    return (
        n
        for n, s in ((i, continued_fraction_periodic(0, 1, i)[-1]) for i in count(1))
        if isinstance(s, list) and len(s) % 2 == 0 and s[len(s) // 2 - 1] == 59
    )


def A031597_gen():
    return (
        n
        for n, s in ((i, continued_fraction_periodic(0, 1, i)[-1]) for i in count(1))
        if isinstance(s, list) and len(s) % 2 == 0 and s[len(s) // 2 - 1] == 99
    )


def A031702_gen():
    return (
        n
        for n, s in ((i, continued_fraction_periodic(0, 1, i)[-1]) for i in count(1))
        if isinstance(s, list) and min(s) == 24
    )


def A031713_gen():
    return (
        n
        for n, d in ((n, continued_fraction_periodic(0, 1, n)[-1]) for n in count(1))
        if isinstance(d, list) and min(d) == 35
    )


def A031775_gen():
    return (
        n
        for n, d in ((n, continued_fraction_periodic(0, 1, n)[-1]) for n in count(1))
        if isinstance(d, list) and min(d) == 97
    )


def A031777_gen():
    return (
        n
        for n, d in ((n, continued_fraction_periodic(0, 1, n)[-1]) for n in count(1))
        if isinstance(d, list) and min(d) == 99
    )


def A030082_gen():  # generator of terms
    for i in count(1):
        p = prime(i)
        q = p**3
        if set(str(p)) <= set(str(q)):
            yield q


def A030087_gen(startvalue=1):
    return (
        n
        for n in count(max(startvalue, 1))
        if set(str(n)) & set(str(n**3)) == set() and isprime(n)
    )


def A031415_gen(startvalue=1):  # generator of terms
    for n in count(max(startvalue, 1)):
        cf = continued_fraction_periodic(0, 1, n)
        if (
            len(cf) > 1
            and len(cf[1]) > 1
            and len(cf[1]) % 2
            and cf[1][len(cf[1]) // 2] == 2
        ):
            yield n


def A035523_gen():  # generator of terms
    yield 1
    l = 1
    while True:
        l += reversedigits(l, 3)
        yield l


def A037967(n):
    return comb(comb(2 * n, n) + 1, 2)


def A044460_gen(startvalue=0):
    return (
        n
        for n in count(max(startvalue, 0))
        if "02" in gmpy2digits(n, 5) and "02" not in gmpy2digits(n + 1, 5)
    )


def A045541_gen():  # generator of terms
    yield 2
    l = 2
    while True:
        l = int("".join(d for d in str(l**2) if not d in set(str(l))))
        yield l


def A046380_gen():  # generator of terms
    for x in pal10_gen():
        a = factorint(x)
        if sum(list(a.values())) == 6 and all(map(is_pal, a.keys())):
            yield x


def A045572(n):
    return 2 * (n + (n + 1) // 4) - 1


def A348480(n):
    if n == 1:
        return 1
    xn = 2 * (n + (n + 1) // 4) - 1
    for l in count(xn - 1):
        for d in multiset_permutations(["0"] * (l - xn + 1) + ["1"] * (xn - 1)):
            s = "1" + "".join(d)
            if gcd(int(s), int(s[::-1])) == xn:
                return int(s, 2)


def A046705_gen():
    return (
        n
        for n in (
            (10 ** (2 * l + 1) - 1) // 9 + d * 10**l
            for l in count(0)
            for d in (1, 2, 4, 6)
        )
        if isprime(n)
    )


def A051202_gen():  # generator of terms
    a2, a1 = 1, 1
    for n in count(3):
        a = abs(a1 + 2 * a2 - n)
        if a == 0:
            yield n
        a1, a2 = a, a1


def A053964_gen():  # generator of terms
    for l in count(1):
        for p in product(*["479"] * l):
            a, b = integer_nthroot(int("".join(p)), 2)
            if b:
                yield a


def A053965_gen():  # generator of terms
    for l in count(1):
        for p in product(*["479"] * l):
            n = int("".join(p))
            if is_square(n):
                yield n


def A054793(n):
    a, b = integer_nthroot(n, 4)
    return (
        n
        if n <= 1
        else A054793(a) ** 4
        if b
        else n + 1
        if (n - a**4) % 2
        else (n - 1) ** 4
    )


def A059402_gen(startvalue=2):
    return (
        n
        for n in count(max(startvalue, 2))
        if n % 10
        and len(factorint(n)) > 1
        and all(str(a**b) in str(n) for a, b in factorint(n).items())
    )


def A061051(n):
    if n == 0:
        return 0
    nstart = 10 ** (n - 1)
    nend = 10 * nstart
    for i in range(nstart, nend):
        k = int(str(i) * 2)
        if is_square(k):
            return k
    for i in range(nstart, nend):
        si = str(i) * 2
        for sj in "014569":
            k = int(si + sj)
            if is_square(k):
                return k


def A062935_gen():  # generator of terms
    n = 1
    for i in count(1):
        n *= i
        s = str(n + 1)
        if s == s[::-1]:
            yield n + 1


def A065899(n):
    return compositepi(factorial(composite(n)) // primorial(primepi(composite(n))))


def A066467_gen(startvalue=1):
    return (n for n in count(max(startvalue, 1)) if antidivisor_count(n) == 2)


def A066469_gen(startvalue=1):
    return (n for n in count(max(startvalue, 1)) if antidivisor_count(n) == 4)


def A066472_gen(startvalue=1):
    return (n for n in count(max(startvalue, 1)) if antidivisor_count(n) == 6)


def A073954_gen(startvalue=1):
    return (n for n in count(max(startvalue, 1)) if antidivisor_sigma(n) > 2 * n)


def A074713_gen(startvalue=1):
    return (n for n in count(max(startvalue, 1)) if antidivisor_sigma(n) == totient(n))


def A074730_gen():
    return (n for n in (i**2 for i in count(1)) if is_square(antidivisor_sigma(n)))


def A076642(n):
    y = Poly(rf(6 * symbolx + 1, n)).all_coeffs()[::-1]
    return y.index(max(y))


def A350595(n):
    return sum(
        (-1 if (n + k) % 2 else 1) * comb(2 * n, k) ** n for k in range(2 * n + 1)
    )


def A082439_gen():  # generator of terms
    yield 3
    for i in count(1):
        s = str(i)
        n = int(s + "3" + s[::-1])
        if isprime(n):
            yield n


def A082617_gen():  # generator of terms
    yield 1
    a = 1
    while True:
        p = 2
        b = p * a
        bs = str(b)
        while bs != bs[::-1] or max(factorint(b).values()) > 1:
            p = nextprime(p)
            b = p * a
            bs = str(b)
        yield b
        a = b


def A082646_gen():  # generator of terms
    for i in count(1):
        p = str(prime(i))
        h = [p.count(d) for d in "0123456789" if d in p]
        if min(h) == max(h):
            yield int(p)


def A085375_gen():  # generator of terms
    b = 1
    for n in count(0):
        yield b
        b = b * 2 * (n + 5) * (2 * n + 3) // ((n + 1) * (n + 2))


def A090850_gen():  # generator of terms
    yield 0
    f, blist = 6, [0]
    while True:
        blist = [blist[0] + f] + list(map(add, blist[:-1], blist[1:])) + [1]
        yield from blist


def A096217_gen():  # generator of terms
    yield 1
    blist = [1]
    for n in count(2):
        b = sum(x for x in blist if gcd(x, n) == 1)
        blist.append(b)
        yield b


def A096488(n):
    return len(set(continued_fraction(sqrt((10**n - 1) // 9))[-1]))


def A097963_gen():
    return chain(
        (1,),
        accumulate(
            repeat(15),
            lambda x, _: x
            + 2
            + len(num2words(x, to="ordinal").replace(" and ", " ").replace(", ", " ")),
        ),
    )


def A101701_gen(startvalue=1):
    return (
        n
        for n in count(max(startvalue, 1))
        if n == sum(int(d) for d in (str(x)[::-1] for x in divisors(n)))
    )


def A104476(n):
    return comb(n + 7, 7) * comb(n + 11, 7)


def A104476_gen():  # generator of terms
    m = [3432, -1716, 660, 330, 330, 330, 330, 330, 330, 330, 330, 330, 330, 330, 330]
    while True:
        yield m[-1]
        for i in range(14):
            m[i + 1] += m[i]


def A105252(n):
    return comb(n + 5, n) * comb(n + 9, n)


def A105252_gen():  # generator of terms
    m = [2002, -4433, 3487, -1133, 127, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]
    while True:
        yield m[-1]
        for i in range(14):
            m[i + 1] += m[i]


def A105253(n):
    return comb(n + 6, n) * comb(n + 10, n)


def A105253_gen():  # generator of terms
    m = [8008, -22022, 23023, -11297, 2563, -209] + [1] * 11
    while True:
        yield m[-1]
        for i in range(16):
            m[i + 1] += m[i]


def A105943(n):
    return comb(n + 7, n) * comb(n + 10, 7)


def A105943_gen():  # generator of terms
    m = [3432, -3432, 1320, 0] + [120] * 11
    while True:
        yield m[-1]
        for i in range(14):
            m[i + 1] += m[i]


def A107337_gen():  # generator of terms
    yield 1
    blist, c = [1], 1
    while True:
        blist = list(
            chain.from_iterable(
                (
                    [1, 2, 1, 3, 2, 3, 1] if d == 1 else [3] if d == 2 else [1]
                    for d in blist
                )
            )
        )
        yield from blist[c:]
        c = len(blist)


def A107908_gen():  # generator of terms
    m = [21, -13, 3] + [1] * 5
    yield m[-1]
    while True:
        for i in range(7):
            m[i + 1] += m[i]
        yield m[-1]


def A108646_gen():  # generator of terms
    m = [77, -85, 28, -1, 1, 1, 1, 1]
    while True:
        yield m[-1]
        for i in range(7):
            m[i + 1] += m[i]


def A109351_gen(startvalue=2):
    return (
        n
        for n in count(max(startvalue, 2))
        if integer_nthroot(sum(antidivisors(n)), 3)[1]
    )


def A110690_gen():  # generator of terms
    m = [62, -65, 20, 0, 1, 1, 1, 1, 1]
    while True:
        yield m[-1]
        for i in range(8):
            m[i + 1] += m[i]


def A110693_gen():  # generator of terms
    m = [450, -816, 508, -121, 10, 1, 1, 1, 1, 1]
    while True:
        yield m[-1]
        for i in range(9):
            m[i + 1] += m[i]


def A113009(n):
    return sum(int(d) for d in str(n)) ** len(str(n))


def A113010(n):
    return len(str(n)) ** sum(int(d) for d in str(n))


def A115286_gen():  # generator of terms
    m = [120, -300, 272, -96, 8, 0, 0]
    while True:
        yield m[-1]
        for i in range(6):
            m[i + 1] += m[i]


def A116054_gen():  # generator of terms
    k, m = 1, 2
    for n in count(0):
        for i in range(k, m):
            s = str(i * n)
            if s == s[::-1]:
                yield i
        k, m = m, nextprime(m)


def A117790_gen():  # generator of terms
    yield 1
    a, b = 1, 3
    while True:
        if isprime(sum(int(d) for d in str(b))):
            yield b
        a, b = b, a + b


def A118548_gen():
    return (
        n
        for n in (x**2 for x in count(1))
        if not (str(n).count("0") or n % prod(int(d) for d in str(n)))
    )


def A118575_gen(startvalue=1):
    return (
        n
        for n in count(max(startvalue, 1))
        if (m := A031347(n))
        and not (
            str(n).count("0")
            or n % ((1 + (n - 1) % 9))
            or n % m
            or n % sum(int(d) for d in str(n))
            or n % prod(int(d) for d in str(n))
        )
    )


def A350578_gen():  # generator of terms
    yield 0
    b, bcounter = 0, Counter({0})
    for n in count(1):
        b += -n if b - n >= 0 and bcounter[b - n] <= bcounter[b + n] else n
        bcounter[b] += 1
        yield b


def A350579(n):
    b, bcounter = 0, Counter({0})
    for m in count(1):
        if bcounter[b] == n:
            return b
        b += -m if b - m >= 0 and bcounter[b - m] <= bcounter[b + m] else m
        bcounter[b] += 1


def A122004_gen():  # generator of terms
    p = 2
    while True:
        if (
            0
            == sum(pow(prime(i), prime(j), p) for i in range(1, p) for j in range(1, p))
            % p
        ):
            yield p
        p = nextprime(p)


def A123373(n):
    return sum(prime(i) ** prime(j) for i in range(1, n + 1) for j in range(1, n + 1))


def A086787(n):
    return (
        1
        - digamma(n)
        - EulerGamma
        + sum(Fraction(i ** (n + 1), i - 1) for i in range(2, n + 1))
    )


def A128287_gen():  # generator of terms
    yield 1
    x, s = 1, 2
    for i in count(2):
        x = x * (4 * i - 2) // (i + 1)
        s += x
        if not (isprime(i) or s % i):
            yield i


def A130870_gen():  # generator of terms
    for i in pal10_odd_range_gen():
        if (
            i > 2
            and isprime(i)
            and max(factorint(i - 1).values()) > 1
            and max(factorint(i + 1).values()) > 1
        ):
            yield i


def A132365(n):
    a, b, m, s = 2, 1, 0, str(n)
    while True:
        if s in str(a):
            return m
        m += 1
        a, b = b, a + b


def A134009_gen():  # generator of terms
    yield 1
    b = 1
    while True:
        i, j = isqrt_rem(3 * b**2)
        b = i + int(4 * (j - i) >= 1)
        yield int(b)


def A135923_gen():  # generator of terms
    m = [1680, -840, -1380, -240, 641, 393, -209, -10, 0]
    yield m[-1]
    while True:
        for i in range(8):
            m[i + 1] += m[i]
        yield m[-1]


def A137079_gen():
    return (
        int("".join(a) + b)
        for l in count(0)
        for a in product("2356", repeat=l)
        for b in ("5", "6")
        if set(str(int("".join(a) + b) ** 2)) <= {"2", "3", "5", "6"}
    )


def A137093_gen():
    return (
        int("".join(a))
        for l in range(1, 10)
        for a in product("2456", repeat=l)
        if set(str(int("".join(a)) ** 2)) <= {"2", "4", "5", "6"}
    )


def A138584_gen():  # generator of terms
    for l in count(0):
        for d in product("35", repeat=l):
            s = "".join(d)
            n = int(s + "3" + s[::-1])
            if isprime(n):
                yield n
            n += 2 * 10**l
            if isprime(n):
                yield n


@lru_cache(maxsize=None)
def A140466(n):
    if n == 0:
        return 0
    c, j = 0, 2
    k1 = n // j
    while k1 > 1:
        j2 = n // k1 + 1
        c += (j2 - j) * (A140466(k1) // 2 - 1)
        j, k1 = j2, n // j2
    return 2 * (n * (n - 1) - c + j)


def A145203_gen():
    return (
        primepi(3 * n * (n + 1) + 1) for n in count(0) if isprime(3 * n * (n + 1) + 1)
    )


def A145285(n):
    return (5, 8, 12, 16, 20, 25, 28, 32)[n - 1] if n <= 8 else 4 * n + 1


def A147773(n):
    i, j = iroot_rem(n**n, 3)
    return int(i + int(8 * j >= 6 * i * (2 * i + 1) + 1))


def A158215(n):
    if n == 1:
        return 11
    if n == 2:
        return 0
    p2 = prime(n) // 2
    l = p2
    while True:
        for i in combinations(range(l), l - p2):
            s = ["1"] * l
            for x in i:
                s[x] = "0"
            s = "".join(s)
            q = int(s + "1" + s[::-1])
            if isprime(q):
                return q
        l += 1


def A153568(n):
    a, b, = (
        0,
        1,
    )
    for _ in range(n):
        a, b = b, a + b
    return (lambda m: 2 * sum(a // k for k in range(1, m + 1)) - m * m)(isqrt(a))


def A158962(n):
    m = 1
    while True:
        for i in range(n):
            if not isprime(int(str(m) * (i + 1)) - 1):
                break
        else:
            return m
        m += 1


def A160828_gen():  # generator of terms
    m = [96, 0, 80, 80, 98]
    while True:
        yield m[-1]
        for i in range(4):
            m[i + 1] += m[i]


def A160943(n):
    return n + sum(int(d) for d in str(n - 1)) + sum(int(d) for d in str(n + 1))


def A161354_gen():
    return (m for m in (n**3 for n in count(1)) if isprime(int(str(m)[::-1])))


@lru_cache(maxsize=None)
def A162459(n):
    if n == 0:
        return 0
    c, j = n, 2
    k1 = n // j
    while k1 > 1:
        j2 = n // k1 + 1
        c += (j2 - j) * A162459(k1) // 2 ** (k1 - 1)
        j, k1 = j2, n // j2
    return 2 ** (n - 1) * (j - c)


def A167218_gen():  # generator of terms
    for l in count(1):
        plist = []
        l1, l2 = 10 ** (l - 1), 10**l
        m = isqrt(l1)
        if m**2 + 1 < l1:
            m += 1
        while (k := m**2 + 1) < l2:
            if k % 10:
                p = int(str(k)[::-1])
                if isprime(p):
                    plist.append(p)
            m += 1
        yield from sorted(plist)


def A167807_gen():  # generator of terms
    for i in count(3):
        n = i * (i + 1) * (2 * i + 1) // 6
        p2 = prevprime(n // 3)
        p1, p3 = prevprime(p2), nextprime(p2)
        q = p1 + p2 + p3
        while q <= n:
            if q == n:
                yield n
            p1, p2, p3 = p2, p3, nextprime(p3)
            q = p1 + p2 + p3


def A171642_gen(startvalue=1):  # generator of terms
    for n in count(max(startvalue, 1)):
        d = divisors(n)
        s = sum(d)
        if s % 2 and 2 * n <= s and s == 3 * sum(x for x in d if x % 2):
            yield n


def A173102(n):
    return (9 * n**2 - (n % 2)) // 4


def A173208_gen():  # generator of terms
    yield 2
    a, b = 2, 3
    while True:
        if (
            max(factorint(b).values()) <= 1
            and max(factorint(b - 1).values()) <= 1
            and max(factorint(b + 1).values()) <= 1
        ):
            yield b
        a, b = b, a + b


@lru_cache(maxsize=None)
def A175549(n):
    if n == 0:
        return 0
    c, j = 0, 2
    k1 = n // j
    while k1 > 1:
        j2 = n // k1 + 1
        c += (j2 - j) * A175549(k1)
        j, k1 = j2, n // j2
    return 4 * n * (n - 1) * (2 * n + 5) - c + 26 * (j - 1)


def A175583_gen(startvalue=1):  # generator of terms
    for n in count(max(startvalue, 1)):
        d = divisors(n)
        s = sum(d)
        if not s % 2 and max(d) <= s // 2 and isprime(s // 2 - n):
            for x in range(1, 2 ** len(d)):
                if sum(Subset.unrank_binary(x, d).subset) == s // 2:
                    yield n
                    break


def A182578(n):
    m, tlist, s = n**n, [1, 2], 0
    while tlist[-1] + tlist[-2] <= m:
        tlist.append(tlist[-1] + tlist[-2])
    for d in tlist[::-1]:
        if d <= m:
            s += 1
            m -= d
    return s


def A185173(n):
    c = n * (n + 1) // 2
    for i in range(2, n + 1):
        for j in range(i + 1, n + 1):
            pset = set(range(2, n + 1)) - {i, j}
            for p in permutations(pset):
                q, rset, rl = [j, 1, i] + list(p), set(), 0
                for k in range(n):
                    r = 0
                    for l in range(n):
                        r += q[(k + l) % n]
                        if r not in rset:
                            rset.add(r)
                            rl += 1
                        if rl >= c:
                            break
                    else:
                        continue
                    break
                else:
                    c = rl
    return c


def A185267(n):
    p = prime(n)
    s = str(p)
    if s == s[::-1]:
        return p
    for i in range(1, len(s)):
        if s[i:] == s[-1 : i - 1 : -1]:
            return int(s + s[i - 1 :: -1])


def A185695(n):
    p, k, m = 2, 61**n, 10
    q, m2 = p % k, m % k
    while True:
        p = nextprime(p)
        while p >= m:
            m *= 10
            m2 = m % k
        q = (q * m2 + p) % k
        if q == 0:
            return p


def A185698(n):
    p, k, m = 2, 67**n, 10
    q, m2 = p % k, m % k
    while True:
        p = nextprime(p)
        while p >= m:
            m *= 10
            m2 = m % k
        q = (q * m2 + p) % k
        if q == 0:
            return p


def A187975_gen(startvalue=1):
    return (
        n
        for n in count(max(startvalue, 1))
        if isqrt(2 * (n + 5) ** 2) - isqrt(2 * n**2) == 8
    )


def A188089_gen(startvalue=1):
    return (
        n
        for n in count(max(startvalue, 1))
        if isqrt(3 * (n + 4) ** 2) - isqrt(3 * n**2) == 6
    )


def A188290_gen(startvalue=1):
    return (
        n
        for n in count(max(startvalue, 1))
        if isqrt(5 * (n + 4) ** 2) - isqrt(5 * n**2) == 8
    )


def A192272_gen(startvalue=3):  # generator of terms
    for n in count(max(startvalue, 3)):
        if (n * antidivisor_count(n)) % sum(antidivisors(n, generator=True)) == 0:
            yield n


def A192276_gen(startvalue=3):
    return (
        n
        for n in count(max(startvalue, 3))
        if not n % sum(1 for d in range(2, n) if n % d and 2 * n % d in (d - 1, 0, 1))
    )


def A192892(n):
    return (
        1
        if n == 0
        else sum(
            1
            for m in product([0, 1], repeat=n**2)
            if (lambda x: x.det() == x.per())(Matrix(n, n, m))
        )
    )


def A194112(n):
    return sum(isqrt(8 * j**2) for j in range(1, n + 1))


def A194116(n):
    return sum(isqrt(13 * j**2) for j in range(1, n + 1))


def A194137(n):
    return sum(isqrt(6 * j**2) for j in range(1, n + 1))


def A194140(n):
    return n * (n + 1) // 2 + sum(isqrt(3 * j**2) for j in range(1, n + 1))


def A195349_gen():  # generator of terms
    s, p = 0, 1
    for k in count(1):
        d = divisor_count(k)
        s += d
        p *= d
        if p % s == 0:
            yield k


def A197194_gen():  # generator of terms
    m, k = [1] * 10, 1
    while True:
        yield k * m[-1]
        k *= 9
        for i in range(9):
            m[i + 1] += m[i]


def A198193(n):
    return sum((n - i) * int(j) for i, j in enumerate(bin(n)[2:]))


def A201009_gen(startvalue=1):
    return (
        n
        for n in count(max(startvalue, 1))
        if primefactors(n)
        == primefactors(
            sum(int(n * e / p) for p, e in factorint(n).items()) if n > 1 else 0
        )
    )


def A205770(n):
    m = 100**n
    i = integer_nthroot(m, 5)[0]
    return i + int(32 * m >= (1 + 2 * i) ** 5)


def A038103_gen():
    return (
        int(s)
        for s in (gmpy2digits(n, 3) for n in count(0))
        if s in gmpy2digits(int(s), 3)
    )


def A350573_gen():
    return (n for n in count(0) if (s := gmpy2digits(n, 3)) in gmpy2digits(int(s), 3))


def A214332_gen():  # generator of terms
    yield 0
    blist, c = [0], 1
    while True:
        blist = list(
            chain.from_iterable(
                ([0, 1] if d == 0 else [2, 0, 2] if d == 1 else [] for d in blist)
            )
        )
        yield from blist[c:]
        c = len(blist)


def A216395(n):
    if n == 1:
        return 1
    c = 0
    for i in range(2 ** (n - 1) + 1, 2**n):
        s1, s2 = sorted(str(i)), sorted(str(divisor_sigma(i)))
        if len(s1) == len(s2) and s1 == s2:
            c += 1
    return c


def A216396(n):
    c = 0
    for i in range(2 ** (n - 1) + 1, 2**n):
        s1, s2 = sorted(str(i)), sorted(str(divisor_sigma(i) - i))
        if len(s1) == len(s2) and s1 == s2:
            c += 1
    return c


def A216873_gen():  # generator of terms
    n = 1
    for i in count(0):
        s = str(n)
        if sum(isprime(s.count(d)) for d in "0123456789") >= 9:
            yield i
        n *= 2


def A217186(n):
    l, x = [str(d) * n for d in range(10)], 1
    for m in count(0):
        s = str(x)
        for k in l:
            if k in s:
                return len(s)
        x *= 3


def A217191(n):
    if n == 1:
        return 1
    else:
        l, y, x = [str(d) * n for d in range(10)], 0, 1
        for m in count(1):
            s = str(x)
            for k in l:
                if k in s:
                    return len(s)
            y, x = x, y + x


def A217192(n):
    if n == 1:
        return 1
    else:
        l, y, x = [str(d) * n for d in range(10)], 2, 1
        for m in count(1):
            s = str(x)
            for k in l:
                if k in s:
                    return len(s)
            y, x = x, y + x


def A349576_gen():  # generator of terms
    blist = [1, 5]
    yield from blist
    while True:
        blist = [blist[1], sum(blist) // gcd(*blist) + 1]
        yield blist[-1]


def A225864_gen():  # generator of terms
    for l in count(1):
        plist, q = [p for p in [2, 3, 5, 7] if isprime(l - 1 + p)], (10**l - 1) // 9
        for i in range(l):
            for p in plist:
                r = q + (p - 1) * 10**i
                if not isprime(r):
                    yield r


def A226019_gen():  # generator of terms
    yield 2
    for l in count(1):
        plist = []
        l1, l2 = 10 ** (l - 1), 10**l
        m = isqrt(l1)
        if m**2 < l1:
            m += 1
        while (k := m**2) < l2:
            if k % 2:
                p = int(bin(k)[-1:1:-1], 2)
                if isprime(p):
                    plist.append(p)
            m += 1
        yield from sorted(plist)


def A228000(n):
    return min(factorint(144396166620968 * n + 1))


def A228295(n):
    return 0 if n == 0 else 1 + integer_nthroot(12 * n**4, 4)[0]


def A235164_helper(n, b):
    if n == 1:
        t = list(range(1, b))
        for i in range(1, b):
            u = list(t)
            u.remove(i)
            yield i, u
    else:
        for d, v in A235164_helper(n - 1, b):
            for g in v:
                k = d * b + g
                if not k % n:
                    u = list(v)
                    u.remove(g)
                    yield k, u


def A235164_gen():
    return (a for n in count(2, 2) for a, b in A235164_helper(n - 1, n))


def A239437(n):  # requires 3 <= n <= 62
    m = n
    while True:
        s = "".join(gmpy2digits(i, m) for i in range(m))
        for d in permutations(s, m):
            if d[0] != "0":
                c = mpz("".join(d), m)
                for b in range(3, n):
                    if len(set(gmpy2digits(c, b))) == b:
                        break
                else:
                    return int(c)
        m += 1


def A239638_gen():  # generator of terms
    p = 5
    while True:
        if (p % 6) == 5:
            n = (p - 1) // 2
            if pow(2, n, p) == 1 and isprime((2**n - 1) // p):
                yield n
        p = nextprime(p)


def A239942(n):
    return factorial(prime(n)) - factorial(prime(n - 1))


def A240975(n):
    return len(primefactors(n**3 - 1))


def A242028_gen():
    return filter(lambda n: lcm(*antidivisors(n)) < n, count(3))


def A242092_gen(startvalue=1):
    return (
        n
        for n in count(max(startvalue, 1))
        if primefactors(n) == primefactors(int(str(prime(n))[::-1]))
    )


def A242347_gen():
    yield 1
    l = 2
    while True:
        l = int(bin(l)[2:])
        yield len(str(l))


def A242930_gen():
    return filter(
        isprime, (a for a, b in (divmod(k**2 + 7, 11) for k in count(1)) if b == 0)
    )


def A243097_gen():  # generator of terms
    for n in count(1):
        if n % 10:
            s1 = str(n)
            s2 = s1[::-1]
            if s1 != s2 and not n % int(s2):
                yield sum(int(d) for d in s1)


def A243112_gen():  # generator of terms
    yield 0
    a = 0
    for n in count(1):
        s = bin(n)[2:]
        b = sum(s[i:].count("0") for i, d in enumerate(s, start=1) if d == "1")
        if b > a:
            yield n
            a = b


def A243298_gen():  # generator of terms
    m = [362880, -1491840, 2464560, -2082240, 945000, -220248, 22560, -680, 1, -1]
    for n in count(1):
        for i in range(9):
            m[i + 1] += m[i]
        if isprime(m[-1]):
            yield n


def A244444_gen(startvalue=1):
    return (
        n
        for n in count(max(startvalue, 1))
        if len(set(str(n + sum(divisors(n))))) == 1
        and str(n + sum(divisors(n)))[0] == "1"
    )


def A245048_gen():
    return filter(lambda p: isprime(p**2 + 28), (prime(n) for n in count(1)))


def A245061_gen():
    return (p for n, p in enumerate(prime(n) for n in count(1)) if is_square(p - n - 1))


def A245199_gen(startvalue=1):
    return (
        n
        for n in count(max(startvalue, 1))
        if is_square(int(divisor_count(n))) and is_square(int(totient(n)))
    )


def A245202_gen(startvalue=1):
    return (
        n
        for n in count(max(startvalue, 1))
        if is_square(int(divisor_count(n) + totient(n)))
    )


def A245270(n):
    return int("".join(bin(y)[2:] for x in sorted(factorint(n).items()) for y in x), 2)


def A246666_gen(startvalue=1):
    return (
        n for n in count(max(startvalue, 1)) if isprime(3 * n * (n * (n + 4) + 10) + 28)
    )


def A246757(n):
    for i in range(10**n - 1, int("1" * n) - 1, -1):
        pd = prod(int(d) for d in str(i))
        if pd and not i % pd:
            return i


def A246763_gen():
    yield 1
    c = 1
    for n in count(2):
        c = c * (4 * n - 2) // (n + 1)
        yield c**2 % prime(n)


def A247000(n):
    maxcount = 0
    for i in range(2 ** (n - 1), 2**n):
        s = format(i, "0" + str(n) + "b")
        s, plist = s + s[:-1], []
        for j in range(n):
            for k in range(n):
                t = s[j : j + k + 1]
                if t == t[::-1] and not t in plist:
                    plist.append(t)
        if len(plist) > maxcount:
            maxcount = len(plist)
    return maxcount


def A247048_gen(startvalue=1):  # generator of terms
    for n in count(max(startvalue, 1)):
        if not (isprime(n) or isprime(n + 2)):
            m = sum(p * e for p, e in factorint(n).items())
            if isprime(m):
                m2 = sum(p * e for p, e in factorint(n + 2).items())
                if ((m2 == m + 2) or (m == m2 + 2)) and isprime(m2):
                    yield n


def A247108_gen():  # generator of terms
    yield 1
    blist = [1]
    while True:
        blist = list(accumulate([-blist[-1]] + blist))
        yield from blist


def A247213_gen(startvalue=1):
    return (
        n
        for n in count(max(startvalue, 1))
        if n <= 1 or not prod((p + 2) ** e for p, e in factorint(n).items()) % n
    )


def A247592_gen():  # generator of terms
    blist, m, c = [2], 2, 2
    for n in count(1):
        m += 2 * n + 1
        if is_prime(m):
            if is_square(m % blist[-1]):
                yield c
            blist.append(m)
            c += 1


def A247650_gen():  # generator of terms
    yield 1
    blist, g, f = (
        [1],
        1,
        (
            (1 / symbolx**2 + 1 / symbolx + 1 + symbolx + symbolx**2)
            * (1 / symboly**2 + 1 / symboly + 1 + symboly + symboly**2)
        ).expand(modulus=2),
    )
    for n in count(1):
        s = [int(d, 2) for d in bin(n)[2:].split("00") if d != ""]
        g = (g * f).expand(modulus=2)
        if len(s) == 1:
            blist.append(g.subs([(symbolx, 1), (symboly, 1)]))
        else:
            blist.append(prod(blist[d] for d in s))
        yield blist[-1]


def A248587_gen():  # generator of terms
    for i in count(3):
        n = i**3
        p3 = prevprime(n // 4)
        p2, p4 = prevprime(p3), nextprime(p3)
        p1 = prevprime(p2)
        q = p1 + p2 + p3 + p4
        while q <= n:
            if q == n:
                yield p1
            p1, p2, p3, p4 = p2, p3, p4, nextprime(p4)
            q = p1 + p2 + p3 + p4


def A248705_gen():  # generator of terms
    x, m = 0, [6, -6, 1, 0]
    while True:
        for i in range(3):
            m[i + 1] += m[i]
        xn = prod(int(d) for d in str(m[-1]))
        if xn > x:
            x = xn
            yield m[-1]


def A249586_gen():  # generator of terms
    yield 0
    m = [
        119750400,
        -658627200,
        1546776000,
        -2020606560,
        1602266400,
        -789354720,
        237304980,
        -40965390,
        3576156,
        -120849,
        784,
        0,
        0,
    ]
    while True:
        for i in range(12):
            m[i + 1] += m[i]
        yield m[-1]


def A350037(n):
    return pow(n, 2, (m := isqrt(n)) + int(4 * n >= (2 * m + 1) ** 2))


def A350046_gen():  # generator of terms
    f = Counter()
    for m in count(2):
        f += Counter(factorint(m))
        e = sorted(f.items())
        if all(
            d <= 1 or isprime(d)
            for d in (abs(e[i + 1][1] - e[i][1]) for i in range(len(e) - 1))
        ):
            yield m


def A249610_gen():  # generator of terms
    m = [48, -56, 13, 1]
    while True:
        for i in range(3):
            m[i + 1] += m[i]
        if isprime(m[-1]):
            yield m[-1]


def A249627(n):
    return min(fs := factorint((10**n - 1) // 9)) * max(fs)


def A249875_gen():  # generator of terms
    x = 1
    while True:
        yield 2 * sum(divmod(isqrt(2 * x), 2)) ** 2 + x
        x *= 4


def A251853_gen():
    (
        int("".join(d))
        for d in product("02468", repeat=4)
        if not sum(int(y) for y in str(sum(int(x) for x in d))) % 2
    )


def A253295_gen():  # generator of terms
    yield 8
    b = 8
    while True:
        b = int("".join((str(e) + str(p) for p, e in sorted(factorint(b).items()))))
        yield b


def A253549(n):
    p = prime(n)
    for b in range(2, 17):
        x, y, z = p, 0, 1
        while x >= b:
            x, r = divmod(x, b)
            y += r * z
            z *= 16
        y += x * z
        if isprime(y):
            return y


def A253575_gen(startvalue=1):
    return (
        n
        for n in count(max(startvalue, 1))
        if set(str(n)) & set(str(n**6)) == set() and isprime(n)
    )


def A253578_gen(startvalue=1):
    return (
        n
        for n in count(max(startvalue, 1))
        if set(str(n)) & set(str(n**10)) == set() and isprime(n)
    )


def A253671_gen():  # generator of terms
    yield 1
    blist, l1, l2 = (0, 1), 1, 1
    while True:
        l2, l1 = l1, (blist := tuple(accumulate(reversed(blist), initial=0)))[-1]
        yield l1 // l2


def A253769(n):
    return (lambda m, p: 2 * sum(p // k for k in range(1, m + 1)) - m * m)(
        isqrt(prime(n)), prime(n)
    )


def A253912_gen():
    return (n for n in (i**4 for i in range(10**6)) if isprime(int(str(n)[::-1])))


def A254058(n):
    b, a1, a2, t = 1, 0, n, 2**n
    while b < t:
        a2 += 1
        a1 += 1
        b = (b * a2) // a1
    return a2


def A254625_gen():  # generator of terms
    c0, c1, c2 = 1, 8, 27
    for n in count(1):
        if max(c0, c1, c2) < n:
            yield n
        c0, c1, c2 = c1, c2, A007913(n + 3) ** 3


def A254648_gen(startvalue=10):  # generator of terms
    for n in count(max(startvalue, 10)):
        m = str(n**2)
        for a in combinations(range(1, len(m)), 2):
            x, y, z = int(m[: a[0]]), int(m[a[0] : a[1]]), int(m[a[1] :])
            if y != 0 and z != 0 and x + y + z == n:
                yield n
                break


def A254746_gen():  # generator of terms
    yield 1
    c, s, s2 = {}, 2, 4
    for n in count(2):
        for p, e in factorint(4 * n - 2).items():
            if p in c:
                c[p] += e
            else:
                c[p] = e
        for p, e in factorint(n + 1).items():
            if c[p] == e:
                del c[p]
            else:
                c[p] -= e
        if n == s2:
            d, ps = 1, prime(s)
            for p, e in c.items():
                d = (d * pow(p, e, ps)) % ps
            yield d
            s2 += 2 * s + 1
            s += 1


def A254999_gen():
    return (
        n
        for n, m in (
            (4 * k + 2, divisor_sigma_mod(4 * k + 2, 4 * k + 2)) for k in count(0)
        )
        if m and not n % m
    )


def A255400(n):
    f, i, s = 1, 0, re.compile("[0-9]*[1-9]0{" + str(n) + "}[1-9][0-9]*")
    while s.match(str(f) + "1") is None:
        i += 1
        f *= i
    return i


def A255911_gen():  # generator of terms
    blist, c, m = [], 0, 0
    for i in count(1):
        d = divisor_count(i)
        if d > m:
            m = d
            blist.append(i)
            for j in range(c - 1, -1, -1):
                q, r = divmod(i, blist[j])
                if not r:
                    yield q
                    break
            c += 1


def A256370_gen(startvalue=1):
    return (
        n
        for n in count(max(startvalue, 1))
        if is_prime(5 * n * (n * (n * (n + 8) + 36) + 80) + 354)
    )


def A256969_gen():  # generator of terms
    c, bn, bd = 0, 1, 1
    for k in count(1):
        p = prime(k)
        bn *= p
        bd *= p - 1
        while bn > c * bd:
            yield k
            c += 1


def A256985(n):
    ilist, k = [1] * (n + 1), 1
    jlist = [d % 10 for d in accumulate(ilist)]
    jlist = [jlist[-1]] + jlist[:-1]
    while ilist != jlist:
        k += 1
        jlist = [d % 10 for d in accumulate(jlist)]
        jlist = [jlist[-1]] + jlist[:-1]
    return k


def A257002_gen():
    return (p for p in (prime(n) for n in count(1)) if pow(p, p, p + 2) == p)


def A258231_gen(startvalue=0):
    return (
        n
        for n in count(max(startvalue, 0))
        if n % 10 and set(str(n)) == set(str(n**2))
    )


def A258456_gen(startvalue=1):
    return (
        i
        for i in count(max(startvalue, 1))
        if not integer_nthroot(i, 4)[1] and divisor_count(i) % 4
    )


def A258786_gen(startvalue=1):
    return (
        n
        for n in count(max(startvalue, 1))
        if sorted(str(n)) == sorted(str(sum(antidivisors(n))))
    )


def A260031(n):
    return int(gmpy2digits(n**n, 12).rstrip("0")[-1], 12)


def A260375_gen():  # generator of terms
    yield 0
    g = 1
    for i in count(1):
        g *= i
        s = isqrt(g)
        t = g - s**2
        if is_square(t if t - s <= 0 else 2 * s + 1 - t):
            yield i


def A260534_T(n, k):
    return sum(0 if ~(k - j) & j else n**j for j in range(k + 1))


def A260597_gen():  # generator of terms
    bset = set()
    for n in count(1):
        m = primefactors(
            int(
                "".join(
                    [str(d) for d in range(1, n + 1)]
                    + [str(d) for d in range(n - 1, 0, -1)]
                )
            )
        )
        for p in m:
            if not p in bset:
                bset.add(p)
                yield p


def A260796_gen(startvalue=1):
    return (
        n
        for n in count(max(startvalue, 1))
        if isprime(sum(int(d) for d in str(prime(n)) + str(prime(n + 1))))
    )


def A261175_gen():  # generator of terms
    n = 1
    for i in count(0):
        n *= i**i
        yield len(str(n))


def A261534_gen():  # generator of terms
    for m in pal_gen(3):
        n = int(gmpy2digits(m, 3))
        if n > 0 and not isprime(n) and (s := str(divisor_prod(n))) == s[::-1]:
            yield n


def A261593_gen():  # generator of terms
    for l in count(10):
        for c in multiset_permutations("0" * (l - 10) + "1" * 10, l):
            n = 2 * int("1" + "".join(c), 2)
            if sum(int(d) for d in format(n * (n + 2), "b")) == 11:
                yield n + 1


def A261694_gen():  # generator of terms
    a, b, = (
        0,
        1,
    )
    while True:
        yield a
        a, b = b, (a + b) % 21


def A261749_gen(startvalue=1):
    return (
        n
        for n in count(max(startvalue, 1))
        if sorted(str(n**2)) == sorted(str((n + 2) ** 2))
    )


def A262776(n):
    if n < 2:
        return 0
    a, b, m = 0, 1, factorial(fibonacci(n))
    for i in range(factorial(n) - 1):
        b, a = (b + a) % m, b
    return b


def A350577_gen():  # generator of terms
    p = 2
    while True:
        s = bin(p)[2:]
        c, l = 0, len(s)
        for i in range(l):
            c += int(s[l - i - 1])
            if 2 * c <= i:
                break
        else:
            yield p
        p = nextprime(p)


def A262814_gen(startvalue=1):  # generator of terms
    for k in count(max(startvalue, 1)):
        n = k**k
        if not n % k:
            s = str(n)
            for i in range(len(s) - 1):
                s = s[1:] + s[0]
                if int(s) % k:
                    break
            else:
                yield k


def A263400(n):
    b, a = fib2(n)
    s, m = gmpy2digits(b), n
    while True:
        a, b, m = b, a + b, m + 1
        t = gmpy2digits(b)
        if b > a and s in t:
            return m


def A263457_gen(startvalue=1):  # generator of terms
    s = 0
    for n in count(1):
        s += divisor_count(n)
        if is_square(8 * s + 1):
            yield n


def A266001_gen():
    return (
        j
        for j in (
            int(format(i, "b"), 3) + (3**n - 1) // 2
            for n in range(1, 10)
            for i in range(2**n)
        )
        if "0" not in gmpy2digits(j, 4)
    )


def A267140(n):
    u, r, k, m = 2 * n + 1, 4 * n * (n + 1) + 1, 0, 2 * n + 1
    while True:
        if is_square(8 * m + r):
            return m
        k += 2
        m += u + k


def A267767_gen():
    return (int(s, 7) for s in (str(i**2) for i in count(0)) if max(s) < "7")


def A267818_gen():
    return (
        int(d, 4)
        for d in (str(i**2) for i in count(1))
        if max(d) < "4" and isprime(int(d, 4))
    )


def A267982_gen():  # generator of terms
    yield 0
    b = 4
    for n in count(1):
        yield b
        b = b * 4 * (n + 1) * (2 * n + 1) ** 2 // (n * (n + 2) ** 2)


def A268045(n):
    if n == 0:
        return 2
    flist, k = Counter(factorint((n + 2) * (n + 1) // 2)), 2
    while max(flist.values()) >= 2:
        k += 1
        flist += Counter(factorint(n + k))
        flist -= Counter(factorint(k))
    return k


def A268140(n):
    p, n2 = 2, 2**n + 1
    while True:
        for i in range(1, n2):
            if isprime(p + i):
                p += i
                break
        else:
            return p


def A268304_gen():  # generator of terms
    b, m1, m2 = (
        15,
        [
            21941965946880,
            -54854914867200,
            49244258396160,
            -19011472727040,
            2933960577120,
            -126898662960,
            771887070,
            385943535,
            385945560,
        ],
        [
            10569646080,
            -25763512320,
            22419210240,
            -8309145600,
            1209116160,
            -46992960,
            415800,
            311850,
            311850,
        ],
    )
    for n in count(0):
        if b % 8 == 7:
            yield 2 * n + 1
        b = b * m1[-1] // m2[-1]
        for i in range(8):
            m1[i + 1] += m1[i]
            m2[i + 1] += m2[i]


def A269903_gen():  # generator of terms
    p = 1
    for i in count(2):
        p = (p * prime(i)) % 8
        if p == 7:
            yield i


def A269927_gen():  # generator of terms
    yield 0
    blist, c = [0], 1
    while True:
        ylist = [1 - d for d in blist]
        zlist = list(blist)
        for i in blist:
            if i:
                zlist += blist
            else:
                zlist += ylist
        blist = zlist
        yield from blist[c:]
        c = len(blist)


def A270440_gen():  # generator of terms
    b = 8
    for n in count(0):
        q, r = integer_nthroot(b + 1, 2)
        yield (q + 1) // 2 + (0 if r else 1)
        b = b * 2 * (2 * n + 1) // (n + 1)


def A271327_gen(startvalue=1):  # generator of terms
    for n in count(max(startvalue, 1)):
        p, a, b = prime(n), 1, 1
        for i in range(n):
            if not a:
                yield n
                break
            a, b = b, (a + b) % p


def A271899_gen():  # generator of terms
    m = [88, -128, 61, -8] + [1] * 5
    while True:
        yield m[-1]
        for i in range(8):
            m[i + 1] += m[i]


def A272383_gen(startvalue=78):  # generator of terms
    for i in count(max(startvalue + (78 - startvalue % 78) % 78, 78), 78):
        for d in divisors(i):
            if d not in (1, 2, 6, 78) and isprime(d + 1):
                break
        else:
            yield i


def A272673_gen():
    return chain(
        (0,),
        (
            int(str(m**2)[1:]) if sum(int(d) for d in str(m**2)[1:]) != 1 else 0
            for m in count(4)
            if str(m**2)[0] == "1"
        ),
    )


def A272890_gen(startvalue=3):
    return (
        n
        for n in count(max(startvalue, 3))
        if sum(Fraction(n, a) for a in antidivisors(n)).denominator == 1
    )


def A274951_gen():  # generator of terms
    a, b = 8, 12
    yield from [a, b]
    for i in count(0):
        c, d = divmod(b**2, a)
        a, b = b, c + (0 if 2 * d < a else 1)
        yield b


def A275465(n):
    p = min(primefactors(n))
    return p ** (n // p)


def A275544_gen():  # generator of terms
    yield 1
    c = [Fraction(0, 1)]
    while True:
        c = set(e for d in c for e in (3 * d + 1, d / 2))
        yield len(c)


def A275628_gen():  # generator of terms
    a, b = 31, 51
    yield from [a, b]
    for i in count(0):
        c, d = divmod(b**2, a)
        a, b = b, c + (0 if 2 * d < a else 1)
        yield b


def A276389_gen():  # generator of terms
    yield 0
    m = 1
    for n in count(1):
        m *= n
        s, h = str(m), hex(m)
        if not len(s) - len(s.rstrip("0")) + len(h.rstrip("0")) - len(h):
            yield n


def A276460_gen():  # generator of terms
    yield 0
    for m in count(0):
        k = m**2 + 1
        for d in divisors(k):
            if d > m:
                yield k
                break
            if not is_square(k // d - d):
                break


def A276756_gen():
    return chain(
        (1,),
        (
            n
            for n in count(2)
            if max(factorint(n).values()) <= 1
            and sum(Fraction(p, 10 ** len(str(p))) for p in primefactors(n)).denominator
            == 1
        ),
    )


def A277692(n):
    return (
        sum(1 for c in divisors(n - 1) if c < n - 1 and not (n * (n - 1) // 2) % c)
        if n != 2
        else 1
    )


def A277937(n):
    return sum(1 for d in bin(n)[2:].split("0") if len(d) == 1)


@lru_cache(maxsize=None)
def A278049(n):
    if n == 0:
        return -1
    c, j = 0, 2
    k1 = n // j
    while k1 > 1:
        j2 = n // k1 + 1
        c += (j2 - j) * (2 * A278049(k1) - 1) // 3
        j, k1 = j2, n // j2
    return 3 * (n * (n - 1) - c + j) // 2 - 1


def A280056(n):
    return (n**2 - (n % 2)) * (n - 1) * (n - 2) // 2


def A280660(n):
    m, k, l = 10**n, 1, 2
    while True:
        if 2 * str(l).count("9") >= n:
            return k
        k += 1
        l = (l * 2) % m


def A280717_gen():  # generator of terms
    yield 3
    n = 3
    while True:
        for i in range(1, n // 2 + 1):
            j = i**2 + n * (n - i)
            if isprime(j):
                n = j
                yield n
                break


def A286328(n):
    p, area = prime(n), 0
    k, q, kq = (p + 1) // 2, (p**2 - 1) // 2, (p - 1) * (p + 1) ** 2 // 4
    while True:
        area += kq
        if is_square(area):
            return k
        k += 1
        kq += q


def A287298(n):  # assumes 2 <= n <= 62
    m = isqrt(mpz("".join(gmpy2digits(i, n) for i in range(n - 1, -1, -1)), n))
    m2 = m**2
    d = gmpy2digits(m2, n)
    while len(set(d)) < len(d):
        m -= 1
        m2 -= 2 * m + 1
        d = gmpy2digits(m2, n)
    return m2


def A287609_gen():  # generator of terms
    p, q, r = 2, 3, 5
    while True:
        n = p * (q + r) + q * r
        m = n // 3
        pm, nm = prevprime(m), nextprime(m)
        k = n - pm - nm
        if isprime(m):
            if m == k:
                yield n
        else:
            if nextprime(nm) == k or prevprime(pm) == k:
                yield n
        p, q, r = q, r, nextprime(r)


def A287686_gen():  # generator of terms
    p2, q2, r2, r = 4, 9, 25, 5
    while True:
        n = p2 + q2 + r2
        m = n // 3
        pm, nm = prevprime(m), nextprime(m)
        k = n - pm - nm
        if isprime(m):
            if m == k:
                yield n
        else:
            if nextprime(nm) == k or prevprime(pm) == k:
                yield n
        s = nextprime(r)
        p2, q2, r2, r = q2, r2, s**2, s


def A288507(n):
    k, p, q = 1, 2, 3
    while True:
        if sum(factorint(q - p).values()) == n and sum(factorint(q + p).values()) == n:
            return k
        k += 1
        p, q = q, nextprime(q)


def A289829_gen(startvalue=0):  # generator of terms
    a, b = integer_nthroot(startvalue, 2)
    for n in count(max(a + (1 - int(b)), 0)):
        m = n**2 - 1
        for d in divisors(m):
            if d * d >= m:
                break
            r = m // d
            if not r % 2:
                r = r // 2
                if not isprime(r):
                    p, q = prevprime(r), nextprime(r)
                    if m == (q - p) * (q + p):
                        yield n**2
                        break


def A291175_gen():  # generator of terms
    a, b, c = 1, 1, 2
    for n in count(3):
        if c == a + b:
            yield n
        a, b, c = b, c, reduced_totient(n + 1)


def A291199_gen():  # generator of terms
    p = 3
    while True:
        if is_square(8 * (p - 1) * totient((p + 1) // 2) + 1):
            yield p
        p = nextprime(p)


def A292995(n):
    return sum(int(d) for d in str(3**n)) // 9


def A294092_gen():  # generator of terms
    m = 59
    for k in count(119, 120):
        if pow(2, m, k) == 1 and pow(3, m, k) == 1 and pow(5, m, k) == 1:
            yield k
        m += 60


def A295430(n):
    m = 2 * n
    while True:
        if str(m)[0] == "3":
            return m
        m += n


def A295900_gen(startvalue=1):
    return (n for n in count(max(startvalue, 1)) if "2357" in str(n**3))


def A296516(n):
    P, Q = {(1, 0)}, {(0, 1)}
    for _ in range(n):
        P, Q = P | Q, set((p[0] + q[0], p[1] + q[1]) for p in P for q in Q)
    return len(Q)


def A297624_gen():  # generator of terms
    b, c, aflag = 1, 2, False
    for k in count(1):
        cflag = isprime(c)
        if aflag and cflag:
            yield k
        b, c, aflag = b + c, b + 2 * c, cflag


def A297815(n):
    f = factorial(n)
    return sum(
        f // prod(factorial(d.count(a)) for a in set(d))
        for d in combinations_with_replacement(range(1, 10), n)
        if prod(d) == sum(d)
    )


def A298077_gen():
    return (
        m
        for m in (n * (n + 1) for n in count(3))
        if prevprime(m // 2) + nextprime(m // 2) == m
    )


def A298940(n):
    if n == 1:
        return 1
    try:
        return discrete_log(3**n - 2, -1, 3)
    except ValueError:
        return 0


def A299300_gen():  # generator of terms
    p, d, n, r = 2, -1, 0, False
    while True:
        pn, k = p - n, d if r else -d
        if 0 < k <= pn:
            yield n + k
        d += -pn if r else pn
        r, n, p = not r, p, nextprime(p)


def A300817(n):
    p, n2 = 2, n**2
    if n % 2:
        return 2 if isprime(2 + n2) else 0
    while not isprime(p + n2):
        p = nextprime(p)
    return p


def A300902_gen():  # generator of terms
    yield 1
    m = 1
    for n in count(1):
        m *= n
        yield m
        if isprime(n):
            m //= n


def A302292(n):
    s = set()
    for i in range(1, (n + 3) // 2):
        for j in divisors(i):
            for k in divisors(n - i):
                if j != k:
                    s.add((min(j, k), max(j, k)))
    return divisor_count(n) + 2 * len(s) - 1


def A302293(n):
    s = set()
    for i in range(1, n):
        for j in divisors(i):
            if integer_nthroot(j, 2)[1]:
                for k in divisors(n - i):
                    s.add((j, k))
    return len(s)


def A304290_gen(startvalue=0):
    return (k for k in count(max(startvalue, 0)) if str(k - 1) in str(k**2))


def A305378(n):
    m, tlist, s = 2 * n + 1, [1, 2, 4], 0
    while tlist[-1] + tlist[-2] + tlist[-3] <= m:
        tlist.append(tlist[-1] + tlist[-2] + tlist[-3])
    for d in tlist[::-1]:
        s *= 2
        if d <= m:
            s += 1
            m -= d
    return s


def A305884_gen():  # generator of terms
    blist, n, m = [], 1, 1
    while True:
        for l in range(1, len(blist) + 1):
            for d in multiset_combinations(blist, l):
                if integer_nthroot(sum(d) + m, 2)[1]:
                    break
            else:
                continue
            break
        else:
            blist.append(m)
            yield m
            continue
        n += 1
        m += 2 * n - 1


def A306043_gen():  # generator of terms
    blist, n, m = [], 1, 1
    while True:
        for l in range(1, len(blist) + 1):
            for d in combinations(blist, l):
                if integer_nthroot(sum(d) + m, 2)[1]:
                    break
            else:
                continue
            break
        else:
            blist.append(m)
            yield m
        n += 1
        m += 2 * n - 1


def A306384(n):
    mset, m, c = set(), n, 0
    while True:
        if m == 1 or m == 0 or m == 5:
            return c
        m = int(
            "0"
            + "".join(
                d
                for d in split(
                    "(0+)|(1+)|(2+)|(3+)|(4+)|(5+)|(6+)|(7+)|(8+)|(9+)", str(2 * m)
                )
                if d != "" and d != None and len(d) == 1
            )
        )
        if m in mset:
            return -1
        mset.add(m)
        c += 1


def A306540(n):
    if n == 1 or n == 10:
        return 1
    k, nk = 1, n
    while True:
        s = str(nk)
        if s[:2] == "99" or s[:3] == "100":
            return k
        k += 1
        nk *= n


def A306572_gen():
    return (
        n
        for n, p in enumerate(primepi(k) for k in count(0))
        if n > 0 and n % 10 ** len(str(p)) == p
    )


def A307636_gen():
    return filter(
        lambda n: all(
            len(set(s[0]) & set(s[1])) == 0
            for s in combinations((str(d) for d in divisors(n, generator=True)), 2)
        ),
        count(1),
    )


def A308438(n):
    l, p = 1, nextprime(n)
    while True:
        q = nextprime(p)
        if q - p == 2 * n:
            return p
        p = q
        if p >= (n + 1) * l:
            l *= 10
            p = nextprime(n * l)


def A308439(n):
    return min(
        primefactors(
            1 + prod(prime(i + 1) for i, j in enumerate(bin(n)[:1:-1]) if j == "1")
        )
    )


def A308575(n):
    n2, t1 = 2 ** (n - 1), 0
    k = n2 - 1
    kp = primepi(k)
    kp2 = primepi(k + n2) - kp
    while kp2 < kp or t1 >= kp:
        k += n2
        t1, t2 = kp, kp2
        kp2 = primepi(k + n2) - kp2
        kp = t2
    return 2 * kp


def A308777(n):
    if n == 1:
        return 1
    c, p = 0, prime(n)
    p2, x = p**2, [prevprime(p), p, nextprime(p)]
    while x[1] <= p2:
        if x[1] - x[0] == 2 or x[2] - x[1] == 2:
            c += 1
        x = x[1:] + [nextprime(x[2])]
    return c


def A308935(n):
    n2, m, m2 = (
        n**2 * (n**2 + 1),
        n + 1,
        ((n + 1) ** 2 * ((n + 1) ** 2 + 1)) % (n**2 * (n**2 + 1)),
    )
    while m2:
        m2, m = (m2 + 2 * (2 * m + 1) * (m**2 + m + 1)) % n2, (m + 1) % n2
    return m


def A309388_gen():  # generator of terms
    y, w = 1, 0
    while True:
        w += y
        z = 0
        for x in range(1, y + 1):
            z += x
            if is_square(8 * (w + z) + 1):
                break
        else:
            yield y
        y += 1


def A309387(n):
    return gcd(n**2, harmonic(n - 1).p)


def A309851_gen():
    return (m for m in (int(str(n) + str(2 * n - 1)) for n in count(1)) if isprime(m))


def A317977(n):
    m = 2**n - 1
    c = 4 % m
    for _ in range(n - 2):
        c = (c**2 - 2) % m
    return c


def A318157_gen():  # generator of terms
    for n in count(2):
        if not (isprime(n) or isprime(n + 1) or isprime(n + 2) or isprime(n + 3)):
            if isprime(4 * n + 5):
                yield 4 * n + 5
            if isprime(4 * n + 7):
                yield 4 * n + 7


def A318972(n):
    return (
        (7 * n + 1) // 4 if n % 4 == 1 else (7 * n - 1) // 4 if n % 4 == 3 else n // 2
    )


def A319228(n):
    c, b, b2, n10 = 0, 1, 3, 10**n
    while b <= n10:
        if isprime(b2):
            c += 1
        b += 1
        b2 += 2 * b
    return c


def A320909_gen(startvalue=1):
    return (
        n
        for n in count(max(startvalue, 1))
        if isprime(int(str(n**2)[::-1])) and isprime(int(str(n**3)[::-1]))
    )


def A320920(n):
    w, m = int(factorial(n)), n
    bc = [comb(n - 1, i) % w for i in range(n + 1)]
    while True:
        bc[n] = (bc[n - 1] + bc[n]) % w
        if bc[n] == 0:
            return m
        for i in range(n - 1, 0, -1):
            bc[i] = (bc[i - 1] + bc[i]) % w
        m += 1


def A321685(n):
    return Matrix(n, n, [composite(i) for i in range(1, n**2 + 1)]).det()


def A322250(n):
    s = bin(2 * n - 1)[2:].rstrip("1")
    return int(s, 2) if s != "" else 1


def A322743(n):
    i = 4 if n <= 1 else 2**n + 1
    j = 1 if n <= 2 else 2
    while True:
        if not isprime(i):
            c = 0
            for m in range(len(bin(i)) - 2):
                if isprime(i ^ (2**m)):
                    c += 1
                if c > n:
                    break
            if c == n:
                return i
        i += j


def A323026_gen():
    return (
        n
        for n in (
            int("".join(s)) for l in count(9) for s in permutations("123456789", l)
        )
        if isprime(n - 1) and isprime(n + 1)
    )


def A323062_gen(startvalue=1):
    return (
        k
        for k in count(max(startvalue, 1))
        if (2 * isqrt(2 ** (2 * k - 1)) - 1) ** 2 > 1 + 4 * (2 ** (2 * k - 1) - 2**k)
    )


def A323278_gen():  # generator of terms
    p, nmax = 2, -1
    while True:
        n = divisor_count(p**2 - 1)
        if n > nmax:
            nmax = n
            yield p**2 - 1
        p = nextprime(p)


def A324309(n):
    m, k = 2, 2**n
    while True:
        s = str(k)
        for i in range(1, len(s)):
            if s[i] == s[i - 1]:
                return m
        m += 1
        if m % 10 == 0:
            m += 1
        k = m**n


def A328131(n):
    s, tlist = str(n), ("2468", "369", "468", "5", "689", "7", "8", "9")
    dset = set(
        "0"
        + "".join(
            t if t[0] in s and sum(s.count(d) for d in t) > 1 else "" for t in tlist
        )
    )
    return int("0" + "".join(d for d in s if d not in dset))


def A328375_gen(startvalue=0):
    return (k for k in count(max(startvalue, 0)) if "777" in str(2**k))


def A328947_geh():
    return (n for n in (int(bin(m)[2:]) for m in count(0)) if not n % 7)


def A330243_gen(startvalue=0):
    return (n for n in count(0) if str(2**n)[0] == "7")


@lru_cache(maxsize=None)
def A330503(n):
    if n == 0:
        return 0
    c, j = 0, 2
    k1 = n // j
    while k1 > 1:
        j2 = n // k1 + 1
        c += (j2 - j) * (2 * A330503(k1) // (k1 + 1) - 1)
        j, k1 = j2, n // j2
    return (n + 1) * (n * (n - 1) - c + j) // 2


def A331988_T(n, k):  # compute T(n,k)
    if k == 1:
        count = 1
        for i in range(1, n):
            count *= i + 1
        return count
    ntuple, count = tuple(range(1, n + 1)), 0
    for s in combinations_with_replacement(permutations(ntuple, n), k - 2):
        t = list(ntuple)
        for d in s:
            for i in range(n):
                t[i] += d[i]
        t.sort()
        w = 1
        for i in range(n):
            w *= (n - i) + t[i]
        if w > count:
            count = w
    return count


def A332842(n):
    m, k = 1, 1
    for i in range(2, n + 1):
        k *= i
        m *= k
    return int(str(m)[0])


def A333445_T(n, k):  # compute T(n,k)
    c, l = 1, list(range(1, k * n + 1, k))
    lt = list(l)
    for i in range(n):
        for j in range(1, k):
            lt[i] += l[i] + j
        c *= lt[i]
    return c


def A333596_gen():
    return accumulate(A334841(n) for n in count(0))


def A333975_gen():  # generator of terms
    yield from [1, 2]
    blist, bset, m = [1, 2], set(), 2
    for i in count(3):
        for j in range(i - 2):
            bset.add(m | blist[j])
        m += 1
        while m in bset:
            m += 1
        blist.append(m)
        yield m


def A334042(n):
    return 2 ** (len(bin(n**2)) - 2) - 1 - n**2


def A334076(n):
    m = n | (2 * n)
    return 0 if n == 0 else 2 ** (len(bin(m)) - 2) - 1 - m


def A334116_helper(w, m):
    a, p, s, vv = m, 0, w, []
    while a < 2 * m:
        p += 1
        s = S.One / (s - floor(s))
        a = floor(s)
        if a < 2 * m:
            vv.append(a)
    j = (p - 1) // 2
    v = [0, 1, 1] if p % 2 else [1, 0, vv[j]]
    for i in range(j - 1, -1, -1):
        h = vv[i]
        v = [v[0] + h * v[2], v[2], 2 * h * v[0] + v[1] + h**2 * v[2]]
    return v


def A334116(n):
    w = sqrt(n)
    m = floor(w)
    if w == m:
        return n
    else:
        x, y, z = A334116_helper(w, m)
        if z % 2:
            x *= 2
        else:
            z //= 2
            y //= 2
        return (m + z) ** 2 + x + (x * m + y) // z


@lru_cache(maxsize=None)
def A334535(n):
    if n <= 2:
        return n
    i, a, b = 2, A334535(n - 1), A334535(n - 2)
    q = b
    while q >= n:
        i += 1
        q = A334535(n - i)
    return 2 * A334535(q) + a - b


def A335306(n):
    p = prime(n)
    for m in range(max(4, 2 * p - 4), p**2 + 1):
        if sum(primefactors(m)) == p:
            return m


def A335313(n):
    m = 2 ** (3 * 2**n)
    p = prevprime(m)
    while not isprime((p - 1) // 2):
        p = prevprime(p)
    return m - p


def A335940(n):
    if isprime(n):
        return n
    else:
        pf = primefactors(n)
        return max(pf) - min(pf)


def A336257_gen():  # generator of terms
    yield from [0, 1]
    c = 1
    for n in count(2):
        c = c * (4 * n - 2) // (n + 1)
        yield c % (2 * n + 1)


def A337098(n):
    k = 1
    while True:
        if n == sum(
            1
            for x in combinations((d**3 for d in divisors(k)), 4)
            if sum(x[:-1]) == x[-1]
        ):
            return k
        k += 1


def A337212(n):
    x, y, k, r, m = (3**n - 3) // 2, (3**n - 3) // 2, (n - 1) % 3, 3 ** (n - 1), 0
    while True:
        m += 1
        a, b = divmod(x, 3)
        x, k = a + k * r, (k + k - b) % 3
        if y == x:
            return m


def A339566_gen():  # generator of terms
    p = 2
    while True:
        if int(bin(p)[2:]) % p == 1:
            yield p
        p = nextprime(p)


def A340290_gen():
    return (
        int(s)
        for s in (gmpy2digits(prime(i), 3) for i in count(1))
        if isprime(int(s, 4))
    )


def A340479(n):
    s = str(n)
    return int(s[::-1]) + sum(int(d) for d in s)


def A340768(n):
    return divisors(composite(n))[2]


def A350093_gen():  # generator of terms
    a, b = divisor_count(1), divisor_count(2)
    for k in count(1):
        if a + b == 6:
            yield k
        a, b = b, divisor_count(k + 2)


def A340876_gen():  # generator of terms
    p, q, r, s = 2, 3, 5, 7
    for k in count(1):
        if pow(p, q, s) == r:
            yield k
        p, q, r, s = q, r, s, nextprime(s)


def A341115_gen():  # generator of terms
    m, l, n = 2**101, 2**101 + 1, 10**100
    for k in count(1):
        if pow(10, n, l) == l - 1:
            yield k
        l += m


def A341276(n):
    return (
        1
        + 3 * n * (n + 1)
        - 2 * sum(n // k for k in range(1, isqrt(n) + 1))
        + isqrt(n) ** 2
    )


def A341700(n):
    s, m = 0, nextprime(n)
    while m <= 2 * n:
        s += m
        m = nextprime(m)
    return s


def A342025(n):
    f = factorint(n)
    return int(
        sum(b for a, b in f.items() if a % 4 == 3)
        == sum(b for a, b in f.items() if a % 4 == 1)
    )


def A342081_gen(startvalue=1):
    return (
        n
        for n in count(max(startvalue, 1))
        if len([p for p in primefactors(n) if p > 2 and p * p <= n]) == 0
    )


def A342082_gen(startvalue=1):
    return (
        n
        for n in count(max(startvalue, 1))
        if len([p for p in primefactors(n) if p > 2 and p * p <= n]) > 0
    )


def A342175(n):
    m = composite(n)
    k = m + 1
    while gcd(k, m) != 1 or isprime(k):
        k += 1
    return k - m


def A342308_gen(startvalue=1):
    return (
        n
        for n in count(max(startvalue, 1))
        if set(str(n**5)) == {"1", "2", "3", "4", "5", "6", "7", "8", "9"}
    )


def A342403(n):
    return 1 if n == 1 else -sum(d * A342403(d) for d in divisors(n) if d < n)


def A342601_gen():  # generator of terms
    m, s = 2, str(2**10)
    for k in count(1):
        if s in str(m):
            yield k
        m *= 2


def A342851_gen(startvalue=0):
    return (n for n in count(max(startvalue, 0)) if n == 0 or n % 10)


def A342871(n):
    c = 0
    for k in range(1, n + 1):
        m = integer_nthroot(n, k)[0]
        if m == 1:
            return c + n - k + 1
        else:
            c += m
    return c


def A342892(n):
    s = bin(n)[2:]
    m = len(s)
    i = s[::-1].find("1")
    return 1 - int(s[m - i - 3]) if m - i - 3 >= 0 else 1


def A342906(n):
    return 2 ** (2 * n - 2) - catalan(n)


def A343128_gen(startvalue=1):
    return (
        n
        for n in count(max(startvalue, 1))
        if n % 2 and n % 5 and prime(prime(prime(n))) % 10 ** (len(str(n))) == n
    )


def A343145(n):
    k = 1
    while True:
        m = k
        for _ in range(n):
            m = prime(m)
        if m % 10 ** (len(str(k))) == k:
            return k
        k += 1
        while not (k % 2 and k % 5):
            k += 1


@lru_cache(maxsize=None)
def A343493(n):
    return 1 - sum(A343493(d - 1) for d in divisors(n) if d < n)


def A343507(n):
    k, f = 0, Fraction(1, int(factorial(n)) ** 2)
    while f.denominator != 1:
        k += 1
        f *= Fraction(2 * k * (2 * k - 1), (k + n) ** 2)
    return k


def A343536_gen():  # generator of terms
    s = "1"
    for k in count(1):
        if str(k**2) in s:
            yield k
        s += str(k + 1)


def A343727_gen():
    return (
        n
        for n in (int("".join(d)) for l in count(1) for d in product("13579", repeat=l))
        if set(str(n**2)[:-1]) <= set("02468")
    )


def A343731_gen():  # generator of terms
    yield 0
    c = 0
    for n in count(2):
        x = prod(n * d + 1 for d in factorint(n).values())
        if x > c:
            c = x
            yield n


def A343780(n):
    q = 1
    while True:
        s, c = [1] * n + [0] * n, 0
        for i in range(n):
            c = (c + q) % (2 * n - i)
            if s[c]:
                break
            s = s[:c] + s[c + 1 :]
        else:
            return q + 1
        q += 1


def A343802(n):
    s, c = 0, 0
    while s < 10**n:
        c += 1
        s += totient(c)
    return c


def A344013_gen():  # generator of terms
    yield 1
    b = 1
    while True:
        b = sum(ord(s) - 96 for s in unidecode(num2words(b, lang="fr")) if s.isalpha())
        yield b


def A344421(n):
    return sum(
        floor(n * sin(x * pi / n)) - int((n * sin(x * pi / n)).is_integer == True)
        for x in range(1, n)
    )


def A344478(n):
    fs = factorint(n)
    return 0 if len(fs) == 0 or max(fs.values()) > 1 else len(fs)


def A344856(n):
    return prime(n) ^ n**2


def A344888(n):
    b, m = 2, n
    while True:
        m, x = divmod(m, b)
        m, y = divmod(m, b)
        while m > 0:
            m, z = divmod(m, b)
            if z != x:
                break
            if m > 0:
                m, z = divmod(m, b)
                if z != y:
                    break
            else:
                return b
        else:
            return b
        b += 1
        m = n


def A344949(n):
    return min(d[1] ** 2 for d in diop_DN(4 * n + 2, 1)) // 4


def A344985(n):
    s, c, b = bin(n)[2:], 0, 0
    for x in s:
        b += 1 if x == "1" else -1
        c += abs(b)
    return c


def A345299(n):
    return sum(p ** primepi(p) for p in primefactors(n))


def A345301(n):
    return sum(p ** primepi(n // p) for p in primefactors(n))


def A345348_gen():
    return (
        n
        for n in (m * (m + 1) // 2 for m in count(0))
        if len(bin(n)) - 2 == 2 * bin(n).count("1")
    )


def A345420(n):
    return igcdex(5, prime(n))[0]


def A345696(n):
    zlist = [
        z
        for z in (igcdex(x, y) for x in range(1, n + 1) for y in range(1, n + 1))
        if z[2] == 1
    ]
    return pvariance(len(zlist) * (u**2 + v**2) for u, v, w in zlist)


def A345724(n):
    return pvariance(
        n**2 * (u + v)
        for u, v, w in (igcdex(x, y) for x in range(1, n + 1) for y in range(1, n + 1))
    )


def A345725(n):
    zlist = [
        z
        for z in (igcdex(x, y) for x in range(1, n + 1) for y in range(1, n + 1))
        if z[2] == 1
    ]
    return pvariance(len(zlist) * (u + v) for u, v, w in zlist)


def A346147_gen():  # generator of terms
    p, q = 2, 3
    while True:
        if isprime(p * q % (p + q)) and isprime(p * q // (p + q)):
            yield p
        p, q = q, nextprime(q)


def A346203(n):
    m, k, p, s = 1, 0, 1, str(n)
    while s not in str(m):
        k += 1
        p = nextprime(p)
        m *= p
    return k


def A346528(n):
    if n == 1:
        return 17
    a, b, k, k2, m, r, s = -6 * (n + 1) ** 2, (n + 1) ** 4, 2, 4, 1, 0, 0
    while 2 * m + a < 0 or m * (m + a) + b < 0:
        if isqrt(2 * m) - isqrt(m - 1) == n:
            r = m
        if s == 0 and isqrt(2 * m + 2) - isqrt(m) == n:
            s = m
        k += 1
        k2 += 2 * k - 1
        m = (k2 - 1) // 2
    return r - s


def A347274(n):
    return 1 if n == 1 else n**2 * (n**n - n) // (n - 1) ** 2


def A347275(n):
    return (
        2 * n + 1
        if n <= 1
        else 2 * (n + sum(n // k for k in range(1, isqrt(n) + 1))) - isqrt(n) ** 2 - 1
    )


def A347304(n):
    return factorial(n) // factorial(n // 2) // factorial(n // 3) // factorial(n // 6)


def A347314_gen():  # generator of terms
    yield 1
    nset, m, j = {1}, 2, 2
    for i in count(2):
        k = m
        while k == j or gcd(k, j) == 1 or k in nset:
            k += 1
        if i == k:
            yield i
        j = k + 1
        nset.add(k)
        while m in nset:
            m += 1


def A347815_gen():
    return (
        p
        for p in (prime(n) for n in count(3))
        if legendre_symbol(30, p) == legendre_symbol(105, p) == -1
    )


def A347816_gen():
    return (
        p
        for p in (prime(n) for n in count(3))
        if legendre_symbol(15, p) == legendre_symbol(85, p) == -1
    )


def A348017_gen(startvalue=0):
    return (
        k
        for k in count(max(startvalue, 0))
        if isprime((lambda x: x.p % x.q)(harmonic(k)))
    )


def A022510_gen():  # generator of terms
    yield 6
    l = "6"
    while True:
        l = "".join(
            str(len(d)) + d[0]
            for d in split("(0+|1+|2+|3+|4+|5+|6+|7+|8+|9+)", l[::-1])
            if d
        )
        yield int(l)


def A058994_gen():  # generator of terms
    m = 7
    for k in count(1):
        if isprime(int(str(m)[::-1])):
            yield k
        m *= 7


def A058995_gen():  # generator of terms
    m = 13
    for k in count(1):
        if isprime(int(str(m)[::-1])):
            yield k
        m *= 13


def A093502_gen():  # generator of terms
    yield 2
    p, q = 2, 1
    while True:
        r = p + q
        p, q = prime(r), r
        yield p


def A108860_gen(startvalue=1):
    return (
        n
        for n in count(max(startvalue, 1))
        if not sum(int(d) for d in str((2 * n) ** n)) % n
    )


def A109675_gen(startvalue=1):
    return (
        n
        for n in count(max(startvalue, 1))
        if not sum([int(d) for d in str(n**n - 1)]) % n
    )


def A112258_gen(startvalue=1):
    return (
        n for n in count(max(startvalue, 1)) if n % 10 and len(set(str(n**26))) < 10
    )


def A123911_gen():  # generator of terms
    plist = [0] + [prime(i) for i in range(1, 10)]
    for l in count(1):
        L = 10 ** (l - 1)
        H = 10 * L
        for c in combinations_with_replacement(range(1, 10), l):
            n = prod(plist[i] for i in c) + sum(c)
            if L <= n < H and sorted(int(d) for d in str(n)) == list(c):
                yield n


def A126703_gen(startvalue=1):
    return (n for n in count(max(startvalue, 1)) if isprime(pow(n, n, 10**n)))


def A137019_gen():
    return (
        n
        for n in (int("".join(d)) for l in count(1) for d in product("1279", repeat=l))
        if set(str(n**2)) <= set("1279")
    )


def A143992_gen(startvalue=2):
    return (
        n
        for n in count(max(startvalue, 2))
        if n != 4
        and not isprime(n)
        and str(sum(a * b for a, b in factorint(n).items())) in str(n)
    )


def A155012_gen():  # generator of terms
    a, b, a2, b2 = 0, 1, 2, 5
    while True:
        if isprime(b) and isprime(b2):
            yield b
        a, b, a2, b2 = b, a + b, b2, a2 + b2 - 2


def A175975_gen(startvalue=0):
    return (n for n in count(max(startvalue, 0)) if str(n**n).count("1") == 2)


def A246421_gen(startvalue=1):
    for n in count(max(startvalue, 1)):
        s = str(n)
        if not s.count("0"):
            s2 = sorted(s)
            if s2 == sorted(str(n + sum(int(d) for d in s))) and s2 == sorted(
                str(n + prod(int(d) for d in s))
            ):
                yield n


def A247047_gen(startvalue=1):
    return (
        n
        for n in count(max(startvalue, 1))
        if len(set(str(n**3))) == 3 and len(set(str(n**2))) == 2
    )


def A248135_gen(startvalue=1):
    for n in count(max(startvalue, 1)):
        if not isprime(n):
            a = sum([int(n * e / p) for p, e in factorint(n).items()]) if n > 1 else 0
            if not sum(a % i for i in range(1, a)) % n:
                yield n


def A255669_gen():  # generator of terms
    p1, p2, l = 2, 3, 10
    for n in count(0):
        p3 = nextprime(p2)
        if p3 >= l:  # this test is sufficient due to Bertrand-Chebyshev theorem
            l *= 10
        if not ((p2 % p1) * l + p3) % p1:
            yield p1
        p1, p2 = p2, p3


def A259630_gen():  # generator of terms
    bset, k = set(), 0
    while True:
        n, m = 0, 1
        k += m
        while n in bset or not isprime(k):
            n += 1
            k += m
            m *= 2
        bset.add(n)
        yield n


def A260097_gen(startvalue=11):  # generator of terms
    for n in count(max(startvalue, 11)):
        s = str(n)
        for l in range(1, len(s)):
            m = int(s[:l]) * int(s[l:])
            if m > 0 and n == divisor_sigma(m):
                yield n
                break


def A261459_gen(startvalue=0):
    return (
        k
        for k in count(max(startvalue, 0))
        if is_prime(int("1" * k + str(k * (k + 1) + 1) + "1" * k))
    )


def A264725_gen():  # generator of terms
    c, n, m, k = 3, 7, 29927007, 10**8
    while True:
        if isprime(n):
            yield c
        c += 8
        n = n * k + m


def A268511_gen(startvalue=1):  # generator of terms
    for n in count(max(startvalue + 1 - startvalue % 2, 1), 2):
        m = factorint(3**n + 5**n)
        for d in m:
            if d % 4 == 3 and m[d] % 2:
                break
        else:
            yield n


def A268517_gen():  # generator of terms
    yield 321
    a = 321
    for i in count(0):
        a = (
            ((a + 1 + (2 - i) % 3) % 10) * 100
            + ((a // 100 + 1 + (-i) % 3) % 10) * 10
            + ((a // 10 + 1 + (1 - i) % 3) % 10)
        )
        yield a


def A270538_gen():
    return (
        n**2
        for n in range(10**6)
        if n == sum(int(a) ** (b + 1) for b, a in enumerate(str(n**2)))
    )


def A276718_gen():  # generator of terms
    q = 0
    for i in count(1):
        s = str(i)
        q += Fraction(int(s[::-1]), 10 ** len(s))
        if q.denominator == 1:
            yield i


def A291340_gen():  # generator of terms
    yield 2
    p = 3
    while True:
        if is_square(8 * (p - 1) * totient((p - 1) // 2) + 1):
            yield p
        p = nextprime(p)


def A297710_gen():  # generator of terms
    for i in count(1):
        n = npartitions(i)
        s = [int(d) for d in str(n)]
        for j in range(len(s) - 1):
            if not (s[j] + s[j + 1]) % 2:
                break
        else:
            yield n


def A306666_gen(startvalue=1):
    return (
        n
        for n in count(max(startvalue, 1))
        if is_square(n * (n * (n * (n * (n - 9) + 33) - 58) + 42))
    )


def A318189(n):
    r, q = n % 2, 2
    while True:
        c, m = 0, q
        for i in range(n + 1):
            c += m
            m = prime(m)
        if is_prime(r + c):
            return q
        q = nextprime(q)


def A322047_gen(startvalue=0):
    return (n for n in count(max(startvalue, 0)) if "e" not in num2words(n, lang="fi"))


def A311481(n):
    return ord(unidecode.unidecode(num2words(n, to="ordinal")).lower()[0]) - 96


def A311482(n):
    return ord(unidecode.unidecode(num2words(n, lang="nl")).lower()[0]) - 96


def A311498(n):
    return ord(unidecode.unidecode(num2words(n, lang="fr")).lower()[0]) - 96


def A332242_gen():  # generator of terms
    n = 1
    for i in count(0):
        s = str(n)
        if len(s) - s.count("0") == i:
            yield i
        n *= i + 1


def A333122_gen():  # generator of terms
    plist = [2, 3, 5, 7, 11, 13]
    while True:
        m = plist[0] + plist[5]
        if m == plist[1] + plist[4]:
            yield m
        plist = plist[1:] + [nextprime(plist[-1])]


def A333390_gen(startvalue=1):
    return (
        n
        for n in count(max(startvalue, 1))
        if isprime(primorial(2 * n, nth=False) * 2**n - 1)
    )


def A335361_gen():  # generator of terms
    p = 2
    while True:
        f, g = factorial(p), 1
        for i in range(1, p + 1):
            g += f
            if isprime(g):
                break
        else:
            yield p
        p = nextprime(p)


def A337508_gen():  # generator of terms
    p = 11
    while True:
        s = str(p)
        l = len(s) // 2
        if not (isprime(int(s[:l])) or isprime(int(s[-l:]))):
            yield p
        p = nextprime(p)


def A339174_gen():  # generator of terms
    yield 2
    a = 2
    while True:
        c, b = 1, (a - 1) * a
        for k in count(1):
            c += b
            if isprime(c):
                yield k
                a = c
                break


def A340431_gen():  # generator of terms
    p = 2
    while True:
        q = nextprime(p)
        if q > p + 2:
            pq = p + q
            if pow(q, p, pq) == q and pow(p, q, pq) == p:
                yield p
        p = q


def A340466_gen():
    return (
        p
        for p in (prime(n) for n in count(1))
        if len(bin(p)) - 2 < 2 * bin(p).count("1") < 2 * len(bin(p)) - 4
    )


def A000201(n):
    return (n + isqrt(5 * n**2)) // 2


def A185381(n):
    return fibonacci((n + isqrt(5 * n**2)) // 2)


def A350678(n):
    return sum(fibonacci((i + isqrt(5 * i**2)) // 2) for i in range(n + 1))


def A342118_gen():  # generator of terms
    plist = [Fraction(1, totient(i)) for i in range(1, 7)]
    p = sum(plist)
    for k in count(1):
        if p.numerator == 1:
            yield k
        p -= plist[0]
        plist = plist[1:] + [Fraction(1, totient(k + 6))]
        p += plist[-1]


def A342221_gen(startvalue=1):  # generator of terms
    for k in count(max(startvalue, 1)):
        if k % 3 != 1:
            m, l = (10**k - 1) // 9, 2
            for i in range(k):
                if isprime(m + l):
                    break
                l *= 10
            else:
                yield k


def A342349_gen():
    p = 2
    while True:
        q = p**3
        C1, C2 = Counter(s := str(p)), Counter(str(q))
        if all(C1[d] <= C2[d] for d in s):
            yield q
        p = nextprime(p)


def A342503_gen(startvalue=1):
    return (
        k
        for k in count(max(startvalue, 1))
        if sum(k % i for i in range(1, k // 2 + 1) if gcd(i, k) == 1) % k == 0
    )


def A342809_gen(startvalue=1):
    return (
        k
        for k in count(max(startvalue, 1))
        if isprime(k - 1) and isprime(k // 5 + int(k % 5 > 2))
    )


def A343011_gen(startvalue=1):
    return (
        n
        for n in count(max(startvalue, 1))
        if (divisor_sigma(n, 0) * divisor_sigma(n, 2) - divisor_sigma(n, 1) ** 2)
        % divisor_sigma(n, 0) ** 2
        == 0
    )


def A343732_gen(startvalue=2):
    return (
        n
        for n in count(max(startvalue, 2))
        if len(factorint(prod(n * d + 1 for d in factorint(n).values()))) == 1
    )


def A344202_gen():  # generator of terms
    p = 5
    while True:
        if gcd(n_order(2, p), n_order(3, p)) == 1:
            yield p
        p = nextprime(p)


def A000040(n):
    return prime(n)


def A000079(n):
    return 2**n


def A000142(n):
    return factorial(n)


def A001222(n):
    return sum(factorint(n).values())


def A007318_T(n, k):
    return comb(n, k)


def A001221(n):
    return len(factorint(n))


def A001358_gen(startvalue=2):
    return (n for n in count(max(startvalue, 2)) if A001222(n) == 2)


def A000720(n):
    return primepi(n)


def A002110(n):
    return 1 if n == 0 else primorial(n)


def A034386(n):
    return 1 if n == 0 else primorial(n, nth=False)


def A008683(n):
    return mobius(n)


def A000032(n):
    return lucas(n)


def A000225(n):
    return (1 << n) - 1


def A002275(n):
    return (10**n - 1) // 9


def A005408(n):
    return 2 * n + 1


def A006530(n):
    return 1 if n == 1 else max(primefactors(n))


def A020639(n):
    return 1 if n == 1 else min(primefactors(n))


def A000984(n):
    return comb(2 * n, n)


def A000292(n):
    return comb(n + 2, 3)


def A000290(n):
    return n**2


def A000244(n):
    return 3**n


def A002378(n):
    return n * (n + 1)


def A005843(n):
    return 2 * n


def A000129_gen():  # generator of terms
    a, b = 0, 1
    yield from [a, b]
    while True:
        a, b = b, a + 2 * b
        yield b


def A000041(n):
    return npartitions(n)


def A001045_gen():  # generator of terms
    a, b = 0, 1
    yield from [a, b]
    while True:
        a, b = b, 2 * a + b
        yield b


def A000043_gen():
    return (p for p in (prime(n) for n in count(1)) if isprime(2**p - 1))


def A008277_T(n, k):
    return stirling(n, k)


def A000396_gen():
    return filter(lambda n: divisor_sigma(n) == 2 * n, count(1))


def A010060_gen():  # generator of terms
    yield 0
    blist = [0]
    while True:
        c = [1 - d for d in blist]
        blist += c
        yield from c


def A000312(n):
    return n**n


def A000326(n):
    return n * (3 * n - 1) // 2


def A000302(n):
    return 4**n


def A001065(n):
    return divisor_sigma(n) - n


def A000330(n):
    return n * (n + 1) * (2 * n + 1) // 6


def A001405(n):
    return comb(n, n // 2)


def A001405_gen():  # generator of terms
    yield 1
    a = 1
    for i in count(1):
        a = 2 * a * i // (i + 1) if i & 1 else 2 * a
        yield a


def A001764(n):
    return comb(3 * n, n) // (2 * n + 1)


def A000124(n):
    return n * (n + 1) // 2 + 1


def A350536(n):
    m = 2 * n + 1
    for l in count(len(str(m))):
        for s in product("13579", repeat=l):
            k = int("".join(s))
            if k > m and k % m == 0:
                return k


def A350538(n):
    for l in count(len(str(n)) - 1):
        for a in "2468":
            for b in product("02468", repeat=l):
                k = int(a + "".join(b))
                if k > n and k % n == 0:
                    return k


def A350654(n):
    for m in count(2):
        c = 0
        for d in divisors(m, generator=True):
            if not (
                ((m - 1) % (d - 1) if d > 1 else True)
                and (m - 1) % (d + 1)
                and ((m + 1) % (d - 1) if d > 1 else True)
                and (m + 1) % (d + 1)
            ):
                c += 1
                if c > n:
                    break
        if c == n:
            return m


def A078221(n):
    return 2 * n - 1 if n < 3 else 10 ** (2 ** (n - 3)) - 1


def A350540(n):
    return min(sqrt_mod(17, 2**n, all_roots=True))


def A350549(n):
    return 1 if n == 0 else Matrix(n, n, lambda i, j: (j - i + 1) // 2).per()


def A350603_gen():  # generator of terms
    s = {0}
    while True:
        yield from sorted(s)
        s = set(chain.from_iterable((x + 1, 2 * x) for x in s))


def A000203(n):
    return divisor_sigma(n)


def A027641(n):
    return bernoulli(n).p


def A027642(n):
    return bernoulli(n).q


def A122554_gen():  # generator of terms
    s = {1}
    while True:
        yield len(s)
        s = set(chain.from_iterable((x, x + 2, 2 * x) for x in s))


def A123212_gen():  # generator of terms
    s = {1}
    while True:
        yield sum(s)
        s = set(chain.from_iterable((x, 2 * x, x**2) for x in s))


def A123247_gen():  # generator of terms
    s = {1}
    while True:
        yield len(s)
        s = set(chain.from_iterable((x, x + 1, 2 * x, 3 * x) for x in s))


def A350604_gen():  # generator of terms
    s = {1}
    while True:
        yield from sorted(s)
        s = set(chain.from_iterable((x, 2 * x, 3 * x) for x in s))


def A350605_gen():  # generator of terms
    s = {1}
    while True:
        yield from sorted(s)
        s = set(chain.from_iterable((x, 2 * x + 1, 3 * x + 1) for x in s))


def A350606_gen():  # generator of terms
    s = {1}
    while True:
        yield len(s)
        s = set(chain.from_iterable((x, 2 * x + 1, 3 * x + 1) for x in s))


def A000272(n):
    return 1 if n <= 1 else n ** (n - 2)


def A001157(n):
    return divisor_sigma(n, 2)


@lru_cache(maxsize=None)
def A002033(n):
    if n <= 1:
        return 1
    return sum(A002033(i - 1) for i in divisors(n + 1, generator=True) if i <= n)


def A005834(n):
    return 2 * n


def A350246_gen():  # generator of terms
    yield 11
    s = "11"
    while True:
        for k in count(3, 3):
            t = str(k)
            m = int(t + s)
            if isprime(m) and isprime(m + 2):
                yield k
                break
        s = t + s


def A350691_helper(
    n, m
):  # generator in order of numbers with n decimal digits and m 1's. leading zeros are allowed.
    if n >= m:
        if n == 1:
            if m == 1:
                yield 1
            else:
                yield 0
                yield from range(2, 10)
        elif n == m:
            yield (10**m - 1) // 9
        else:
            for b in A350691_helper(n - 1, m):
                yield b
            r = 10 ** (n - 1)
            for b in A350691_helper(n - 1, m - 1):
                yield r + b
            for a in range(2, 10):
                k = a * r
                for b in A350691_helper(n - 1, m):
                    yield k + b


def A350691(n):
    for l in count(n):
        r = 10 ** (l - 1)
        for a in range(1, 10):
            n2 = n - 1 if a == 1 else n
            k = a * r
            for s in A350691_helper(l - 1, n2):
                m = k + s
                if bin(m)[2:].count("1") == n:
                    return m


def A350692_helper(
    n, m
):  # generator in order of numbers with n decimal digits and m 0's. leading zeros are allowed.
    if n >= m:
        if n == 1:
            if m == 1:
                yield 0
            else:
                yield from range(1, 10)
        elif n == m:
            yield 0
        else:
            for b in A350692_helper(n - 1, m - 1):
                yield b
            r = 10 ** (n - 1)
            for a in range(1, 10):
                k = a * r
                for b in A350692_helper(n - 1, m):
                    yield k + b


def A350692(n):
    if n == 1:
        return 0
    for l in count(n):
        r = 10 ** (l - 1)
        for a in range(1, 10):
            k = a * r
            for s in A350692_helper(l - 1, n):
                m = k + s
                if bin(m)[2:].count("0") == n:
                    return m


@lru_cache(maxsize=None)
def A000364(n):
    return (
        1
        if n == 0
        else (1 if n % 2 else -1)
        * sum((-1 if i % 2 else 1) * A000364(i) * comb(2 * n, 2 * i) for i in range(n))
    )


def A000688(n):
    return prod(map(npartitions, factorint(n).values()))


def A000262_gen():  # generator of terms
    a, b = [1, 1]
    yield from [1, 1]
    for n in count(2):
        a, b = b, (2 * n - 1) * b - (n - 1) * (n - 2) * a
        yield b


def A000262(n):
    return hyperexpand(hyper((-n + 1, -n), [], 1))


@lru_cache(maxsize=None)
def A001462(n):
    return 1 if n == 1 else 1 + A001462(n - A001462(A001462(n - 1)))


def A005100_gen(startvalue=1):
    return filter(lambda n: divisor_sigma(n) < 2 * n, count(max(startvalue, 1)))


def A005101_gen(startvalue=1):
    return filter(lambda n: divisor_sigma(n) > 2 * n, count(max(startvalue, 1)))


@lru_cache(maxsize=None)
def A001190(n):
    if n <= 1:
        return n
    m = n // 2 + n % 2
    return (
        sum(A001190(i + 1) * A001190(n - 1 - i) for i in range(m - 1))
        + (1 - n % 2) * A001190(m) * (A001190(m) + 1) // 2
    )


def A008292_T(n, k):
    return sum(
        (-1 if j % 2 else 1) * (k - j) ** n * comb(n + 1, j) for j in range(k + 1)
    )


@lru_cache(maxsize=None)
def A000081(n):
    return (
        n
        if n <= 1
        else sum(
            sum(d * A000081(d) for d in divisor_tuple(k)) * A000081(n - k)
            for k in range(1, n)
        )
        // (n - 1)
    )


def A350738(n):
    return Poly(
        sum(
            (-1 if k % 2 else 1)
            * symbolx ** (k**2)
            * prod(1 + symbolx**j for j in range(1, k + 1))
            for k in range(isqrt(n + 1) + 1)
        )
    ).all_coeffs()[-n - 1]


def A014258_gen():  # generator of terms
    a, b = 0, 1
    yield 0
    while True:
        yield b
        a, b = b, int(str(a + b)[::-1])


def A350079_gen():  # generator of terms
    a, b = 0, 1
    for n in count(1):
        if b < a:
            yield n
        a, b = b, int(str(a + b)[::-1])


def A350782(n):
    m, p, c = factorial(n), 3, 0
    while p <= m:
        if isprime(2 * m - p):
            c += 1
        p = nextprime(p)
    return c


def A350743(n):
    f = list(factorint(n).items())
    return sum(
        1
        for k in range(1, n + 1)
        if prod(p ** ((q + 1) * k) - 1 for p, q in f)
        // prod(p**k - 1 for p, q in f)
        % k
        == 0
    )


def A018819_gen():  # generator of terms
    aqueue, f, b, a = deque([2]), True, 1, 2
    yield from (1, 1, 2, 2, 4, 4)
    while True:
        a += b
        yield from (2 * a,) * 2
        aqueue.append(a)
        if f:
            b = aqueue.popleft()
        f = not f


@lru_cache(maxsize=None)
def A018819(n):
    return 1 if n == 0 else A018819(n - 1) + (0 if n % 2 else A018819(n // 2))


def A000123_gen():  # generator of terms
    aqueue, f, b, a = deque([2]), True, 1, 2
    yield from (1, 2, 4)
    while True:
        a += b
        yield 2 * a
        aqueue.append(a)
        if f:
            b = aqueue.popleft()
        f = not f


@lru_cache(maxsize=None)
def A000123(n):
    return 1 if n == 0 else A000123(n - 1) + A000123(n // 2)


def A350493(n):
    return pow(isqrt(prime(n)), 2, n)


def A054108(n):
    return (1 if n % 2 else -1) * sum(
        (-1 if k % 2 else 1) * comb(2 * k, k) for k in range(n + 2)
    )


def A054108_gen():  # generator of terms
    b = 1
    for n in count(1):
        b = comb(2 * n, n) - b
        yield b


def A349554(n):
    return (1 if n % 2 else -1) * (
        sum((-1 if k % 2 else 1) * comb(2 * k, k) for k in range(n + 2)) - 4
    )


def A349554_gen():  # generator of terms
    b = 5
    for n in count(2):
        b = comb(2 * n, n) - b
        yield b


def A350459(n):
    return sum(
        1
        for d in range(1, n + 1)
        for c in range(1, n + 1)
        for b in range(1, d + 1)
        for a in range(1, b + 1)
        if (a * d) ** 2 + (b * c) ** 2 == (c * d) ** 2
    )


def A350247_gen(startvalue=3):  # generator of terms
    for n in count(max(3, startvalue + (3 - startvalue % 3) % 3), 3):
        if isprime(100 * n + 11) and isprime(100 * n + 13):
            yield n


def A010051(n):
    return int(isprime(n))


def A052075_gen():
    return filter(
        lambda p: str(nextprime(p)) in str(p**3), (prime(n) for n in count(1))
    )


def A321796_gen():
    return filter(
        lambda p: str(prevprime(p)) in str(p**3), (prime(n) for n in count(2))
    )


def A003136_gen():
    return (
        n
        for n in count(0)
        if all(e % 2 == 0 for p, e in factorint(n).items() if p % 3 == 2)
    )


def A000045(n):
    return fibonacci(n)


def A000045_gen():  # generator of terms
    a, b = 0, 1
    yield a
    while True:
        yield b
        a, b = b, a + b


def A122045(n):
    return euler(n)


@lru_cache(maxsize=None)
def A000219(n):
    return (
        1
        if n == 0
        else (
            divisor_sigma(n, 2)
            + sum(divisor_sigma(k + 1, 2) * A000219(n - k - 1) for k in range(n - 1))
        )
        // n
    )


def A039834_gen():  # generator of terms
    a, b = 1, 1
    yield a
    while True:
        yield b
        a, b = b, a - b


def A039834(n):
    return fibonacci(-n)


@lru_cache(maxsize=None)
def A001970_helper(n):
    return sum(d * npartitions(d) for d in divisors(n, generator=True))


@lru_cache(maxsize=None)
def A001970(n):
    return (
        1
        if n <= 1
        else (
            A001970_helper(n)
            + A001970_helper(n - 1)
            + sum(A001970_helper(k + 1) * A001970(n - k - 1) for k in range(n - 2))
        )
        // n
    )


def A350858(n):
    return (
        1
        if n == 0
        else min(
            Matrix(n, n, p).per()
            for p in permutations(prime(m) for m in range(1, n**2 + 1))
        )
    )


def A350859(n):
    return (
        1
        if n == 0
        else max(
            Matrix(n, n, p).per()
            for p in permutations(prime(m) for m in range(1, n**2 + 1))
        )
    )


def A350565(n):
    return (
        1
        if n == 0
        else min(Matrix(n, n, p).per() for p in permutations(range(1, n**2 + 1)))
    )


def A350566(n):
    return (
        1
        if n == 0
        else max(Matrix(n, n, p).per() for p in permutations(range(1, n**2 + 1)))
    )


def A350230_gen(startvalue=1):
    return (
        n
        for n in count(max(startvalue, 1))
        if all((isprime(n + d + n // d) for d in divisors(n) if d * d <= n))
    )


def A254926(n):
    return prod(
        p**e - (p ** (e - 3) if e >= 3 else 0) for p, e in factorint(n).items()
    )


def A349309_gen(startvalue=1):  # generator of terms >= startvalue
    a = prod(
        p**e - (p ** (e - 3) if e >= 3 else 0)
        for p, e in factorint(max(startvalue, 1)).items()
    )
    for k in count(max(startvalue, 1)):
        b = prod(
            p**e - (p ** (e - 3) if e >= 3 else 0)
            for p, e in factorint(k + 1).items()
        )
        if a == b:
            yield k
        a = b


def A350179_gen():
    return (
        p
        for p in (prime(n) for n in count(1))
        if max(factorint(p**3 - 1).values()) < 3
    )


def A328727_gen(startvalue=0):  # generator of terms
    for n in count(max(startvalue, 0)):
        s = gmpy2digits(n, 3)
        for i in range(len(s) - 1):
            if "0" not in s[i : i + 2]:
                break
        else:
            yield n


def A350868(n):
    if n < 2:
        return 2 + n
    qlist = [prime(i) - 2 for i in range(2, n + 2)]
    p = prime(n + 1)
    mlist = [2 * k**2 for k in range(1, n + 1)]
    while True:
        if qlist == mlist:
            return p - mlist[-1]
        qlist = [q - qlist[0] for q in qlist[1:]]
        r = nextprime(p)
        qlist.append(r - p + qlist[-1])
        p = r


def A095258_gen():  # generator of terms
    bset, s = {1}, 3
    yield 1
    while True:
        for d in divisors(s):
            if d not in bset:
                yield d
                bset.add(d)
                s += d
                break


def A308751_gen():  # generator of terms
    bset, s = {1}, 3
    yield 2
    while True:
        for d in divisors(s):
            if d not in bset:
                yield s // d
                bset.add(d)
                s += d
                break


def A350741_gen():  # generator of terms
    bset, c, s = {1}, 1, 3
    yield 1
    while True:
        for d in divisors(s):
            if d not in bset:
                if d > c:
                    yield d
                    c = d
                bset.add(d)
                s += d
                break


def A253415_gen():  # generator of terms, first term is a(2)
    bset, m, s = {1}, 2, 3
    while True:
        for d in divisors(s):
            if d not in bset:
                bset.add(d)
                while m in bset:
                    m += 1
                yield m
                s += d
                break


def A253425_gen():  # generator of terms
    bset, l, m, s = {1}, 0, 2, 3
    while True:
        for d in divisors(s):
            if d not in bset:
                bset.add(d)
                if m in bset:
                    yield l
                    l = 1
                    while m in bset:
                        m += 1
                else:
                    l += 1
                s += d
                break


def A350701(n):
    return 0 if n <= 1 else (lambda x: isqrt(x[0] - 1) - isqrt(x[1]))(fib2(n + 1))


def A350701_gen():  # generator of terms
    yield from [0, 0]
    a, b = 1, 2
    while True:
        yield isqrt(b - 1) - isqrt(a)
        a, b = b, a + b


def A324151(n):
    return 2 * multinomial_coefficients(3, 3 * n)[(n, n, n)] // (n + 1) // (n + 2)


def A066750(n):
    return gcd(n, sum(int(d) for d in str(n)))


def A348192_gen():  # generator of terms
    blist = [0]
    yield 0
    for n in count(1):
        blist.append(1 + blist[n - gcd(n, sum(int(d) for d in str(n)))])
        yield blist[-1]


def A306354(n):
    return gcd(n, sum(int(d) ** len(str(n)) for d in str(n)))


def A348591(n):
    return (lambda x, y: int(x[0] * x[1] % y))(lucas2(n + 1), fib(n + 2))


def A350932(n):
    return min(
        Matrix([p[n - 1 - i : 2 * n - 1 - i] for i in range(n)]).det()
        for p in permutations(prime(i) for i in range(1, 2 * n))
    )


def A350933(n):
    return max(
        Matrix([p[n - 1 - i : 2 * n - 1 - i] for i in range(n)]).det()
        for p in permutations(prime(i) for i in range(1, 2 * n))
    )


def A350930(n):
    return min(
        Matrix([p[n - 1 - i : 2 * n - 1 - i] for i in range(n)]).det()
        for p in permutations(range(1, 2 * n))
    )


def A350931(n):
    return max(
        Matrix([p[n - 1 - i : 2 * n - 1 - i] for i in range(n)]).det()
        for p in permutations(range(1, 2 * n))
    )


def A350937(n):
    return (
        1
        if n == 0
        else min(
            Matrix([p[n - 1 - i : 2 * n - 1 - i] for i in range(n)]).per()
            for p in permutations(range(1, 2 * n))
        )
    )


def A350938(n):
    return (
        1
        if n == 0
        else max(
            Matrix([p[n - 1 - i : 2 * n - 1 - i] for i in range(n)]).per()
            for p in permutations(range(1, 2 * n))
        )
    )


def A350939(n):
    return (
        1
        if n == 0
        else min(
            Matrix([p[n - 1 - i : 2 * n - 1 - i] for i in range(n)]).per()
            for p in permutations(prime(i) for i in range(1, 2 * n))
        )
    )


def A350940(n):
    return (
        1
        if n == 0
        else max(
            Matrix([p[n - 1 - i : 2 * n - 1 - i] for i in range(n)]).per()
            for p in permutations(prime(i) for i in range(1, 2 * n))
        )
    )


def A350956(n):
    return max(
        Matrix([p[i:0:-1] + p[0 : n - i] for i in range(n)]).det()
        for p in permutations(prime(i) for i in range(1, n + 1))
    )


def A350955(n):
    return min(
        Matrix([p[i:0:-1] + p[0 : n - i] for i in range(n)]).det()
        for p in permutations(prime(i) for i in range(1, n + 1))
    )


def A350954(n):
    return max(
        Matrix([p[i:0:-1] + p[0 : n - i] for i in range(n)]).det()
        for p in permutations(range(1, n + 1))
    )


def A350953(n):
    return min(
        Matrix([p[i:0:-1] + p[0 : n - i] for i in range(n)]).det()
        for p in permutations(range(1, n + 1))
    )


def A348891(n):
    return min(
        d
        for d in (
            abs(Matrix([p[i:0:-1] + p[0 : n - i] for i in range(n)]).det())
            for p in permutations(prime(i) for i in range(1, n + 1))
        )
        if d > 0
    )


def A347718(n):
    return prod(
        (q ** (r + 1) - 1) // (q - 1)
        for q, r in sum(
            (
                Counter(factorint((p ** (n * (e + 1)) - 1) // (p**n - 1)))
                for p, e in factorint(n).items()
            ),
            Counter(),
        ).items()
    )


def A064165(n):
    return prod(
        r + 1
        for q, r in sum(
            (
                Counter(factorint((p ** (n * (e + 1)) - 1) // (p**n - 1)))
                for p, e in factorint(n).items()
            ),
            Counter(),
        ).items()
    )


def A351021(n):
    return (
        1
        if n == 0
        else min(
            Matrix([p[i:0:-1] + p[0 : n - i] for i in range(n)]).per()
            for p in permutations(prime(i) for i in range(1, n + 1))
        )
    )


def A351022(n):
    return (
        1
        if n == 0
        else max(
            Matrix([p[i:0:-1] + p[0 : n - i] for i in range(n)]).per()
            for p in permutations(prime(i) for i in range(1, n + 1))
        )
    )


def A351020(n):
    return (
        1
        if n == 0
        else max(
            Matrix([p[i:0:-1] + p[0 : n - i] for i in range(n)]).per()
            for p in permutations(range(1, n + 1))
        )
    )


def A351019(n):
    return (
        1
        if n == 0
        else min(
            Matrix([p[i:0:-1] + p[0 : n - i] for i in range(n)]).per()
            for p in permutations(range(1, n + 1))
        )
    )


def A351114(n):
    f = factorint(n)
    return int(
        not prod(p * (p ** (e + 1) - 1) for p, e in f.items())
        % (n * prod((p - 1) ** 2 for p in f))
    )


def A005230_gen():  # generator of terms
    blist = [1]
    for n in count(1):
        yield blist[-1]
        blist.append(sum(blist[-i] for i in range(1, (isqrt(8 * n) + 3) // 2)))


def A002024(n):
    return (isqrt(8 * n) + 1) // 2


def A005130(n):
    return prod(factorial(3 * k + 1) for k in range(n)) // prod(
        factorial(n + k) for k in range(n)
    )


def A049503(n):
    return (
        prod(factorial(3 * k + 1) for k in range(n))
        // prod(factorial(n + k) for k in range(n))
    ) ** 2


def A000140(n):
    return (
        1
        if n == 1
        else max(
            Poly(
                prod(sum(symbolx**i for i in range(j + 1)) for j in range(n))
            ).all_coeffs()
        )
    )


def A000055(n):
    return (
        1
        if n == 0
        else A000081(n)
        - sum(A000081(i) * A000081(n - i) for i in range(1, n // 2 + 1))
        + (0 if n % 2 else (A000081(n // 2) + 1) * A000081(n // 2) // 2)
    )


def A217420(n):
    return sum(A000081(i) * A000081(n - 1 - i) for i in range(1, (n - 1) // 2 + 1)) - (
        (A000081((n - 1) // 2) + 1) * A000081((n - 1) // 2) // 2 if n % 2 else 0
    )


def A336039_gen(startvalue=1):
    return (k for k in count(max(startvalue, 1)) if not A000081(k) % k)


def A036361(n):
    return int(n * (n - 1) * (2 * n - 3) ** (n - 4) // 2)


def A036506(n):
    return int(n * (n - 3) * (n - 2) * (n - 1) * (4 * n - 15) ** (n - 6) // 24)


def A036362(n):
    return int(n * (n - 2) * (n - 1) * (3 * n - 8) ** (n - 5) // 6)


def A000051(n):
    return 2**n + 1


def A145071(n):
    return 2 ** (n + 1) + n - 2


def A060477(n):
    return sum(mobius(n // d) * (2**d + 1) for d in divisors(n, generator=True)) // n


def A001037(n):
    return (
        1
        if n == 0
        else sum(mobius(n // d) * 2**d for d in divisors(n, generator=True)) // n
    )


def A027375(n):
    return sum(mobius(n // d) * 2**d for d in divisors(n, generator=True))


def A000740(n):
    return sum(mobius(n // d) * 2 ** (d - 1) for d in divisors(n, generator=True))


def A059966(n):
    return sum(mobius(n // d) * (2**d - 1) for d in divisors(n, generator=True)) // n


def A343318(n):
    return (2**n + 1) ** 3


def A333474_gen(startvalue=0):  # generator of terms
    m = 2 ** (s := max(startvalue, 0))
    n = m + 1
    for k in count(s):
        if not n % sum(int(d) for d in str(n)):
            yield k
        m *= 2
        n = m + 1


def A023578(n):
    return min((p for p in factorint(prime(n) + 3) if p > 2), default=1)


def A078701(n):
    return min((p for p in factorint(n) if p > 2), default=1)


@lru_cache(maxsize=None)
def A008472(n):
    return sum(primefactors(n))


@lru_cache(maxsize=None)
def A000607(n):
    return (
        1 if n == 0 else sum(A008472(k) * A000607(n - k) for k in range(1, n + 1)) // n
    )


def A007778(n):
    return n ** (n + 1)


def A007830(n):
    return (n + 3) ** n


def A008785(n):
    return (n + 4) ** n


def A008786(n):
    return (n + 5) ** n


def A008787(n):
    return (n + 6) ** n


def A008788(n):
    return n ** (n + 2)


def A008789(n):
    return n ** (n + 3)


def A008790(n):
    return n ** (n + 4)


def A008791(n):
    return n ** (n + 5)


def A000169(n):
    return n ** (n - 1)


def A329723(n):
    return 1 if n <= 1 else lucas(n - 2)


def A278159(n):
    return RLT(n, primorial)


def A246674(n):
    return RLT(n, lambda m: 2**m - 1)


def A001317(n):
    return int("".join(str(int(not (~n & k))) for k in range(n + 1)), 2)


def A247282(n):
    return RLT(
        n, lambda m: int("".join(str(int(not (~(m - 1) & k))) for k in range(m)), 2)
    )


def A286575(n):
    return RLT(n, lambda m: 2 ** (bin(m).count("1")))


def A286574(n):
    return len(bin(RLT(n, lambda m: 2 ** (bin(m).count("1"))))) - 3


def A246685(n):
    return RLT(n, lambda m: 1 if m <= 1 else 2 ** (2 ** (m - 2)) + 1)


def A000012(n):
    return 1


def A000007(n):
    return int(n == 0)


def A046523(n):
    return prod(
        prime(i + 1) ** e
        for i, e in enumerate(sorted(factorint(n).values(), reverse=True))
    )


def A056040(n):
    return factorial(n) // factorial(n // 2) ** 2


def A246661(n):
    return RLT(n, lambda m: factorial(m) // factorial(m // 2) ** 2)


def A245564(n):
    return RLT(n, lambda m: fibonacci(m + 2))


def A185017(n):
    return int(n == 7)


def A185016(n):
    return int(n == 6)


def A185015(n):
    return int(n == 5)


def A185014(n):
    return int(n == 4)


def A185013(n):
    return int(n == 3)


def A185012(n):
    return int(n == 2)


def A063524(n):
    return int(n == 1)


def A014081(n):
    return sum(len(d) - 1 for d in split("0+", bin(n)[2:]) if d != "")


def A053645(n):
    return 0 if n <= 1 else int(bin(n)[3:], 2)


@lru_cache(maxsize=None)
def A346422(n):
    return (
        1
        if n <= 1
        else A346422(int((s := bin(n)[2:])[1:], 2))
        * (1 + sum(len(d) - 1 for d in split("0+", s) if d != ""))
    )


def A245195(n):
    return 2 ** A014081(n)


def A245565(n):
    return RLT(n, lambda m: next(islice(A000129_gen(), m + 1, None)))


def A329722(n):
    return RLT(n, lambda m: 1 if m <= 1 else lucas(m - 2))


def A278161(n):
    return RLT(n, lambda m: m // 2 + 1)


def A000930_gen():  # generator of terms
    blist = [1] * 3
    while True:
        yield blist[0]
        blist = blist[1:] + [blist[0] + blist[2]]


def A329720(n):
    return RLT(n, lambda m: next(islice(A000930_gen(), m, None)))


def A106737(n):
    return RLT(n, lambda m: m + 1)


def A277561(n):
    return RLT(n, lambda m: 1 if m == 0 else 2)


def A246028(n):
    return RLT(n, lambda m: fibonacci(m + 1))


def A001316(n):
    return 2 ** A000120(n)


def A102376(n):
    return 4 ** A000120(n)


def A036044(n):
    return -int((s := bin(n)[-1:1:-1]), 2) - 1 + 2 ** len(s)


def A059894(n):
    return n if n <= 1 else -int((s := bin(n)[-1:2:-1]), 2) - 1 + 2 ** (len(s) + 1)


def A284799(n):
    return -int((s := gmpy2digits(n, 4)[::-1]), 4) - 1 + 4 ** len(s)


def A284797(n):
    return -int((s := gmpy2digits(n, 3)[::-1]), 3) - 1 + 3 ** len(s)


def A284798_gen():
    return (
        n
        for n in count(0)
        if not n + int((s := gmpy2digits(n, 3)[::-1]), 3) + 1 - 3 ** len(s)
    )


def A159006(n):
    return -int((s := bin(prime(n))[-1:1:-1]), 2) - 1 + 2 ** len(s)


def A284807(n):
    return -int((s := oct(n)[-1:1:-1]), 8) - 1 + 8 ** len(s)


def A351198(n):
    return sum(p**10 for p in primefactors(n))


def A351197(n):
    return sum(p**9 for p in primefactors(n))


def A351196(n):
    return sum(p**8 for p in primefactors(n))


def A351262(n):
    return sum((n // p) ** 10 for p in primefactors(n))


def A351249(n):
    return sum((n // p) ** 9 for p in primefactors(n))


def A351248(n):
    return sum((n // p) ** 8 for p in primefactors(n))


def A069359(n):
    return sum(n // p for p in primefactors(n))


def A351219(n):
    return prod(fibonacci(e + 1) for e in factorint(n).values())


def A002371(n):
    return 0 if n == 1 or n == 3 else n_order(10, prime(n))


def A007732(n):
    return n_order(10, n // 2 ** multiplicity(2, n) // 5 ** multiplicity(5, n))


def A350814_gen(startvalue=1):
    return filter(
        lambda m: max(repeating_decimals_expr(Fraction(1, m), digits_only=True)) == "3",
        count(max(startvalue, 1)),
    )


def A072982_gen():
    return (
        p
        for p in (prime(n) for n in count(2))
        if p != 5 and bin(n_order(10, p))[2:].rstrip("0") == "1"
    )


def A051628(n):
    return max(multiplicity(2, n), multiplicity(5, n))


def A341383_gen(startvalue=1):  # generator of terms
    for m in count(max(startvalue, 1)):
        m2, m5 = multiplicity(2, m), multiplicity(5, m)
        if (
            max(str(10 ** (max(m2, m5) + n_order(10, m // 2**m2 // 5**m5)) // m))
            == "2"
        ):
            yield m


def A333236(n):
    m2, m5 = multiplicity(2, n), multiplicity(5, n)
    return int(
        max(str(10 ** (max(m2, m5) + n_order(10, n // 2**m2 // 5**m5)) // n))
    )


def A333442(n):
    if n == 1:
        return 0
    m2, m5 = multiplicity(2, n), multiplicity(5, n)
    r = max(m2, m5) + n_order(10, n // 2**m2 // 5**m5)
    s = str(10**r // n).zfill(r)
    return s.index(max(s)) + 1


def A333237_gen(startvalue=1):  # generator of terms
    for m in count(max(startvalue, 1)):
        m2, m5 = multiplicity(2, m), multiplicity(5, m)
        if (
            max(str(10 ** (max(m2, m5) + n_order(10, m // 2**m2 // 5**m5)) // m))
            == "9"
        ):
            yield m


def A351355(n):
    return (
        0
        if n == 1
        else n * n
        - sum(2 * n // k for k in range(2, 2 * n))
        + sum(n // k for k in range(2, n))
    )


def A351362(n):
    return (
        1
        if n == 2
        else n * n
        - 1
        - sum((2 * n - 1) // k for k in range(2, 2 * n - 1))
        + sum((n - 1) // k for k in range(2, n - 1))
    )


def A351139(n):
    if n == 2:
        return 14
    for r in count(1):
        if (
            k := continued_fraction_reduce(
                [r, list(range(1, n + 1)) + list(range(n - 1, 0, -1)) + [2 * r]]
            )
            ** 2
        ).is_integer:
            return k


def A350562_gen():  # generator of terms
    bdict = {1: 1}
    yield 1
    b = 0
    for n in count(3):
        yield b
        c = (n - bdict[b]) * b if b in bdict else 1
        bdict[b], b = n - 1, c


def A350574_gen():  # generator of terms
    for l in count(1):
        rlist = []
        for a in combinations_with_replacement("123456789", l):
            s = "".join(a)
            p, q = int(s), int(s[::-1])
            if p != q and isprime(p) and isprime(q):
                for b in multiset_permutations(a):
                    r = int("".join(b))
                    if p < r < q and isprime(r):
                        rlist.append(r)
                        break
        yield from sorted(rlist)


def A075188(n):
    m = lcm(*range(1, n + 1))
    mlist = tuple(m // i for i in range(1, n + 1))
    k = sum(mlist)
    c = 0
    for l in range(0, n // 2 + 1):
        for p in combinations(mlist, l):
            s = sum(p)
            r, t = s // gcd(s, m), (k - s) // gcd(k - s, m)
            if isprime(r):
                if 2 * l != n:
                    c += 1
            if isprime(t):
                c += 1
    return c


def A351470_gen(startvalue=1):  # generator of terms
    for m in count(max(startvalue, 1)):
        m2, m5 = multiplicity(2, m), multiplicity(5, m)
        if (
            max(str(10 ** (max(m2, m5) + n_order(10, m // 2**m2 // 5**m5)) // m))
            == "4"
        ):
            yield m


def A351471_gen(startvalue=1):  # generator of terms
    for m in count(max(startvalue, 1)):
        m2, m5 = multiplicity(2, m), multiplicity(5, m)
        if (
            max(str(10 ** (max(m2, m5) + n_order(10, m // 2**m2 // 5**m5)) // m))
            == "5"
        ):
            yield m


def A351472_gen(startvalue=1):  # generator of terms
    for m in count(max(startvalue, 1)):
        m2, m5 = multiplicity(2, m), multiplicity(5, m)
        if (
            max(str(10 ** (max(m2, m5) + n_order(10, m // 2**m2 // 5**m5)) // m))
            == "6"
        ):
            yield m


def A075226(n):
    m = lcm(*range(1, n + 1))
    c, mlist = 0, tuple(m // i for i in range(1, n + 1))
    for l in range(n, -1, -1):
        if sum(mlist[:l]) < c:
            break
        for p in combinations(mlist, l):
            s = sum(p)
            s //= gcd(s, m)
            if s > c and isprime(s):
                c = s
    return c


def A256221(n):
    m = lcm(*range(1, n + 1))
    fset, fibset, mlist = set(), set(), tuple(m // i for i in range(1, n + 1))
    a, b, k = 0, 1, sum(mlist)
    while b <= k:
        fibset.add(b)
        a, b = b, a + b
    for l in range(1, n // 2 + 1):
        for p in combinations(mlist, l):
            s = sum(p)
            if (t := s // gcd(s, m)) in fibset:
                fset.add(t)
            if 2 * l != n and (t := (k - s) // gcd(k - s, m)) in fibset:
                fset.add(t)
    if (t := k // gcd(k, m)) in fibset:
        fset.add(t)
    return len(fset)


def A256220(n):
    m = lcm(*range(1, n + 1))
    fibset, mlist = set(), tuple(m // i for i in range(1, n + 1))
    a, b, c, k = 0, 1, 0, sum(mlist)
    while b <= k:
        fibset.add(b)
        a, b = b, a + b
    for l in range(1, n // 2 + 1):
        for p in combinations(mlist, l):
            s = sum(p)
            if s // gcd(s, m) in fibset:
                c += 1
            if 2 * l != n and (k - s) // gcd(k - s, m) in fibset:
                c += 1
    return c + int(k // gcd(k, m) in fibset)


def A351532(n):
    return sum(
        1
        for d in diop_quadratic(
            n**2 + 3 * symbolx * symboly - 2 * n * (symbolx + symboly)
        )
        if 0 < d[0] < n and 0 < d[1] < n
    )


def A241883(n):
    c, w = 0, n + 1
    while 6 * n + w * (22 * n + w * (18 * n + w * (4 * n - w - 6) - 11) - 6) >= 0:
        x = max(w + 1, n * w // (w - n) + 1)
        wx = w * x
        while (
            2 * n * w
            + x
            * (2 * n + w * (6 * n - 2) + x * (3 * n + w * (3 * n - 3) + x * (n - w)))
            >= 0
        ):
            y = max(x + 1, w * x * n // (x * (w - n) - w * n) + 1)
            wxy = wx * y
            while (
                x * (n * w + y * (n + w * (2 * n - 1) + y * (n - w)))
                + y * (n * w * y + n * w)
                >= 0
            ):
                z, r = divmod(n * wxy, wxy - n * (x * y + w * (x + y)))
                if z > y and r == 0:
                    c += 1
                y += 1
                wxy += wx
            x += 1
            wx += w
        w += 1
    return c


def A347569(n):
    c, p = 0, n + 1
    while (
        120 * n
        + p
        * (
            548 * n
            + p
            * (
                675 * n
                + p * (340 * n + p * (75 * n + p * (6 * n - p - 15) - 85) - 225)
                - 274
            )
            - 120
        )
        >= 0
    ):
        q = max(p + 1, n * p // (p - n) + 1)
        pq = p * q
        while (
            p
            * (
                24 * n
                + q
                * (
                    100 * n
                    + q * (105 * n + q * (40 * n + q * (5 * n - q - 10) - 35) - 50)
                    - 24
                )
            )
            + q * (24 * n + q * (50 * n + q * (35 * n + q * (n * q + 10 * n))))
            >= 0
        ):
            r = max(q + 1, n * pq // (pq - n * (p + q)) + 1)
            pqr = pq * r
            while (
                p
                * (
                    q
                    * (
                        6 * n
                        + r * (22 * n + r * (18 * n + r * (4 * n - r - 6) - 11) - 6)
                    )
                    + r * (6 * n + r * (11 * n + r * (n * r + 6 * n)))
                )
                + q * r * (6 * n + r * (11 * n + r * (n * r + 6 * n)))
                >= 0
            ):
                s = max(r + 1, n * pqr // (pqr - n * (pq + r * (p + q))) + 1)
                pqrs = pqr * s
                while (
                    p
                    * (
                        q
                        * (
                            r * (2 * n + s * (6 * n + s * (3 * n - s - 3) - 2))
                            + s * (2 * n + s * (n * s + 3 * n))
                        )
                        + r * s * (2 * n + s * (n * s + 3 * n))
                    )
                    + q * r * s * (2 * n + s * (n * s + 3 * n))
                    >= 0
                ):
                    t = max(
                        s + 1,
                        n * pqrs // (pqrs - n * (pqr + pq * s + r * s * (p + q))) + 1,
                    )
                    pqrst = pqrs * t
                    while (
                        p
                        * (
                            q
                            * (
                                r * (s * (n + t * (2 * n - t - 1)) + t * (n * t + n))
                                + s * t * (n * t + n)
                            )
                            + r * s * t * (n * t + n)
                        )
                        + q * r * s * t * (n * t + n)
                        >= 0
                    ):
                        u, z = divmod(
                            n * pqrst,
                            pqrst
                            - n
                            * (
                                q * r * s * t
                                + p * r * s * t
                                + pq * s * t
                                + pqr * t
                                + pqrs
                            ),
                        )
                        if u > t and z == 0:
                            c += 1
                        t += 1
                        pqrst += pqrs
                    s += 1
                    pqrs += pqr
                r += 1
                pqr += pq
            q += 1
            pq += p
        p += 1
    return c


def A351372_gen():  # generator of terms
    for z in count(1):
        z2 = z**2
        for y in range(1, z + 1):
            a = isqrt(
                d := 3 * y**2 * (12 * z2 - 4 * z - 1)
                - 3 * z2 * (4 * y + 1)
                - 2 * y * z
            )
            if a**2 == d:
                x, r = divmod(12 * y * z - 2 * y - 2 * z - 2 * a, 4)
                if y <= x <= z and r == 0:
                    yield from (y, x, z)


def A351528_gen():  # generator of terms
    yield from (
        int(d[::-1], 2)
        for l in count(1)
        for d in sorted(bin(m)[:1:-1] for m in primerange(2 ** (l - 1), 2**l))
    )


def A104154_gen():  # generator of terms
    yield from (
        int(d[::-1])
        for l in count(1)
        for d in sorted(str(m)[::-1] for m in primerange(10 ** (l - 1), 10**l))
    )


def A098957(n):
    return int(bin(prime(n))[:1:-1], 2)


def A030101(n):
    return int(bin(n)[:1:-1], 2)


def A351105(n):
    return (
        n
        * (
            n
            * (
                n
                * (
                    n
                    * (
                        n * (n * (n * (n * (280 * n + 2772) + 10518) + 18711) + 14385)
                        + 1323
                    )
                    - 2863
                )
                - 126
            )
            + 360
        )
        // 45360
    )


def A347107(n):
    return (
        n
        * (n**2 * (n * (n * (n * (n * (21 * n + 36) - 42) - 84) + 21) + 56) - 8)
        // 672
    )


def A346642(n):
    return (
        n
        * (n**2 * (n * (n * (n * (n * (21 * n + 132) + 294) + 252) + 21) - 56) + 8)
        // 672
    )


def A333402_gen(startvalue=1):  # generator of terms
    for m in count(max(startvalue, 1)):
        k = 1
        while k <= m:
            k *= 10
        rset = {0}
        while True:
            k, r = divmod(k, m)
            if max(str(k)) > "1":
                break
            else:
                if r in rset:
                    yield m
                    break
            rset.add(r)
            k = r
            while k <= m:
                k *= 10


def A030302_gen():  # generator of terms
    return (int(d) for n in count(1) for d in bin(n)[2:])


def A351753(n):
    s1, s2 = tuple(), tuple()
    for i, s in enumerate(int(d) for n in count(1) for d in bin(n)[2:]):
        if i < n:
            s1 += (s,)
            s2 += (s,)
        else:
            s2 = s2[1:] + (s,)
            if s1 == s2:
                return i - n + 2


def A030303_gen():  # generator of terms
    return (
        i + 1 for i, s in enumerate(d for n in count(1) for d in bin(n)[2:]) if s == "1"
    )


def A003607_gen():  # generator of terms
    return (
        i for i, s in enumerate(d for n in count(0) for d in bin(n)[2:]) if s == "0"
    )


def A194472_gen(startvalue=1):  # generator of terms
    return (
        n
        for n in count(max(startvalue, 1))
        if any(s == n for s in accumulate(divisors(n)[:-2]))
    )


def A138591(n):
    return len(bin(n + len(bin(n)) - 3)) + n - 3


def A094683(n):
    return isqrt(n**3 if n % 2 else n)


def A093112(n):
    return (2**n - 1) ** 2 - 2


def A088054_gen():  # generator of terms
    f = 1
    for k in count(1):
        f *= k
        if isprime(f - 1):
            yield f - 1
        if isprime(f + 1):
            yield f + 1


def A046760_gen():  # generator of terms
    return (
        n
        for n in count(1)
        if len(str(n))
        < sum(
            len(str(p)) + (len(str(e)) if e > 1 else 0) for p, e in factorint(n).items()
        )
    )


def A046758_gen():  # generator of terms
    return (
        n
        for n in count(1)
        if n == 1
        or len(str(n))
        == sum(
            len(str(p)) + (len(str(e)) if e > 1 else 0) for p, e in factorint(n).items()
        )
    )


def A034897_gen():  # generator of terms
    return (
        n
        for n in count(2)
        if not isprime(n) and (n - 1) % (divisor_sigma(n) - n - 1) == 0
    )


def A019279_gen():  # generator of terms
    return (n for n in count(1) if divisor_sigma(divisor_sigma(n)) == 2 * n)


def A014080_gen():  # generator of terms
    return (
        n
        for n in count(1)
        if sum((1, 1, 2, 6, 24, 120, 720, 5040, 40320, 362880)[int(d)] for d in str(n))
        == n
    )


def A007588(n):
    return n * (2 * n**2 - 1)


def A342162(n):
    s1, s2, m = tuple(int(d) for d in str(n)), tuple(), -1
    l = len(s1)
    for i, s in enumerate(int(d) for k in count(0) for d in str(k)):
        s2 = (s2 + (s,))[-l:]
        if s2 == s1:
            if m >= 0:
                return i - m
            m = i


def A337227(n):
    s1 = tuple(int(d) for d in str(n))
    s2 = s1
    for i, s in enumerate(int(d) for k in count(n + 1) for d in str(k)):
        s2 = s2[1:] + (s,)
        if s2 == s1:
            return i + 1


def A052486_gen(startvalue=1):  # generator of terms
    return (
        n
        for n in count(max(startvalue, 1))
        if (lambda x: all(e > 1 for e in x) and gcd(*x) == 1)(factorint(n).values())
    )


def A007850_gen(startvalue=2):  # generator of terms
    return filter(
        lambda x: not isprime(x)
        and all((x // p - 1) % p == 0 for p in primefactors(x)),
        count(max(startvalue, 2)),
    )


def A334409_gen(startvalue=1):  # generator of terms
    for n in count(max(startvalue, 1)):
        ds = divisors(n)
        if any(
            s == 2 * n
            for s in accumulate(ds[i] + ds[-1 - i] for i in range((len(ds) - 1) // 2))
        ):
            yield n


def A334410_gen(startvalue=1):  # generator of terms
    for n in count(max(startvalue, 1)):
        ds = divisors(n)
        s = sum(ds)
        if s % 2 == 0 and any(2 * a == s for a in accumulate(ds)):
            yield n


@lru_cache(maxsize=None)
def A350661(n):
    return 1 if n == 1 else A350661(prod(primefactors(n)) - 1) + n


def A351412(n):
    if n == 1:
        return 1
    q, r = divmod(n, 4)
    if r == 0:
        return n - q + 1
    elif r == 2:
        return n - q
    elif r == 1:
        return n + 2 * q - 1
    else:
        return n + 2 * q


def A106303(n):
    a = b = (0,) * 4 + (1 % n,)
    s = 1 % n
    for m in count(1):
        b, s = b[1:] + (s,), (s + s - b[0]) % n
        if a == b:
            return m


def A106304(n):
    a = b = (0,) * 4 + (1 % (p := prime(n)),)
    s = 1 % p
    for m in count(1):
        b, s = b[1:] + (s,), (s + s - b[0]) % p
        if a == b:
            return m


def A193994(n):
    a = b = (0,) * 4 + (1 % n,)
    c, s = 0, 1 % n
    for m in count(1):
        b, s = b[1:] + (s,), (s + s - b[0]) % n
        c += int(s == 0)
        if a == b:
            return c


def A106295(n):
    a = b = (4 % n, 1 % n, 3 % n, 7 % n)
    s = sum(b) % n
    for m in count(1):
        b, s = b[1:] + (s,), (s + s - b[0]) % n
        if a == b:
            return m


def A106297(n):
    a = b = (5 % n, 1 % n, 7 % n, 3 % n, 15 % n)
    s = sum(b) % n
    for m in count(1):
        b, s = b[1:] + (s,), (s + s - b[0]) % n
        if a == b:
            return m


def A106298(n):
    a = b = (5 % (p := prime(n)), 1 % p, 7 % p, 3 % p, 15 % p)
    s = sum(b) % p
    for m in count(1):
        b, s = b[1:] + (s,), (s + s - b[0]) % p
        if a == b:
            return m


def A068527(n):
    return 0 if n == 0 else (isqrt(n - 1) + 1) ** 2 - n


def A348596(n):
    return (isqrt(2 * n) + 1) ** 2 - 2 * n - 1


def A350962(n):
    return 0 if n == 0 else (isqrt(2 * n - 1) + 1) ** 2 - 2 * n


def A106290(n):
    bset, tset = set(), set()
    for t in product(range(n), repeat=5):
        t2 = t
        for c in count(1):
            t2 = t2[1:] + (sum(t2) % n,)
            if t == t2:
                bset.add(c)
                tset.add(t)
                break
            if t2 in tset:
                tset.add(t)
                break
    return len(bset)


def A351657_helper(n, pe):
    a = b = (0,) * (n - 1) + (1 % pe,)
    s = 1 % pe
    for m in count(1):
        b, s = b[1:] + (s,), (s + s - b[0]) % pe
        if a == b:
            return m


def A351657(n):
    return (
        1
        if n == 1
        else lcm(*(A351657_helper(n, p**e) for p, e in factorint(n).items()))
    )


def A143293_gen():
    return accumulate(accumulate(chain((1,), (prime(n) for n in count(1))), mul))


def A225727_gen():
    return (
        i + 1
        for i, m in enumerate(
            accumulate(accumulate(chain((1,), (prime(n) for n in count(1))), mul))
        )
        if m % (i + 1) == 0
    )


def A225841_gen():
    return (
        i + 1
        for i, m in enumerate(accumulate(accumulate((prime(n) for n in count(1)), mul)))
        if m % (i + 1) == 0
    )


def A225728_gen():
    return (
        prime(i + 1)
        for i, m in enumerate(
            accumulate(accumulate(chain((1,), (prime(n) for n in count(1))), mul))
        )
        if m % prime(i + 1) == 0
    )


def A045345_gen():
    return (
        i + 1
        for i, m in enumerate(accumulate(prime(n) for n in count(1)))
        if m % (i + 1) == 0
    )


def A007504_gen():
    return accumulate(prime(n) if n > 0 else 0 for n in count(0))


@lru_cache(maxsize=None)
def A351889_T(n, k):  # computes the period of the n-step Fibonacci sequence mod k
    if len(fs := factorint(k)) <= 1:
        a = b = (0,) * (n - 1) + (1 % k,)
        s = 1 % k
        for m in count(1):
            b, s = b[1:] + (s,), (s + s - b[0]) % k
            if a == b:
                return m
    else:
        return lcm(*(A351889_T(n, p**e) for p, e in fs.items()))


def A351568(n):
    return prod(
        1 if e % 2 else (p ** (e + 1) - 1) // (p - 1) for p, e in factorint(n).items()
    )


def A351569(n):
    return prod(
        (p ** (e + 1) - 1) // (p - 1) if e % 2 else 1 for p, e in factorint(n).items()
    )


def A350389(n):
    return prod(p**e if e % 2 else 1 for p, e in factorint(n).items())


def A351808_gen():  # generator of terms
    return (
        q
        for q, r in (
            divmod(prod(int(d) for d in str(m**2)), prod(int(d) for d in str(m)))
            for m in count(1)
            if "0" not in str(m)
        )
        if r == 0
    )


def A351807_gen():  # generator of terms
    return (
        m
        for m in count(1)
        if "0" not in str(m)
        and prod(int(d) for d in str(m**2)) % prod(int(d) for d in str(m)) == 0
    )


def A046738(n):
    a = b = (0, 0, 1 % n)
    for m in count(1):
        b = b[1:] + (sum(b) % n,)
        if a == b:
            return m


def A106302(n):
    a = b = (0,) * 2 + (1 % (p := prime(n)),)
    for m in count(1):
        b = b[1:] + (sum(b) % p,)
        if a == b:
            return m


def A195199(n):
    f = Counter(factorint(n))
    d = prod(e + 1 for e in f.values())
    for m in count(2):
        if prod(e + 1 for e in (f + Counter(factorint(m))).values()) > 2 * d:
            return m * n


def A351126(n):
    f = Counter(factorint(n))
    d = prod(e + 1 for e in f.values())
    for m in count(2):
        if prod(e + 1 for e in (f + Counter(factorint(m))).values()) > 2 * d:
            return m


def A037276(n):
    return (
        1
        if n == 1
        else int("".join(str(d) for d in sorted(factorint(n, multiple=True))))
    )


def A351975_gen(startvalue=1):  # generator of terms
    for k in count(max(startvalue, 1)):
        c = 0
        for d in sorted(factorint(k, multiple=True)):
            c = (c * 10 ** len(str(d)) + d) % k
        if c == k - 1:
            yield k


def A349705_gen(startvalue=1):  # generator of terms
    for k in count(max(startvalue, 1)):
        c = 0
        for d in sorted(factorint(k, multiple=True)):
            c = (c * 10 ** len(str(d)) + d) % k
        if c == 1:
            yield k


def A347859(n):
    return (
        n // 2
        if n % 2 == 0 and isprime(n // 2)
        else 3 * (n - 1) // 2
        if n % 2 and isprime((n - 1) // 2)
        else n
    )


def A340592(n):
    c = 0
    for d in sorted(factorint(n, multiple=True)):
        c = (c * 10 ** len(str(d)) + d) % n
    return c


def A001178(n):
    m = n
    for c in count(0):
        k = A001175(m)
        if k == m:
            return c
        m = k


def A351989(n):
    return fibonacci((p := prime(n)) - jacobi_symbol(p, 5)) % p**3


def A352038(n):
    return prod(
        (p ** (10 * (e + 1)) - 1) // (p**10 - 1)
        for p, e in factorint(n).items()
        if p > 2
    ) - (n**10 if n % 2 else 0)


def A352047(n):
    return (
        prod(
            p**e if p == 2 else (p ** (e + 1) - 1) // (p - 1)
            for p, e in factorint(n).items()
        )
        - n % 2
    )


def A351619(n):
    return (0 if n % 2 else 2) - len(primefactors(n))


def A352023_gen():  # generator of terms
    yield from (2, 3, 5)
    p = 7
    while True:
        if "9" not in str(10 ** (n_order(10, p)) // p):
            yield p
        p = nextprime(p)


def A187614_gen():  # generator of terms
    yield from (2, 3, 5)
    p = 7
    while True:
        if len(set("0" + str(10 ** (n_order(10, p)) // p))) < 10:
            yield p
        p = nextprime(p)


def A216664_gen(startvalue=1):  # generator of terms
    for n in count(max(startvalue + 1 - startvalue % 2, 1), 2):
        if 10 ** ((n + 1) // 2) // n % 10 == 9:
            yield n


def A351782(n):
    return n - 1 - int(n % 4 == 0)


def A050795_gen(startvalue=2):  # generator of terms
    for k in count(max(startvalue, 2)):
        if all(
            map(lambda d: d[0] % 4 != 3 or d[1] % 2 == 0, factorint(k**2 - 1).items())
        ):
            yield k


def A140612_gen(startvalue=0):  # generator of terms
    for k in count(max(startvalue, 0)):
        if all(
            starmap(
                lambda d, e: e % 2 == 0 or d % 4 != 3, factorint(k * (k + 1)).items()
            )
        ):
            yield k


def A351211(n):
    return integer_nthroot(3 * 10 ** (14 * (n - 1)), 14)[0] % 10


def A351210(n):
    return integer_nthroot(3 * 10 ** (13 * (n - 1)), 13)[0] % 10


def A351209(n):
    return integer_nthroot(3 * 10 ** (12 * (n - 1)), 12)[0] % 10


def A351208(n):
    return integer_nthroot(3 * 10 ** (11 * (n - 1)), 11)[0] % 10


def A246711(n):
    return integer_nthroot(3 * 10 ** (10 * (n - 1)), 10)[0] % 10


def A011273(n):
    return integer_nthroot(9 * 10 ** (19 * (n - 1)), 19)[0] % 10


def A352152(n):
    return int(
        "".join(
            "".join(list(g) if k else list(g)[::-1])
            for k, g in groupby(str(n), key=lambda x: x == "0")
        )
    )


@lru_cache(maxsize=None)
def A006165(n):
    return 1 if n <= 2 else A006165(n // 2) + A006165((n + 1) // 2)


@lru_cache(maxsize=None)
def A060973(n):
    return n - 1 if n <= 2 else A060973(n // 2) + A060973((n + 1) // 2)


@lru_cache(maxsize=None)
def A283187(n):
    return (
        n
        if n <= 1
        else A283187(n // 2) + (-1 if A283187((n + 1) // 2) % 2 else 1)
        if n % 2
        else 2 * A283187(n // 2)
    )


@lru_cache(maxsize=None)
def A087808(n):
    return 0 if n == 0 else A087808(n // 2) + (1 if n % 2 else A087808(n // 2))


def A352179_gen(startvalue=1):  # generator of terms
    k = max(startvalue, 1)
    k14 = 14**k
    while True:
        if str(k14)[:2] == "14":
            yield k
        k += 1
        k14 *= 14


def A352239_gen():  # generator of terms
    for l in count(0):
        k14 = 14 ** (14 * 10**l)
        for k in range(14 * 10**l, 15 * 10**l):
            if str(k14)[:2] == "14":
                yield k
            k14 *= 14


def A053646(n):
    return min(n - (m := 2 ** (len(bin(n)) - 3)), 2 * m - n)


def A350809(n):
    return len(set(p - n % p for p in primerange(2, n + 1)))


def A352232(n):
    return (2 ** n_order(2, p := prime(n)) - 1) // p


def A351985(n):
    return abs(sum((-1 if a % 2 else 1) * int(b) ** 3 for a, b in enumerate(str(n))))


def A352296(n):
    if n == 0:
        return 1
    pset, plist, pmax = {2}, [2], 4
    for m in count(2):
        if m > pmax:
            plist.append(nextprime(plist[-1]))
            pset.add(plist[-1])
            pmax = plist[-1] + 2
        c = 0
        for p in plist:
            if 2 * p > m:
                break
            if m - p in pset:
                c += 1
        if c == n:
            return m


def A014494(n):
    return (2 * n + 1) * (n + n % 2)


def A352115(n):
    return (n + 1) * (2 * n * (n + 2) + 3 * (n % 2)) // 3


def A351653(n):
    return int("".join(str(len(list(g))) for k, g in groupby(str(n))))


def A318927(n):
    return int("".join(str(len(list(g))) for k, g in groupby(bin(n)[2:])))


def A318926(n):
    return int("".join(str(len(list(g))) for k, g in groupby(bin(n)[:1:-1])))


def A352187_gen():  # generator of terms
    bset, blist, mmax = {1, 2}, [1, 2], 3
    yield from blist
    while True:
        for m in count(mmax):
            if gcd(m, blist[-1]) > 1 and m not in bset:
                if (
                    all(blist[-2] % p == 0 for p in primefactors(blist[-1]))
                    or gcd(m, blist[-2]) == 1
                ):
                    yield m
                    blist = [blist[-1], m]
                    bset.add(m)
                    while mmax in bset:
                        mmax += 1
                    break


def A352191_gen():  # generator of terms
    bset, blist, mmax, c = {1, 2}, [1, 2], 3, 2
    yield from blist
    while True:
        for m in count(mmax):
            if gcd(m, blist[-1]) > 1 and m not in bset:
                if (
                    all(blist[-2] % p == 0 for p in primefactors(blist[-1]))
                    or gcd(m, blist[-2]) == 1
                ):
                    if m > c:
                        yield m
                        c = m
                    blist = [blist[-1], m]
                    bset.add(m)
                    while mmax in bset:
                        mmax += 1
                    break


def A352192_gen():  # generator of terms
    bset, blist, mmax, c = {1, 2}, [1, 2], 3, 2
    yield from blist
    for n in count(3):
        for m in count(mmax):
            if gcd(m, blist[-1]) > 1 and m not in bset:
                if (
                    all(blist[-2] % p == 0 for p in primefactors(blist[-1]))
                    or gcd(m, blist[-2]) == 1
                ):
                    if m > c:
                        yield n
                        c = m
                    blist = [blist[-1], m]
                    bset.add(m)
                    while mmax in bset:
                        mmax += 1
                    break


def A055085(n):  # assumes n <= 62
    dlist = tuple(gmpy2digits(d, n) for d in range(n))
    for l in count(n - 1):
        for t in product(dlist, repeat=l - n + 1):
            for d in range(1, n):
                for u in multiset_permutations(sorted(t + dlist[:d] + dlist[d + 1 :])):
                    m = mpz("".join((dlist[d],) + tuple(u)), n)
                    for b in range(n - 1, 1, -1):
                        if len(set(gmpy2digits(m, b))) < b:
                            break
                    else:
                        return int(m)


def A351426(n):  # assumes n <= 62
    if n == 2:
        return 1
    dlist = tuple(gmpy2digits(d, n) for d in range(n))
    for l in count(n - 2):
        for d in range(1, n):
            c = None
            for t in product(dlist, repeat=l - n + 2):
                for u in multiset_permutations(sorted(t + dlist[1:d] + dlist[d + 1 :])):
                    m = mpz("".join((dlist[d],) + tuple(u)), n)
                    for b in range(n - 1, 1, -1):
                        if len(set(gmpy2digits(m, b)) | {"0"}) < b:
                            break
                    else:
                        if c != None:
                            c = min(m, c)
                        else:
                            c = m
            if c != None:
                return int(c)


def A352447_gen():  # generator of terms
    yield 1
    a = Counter()
    for k in count(2):
        b = Counter(factorint(k - 1))
        if all(b[p] <= a[p] for p in b):
            yield k
        a += b


def A352142_gen(startvalue=1):  # generator of terms
    return filter(
        lambda k: all(
            map(lambda x: x[1] % 2 and primepi(x[0]) % 2, factorint(k).items())
        ),
        count(max(startvalue, 1)),
    )


def A352141_gen(startvalue=1):  # generator of terms
    return filter(
        lambda k: all(
            map(lambda x: not (x[1] % 2 or primepi(x[0]) % 2), factorint(k).items())
        ),
        count(max(startvalue, 1)),
    )


@lru_cache(maxsize=None)
def A109129(n):
    if n <= 2:
        return n - 1
    if isprime(n):
        return A109129(primepi(n))
    return sum(e * A109129(p) for p, e in factorint(n).items())


@lru_cache(maxsize=None)
def A061775(n):
    if n == 1:
        return 1
    if isprime(n):
        return 1 + A061775(primepi(n))
    return 1 + sum(e * (A061775(p) - 1) for p, e in factorint(n).items())


@lru_cache(maxsize=None)
def A196050(n):
    if n == 1:
        return 0
    if isprime(n):
        return 1 + A196050(primepi(n))
    return sum(e * A196050(p) for p, e in factorint(n).items())


@lru_cache(maxsize=None)
def A109082(n):
    if n == 1:
        return 0
    if isprime(n):
        return 1 + A109082(primepi(n))
    return max(A109082(p) for p in primefactors(n))


def A351928(n):
    kmax, m = 3**n, (3 ** (n - 1)).bit_length()
    k2 = pow(2, m, kmax)
    for k in count(m):
        a = k2
        while a > 0:
            a, b = divmod(a, 3)
            if b == 2:
                break
        else:
            return k
        k2 = 2 * k2 % kmax


def A351927(n):
    kmax, m = 3**n, (3 ** (n - 1)).bit_length()
    k2 = pow(2, m, kmax)
    for k in count(m):
        a = k2
        if 3 * a >= kmax:
            while a > 0:
                a, b = divmod(a, 3)
                if b == 0:
                    break
            else:
                return k
        k2 = 2 * k2 % kmax


def A030298_gen():  # generator of terms
    return chain.from_iterable(p for l in count(2) for p in permutations(range(1, l)))


def A061077(n):
    return sum(prod(int(d) for d in str(2 * i + 1)) for i in range(n))


def A061078(n):
    return sum(prod(int(d) for d in str(2 * i + 2)) for i in range(n))


def A061076(n):
    return sum(prod(int(d) for d in str(i)) for i in range(1, n + 1))


def A352329_gen():  # generator of terms
    for l in count(1):
        if (r := l * (l + 1) // 2 % 9) == 0 or r == 1 or r == 4 or r == 7:
            m = tuple(10 ** (l - i - 1) for i in range(l))
            for p in permutations(range(1, l + 1)):
                if integer_nthroot(n := sum(prod(k) for k in zip(m, p)), 2)[1]:
                    yield n


def A352346_gen():  # generator of terms
    n1, m1, n2, m2 = 1, 1, 2, 2
    while True:
        if m1 == m2:
            yield m1
        k = 0
        while k == 0:
            n1 += 2
            m1 += (k := prod(int(d) for d in str(n1)))
        while m2 < m1:
            n2 += 2
            m2 += prod(int(d) for d in str(n2))


def A352601(n):
    return rf(2 * n, n)


def A124320_T(n, k):
    return rf(n, k)


def A351826(n):
    for k in count(1, 2):
        c = 0
        for j in count(1):
            if k - 2**j < 2:
                break
            if isprime(k - 2**j) and isprime(k + 2**j):
                c += 1
            if c > n:
                break
        if c == n:
            return k


def A352420(n):
    return len(
        set().union(
            *(
                primefactors((p ** ((e + 1) * n) - 1) // (p**n - 1))
                for p, e in factorint(n).items()
            )
        )
    )


def A352535_gen(startvalue=0):  # generator of terms
    return filter(
        lambda m: not sum(
            int(d) ** 2 * (-1 if i % 2 else 1) for i, d in enumerate(str(m))
        ),
        count(max(startvalue, 0)),
    )


def A351319(n):
    return n if n <= 2 else int((k := isqrt(n)) ** 2 + k - n + 1 > 0)


def A352155_gen(startvalue=1):  # generator of terms
    for n in count(max(startvalue, 1)):
        m2, m5 = multiplicity(2, n), multiplicity(5, n)
        k, m = 10 ** max(m2, m5), 10 ** (t := n_order(10, n // 2**m2 // 5**m5)) - 1
        c = k // n
        s = str(m * k // n - c * m).zfill(t)
        if s == "0" and min(str(c)) == "1":
            yield n
        elif "0" not in s and min(str(c).lstrip("0") + s) == "1":
            yield n


def A352156_gen(startvalue=1):  # generator of terms
    for n in count(max(startvalue, 1)):
        m2, m5 = multiplicity(2, n), multiplicity(5, n)
        k, m = 10 ** max(m2, m5), 10 ** (t := n_order(10, n // 2**m2 // 5**m5)) - 1
        c = k // n
        s = str(m * k // n - c * m).zfill(t)
        if s == "0" and min(str(c)) == "2":
            yield n
        elif "0" not in s and min(str(c).lstrip("0") + s) == "2":
            yield n


def A352157_gen(startvalue=1):  # generator of terms
    for n in count(max(startvalue, 1)):
        m2, m5 = multiplicity(2, n), multiplicity(5, n)
        k, m = 10 ** max(m2, m5), 10 ** (t := n_order(10, n // 2**m2 // 5**m5)) - 1
        c = k // n
        s = str(m * k // n - c * m).zfill(t)
        if "0" not in s and min(str(c).lstrip("0") + s) == "3":
            yield n


def A352158_gen(startvalue=1):  # generator of terms
    for n in count(max(startvalue, 1)):
        m2, m5 = multiplicity(2, n), multiplicity(5, n)
        k, m = 10 ** max(m2, m5), 10 ** (t := n_order(10, n // 2**m2 // 5**m5)) - 1
        c = k // n
        s = str(m * k // n - c * m).zfill(t)
        if s == "0" and min(str(c)) == "4":
            yield n
        elif "0" not in s and min(str(c).lstrip("0") + s) == "4":
            yield n


def A352159_gen(startvalue=1):  # generator of terms
    for n in count(max(startvalue, 1)):
        m2, m5 = multiplicity(2, n), multiplicity(5, n)
        k, m = 10 ** max(m2, m5), 10 ** (t := n_order(10, n // 2**m2 // 5**m5)) - 1
        c = k // n
        s = str(m * k // n - c * m).zfill(t)
        if s == "0" and min(str(c)) == "5":
            yield n
        elif "0" not in s and min(str(c).lstrip("0") + s) == "5":
            yield n


def A352160_gen(startvalue=1):  # generator of terms
    for n in count(max(startvalue, 1)):
        m2, m5 = multiplicity(2, n), multiplicity(5, n)
        k, m = 10 ** max(m2, m5), 10 ** (t := n_order(10, n // 2**m2 // 5**m5)) - 1
        c = k // n
        s = str(m * k // n - c * m).zfill(t)
        if "0" not in s and min(str(c).lstrip("0") + s) == "6":
            yield n


if sys.version_info < (3, 10):

    def A352631(n):
        return (
            -1
            if n == 2
            else min(
                bin(k**2)[2:].count("0")
                for k in range(1 + isqrt(2 ** (n - 1) - 1), 1 + isqrt(2**n))
            )
        )

else:

    def A352631(n):
        return (
            -1
            if n == 2
            else min(
                n - (k**2).bit_count()
                for k in range(1 + isqrt(2 ** (n - 1) - 1), 1 + isqrt(2**n))
            )
        )


def A352375_gen():  # generator of terms
    a = 5
    while True:
        yield (s := sum(int(d) for d in str(a)))
        a += s


def A016096_gen():  # generator of terms
    a = 9
    while True:
        yield a
        a += sum(int(d) for d in str(a))


def A350813(n):
    m = prod(islice(filter(lambda p: p % 4 == 1, sieve), n))
    a = isqrt(m)
    d = max(filter(lambda d: d <= a, divisors(m, generator=True)))
    return (m // d - d) // 2


def A349708(n):
    m = primorial(n + 1) // 2
    a = isqrt(m)
    d = max(filter(lambda d: d <= a, divisors(m, generator=True)))
    return (m // d - d) // 2


@lru_cache(maxsize=None)
def A000793(n):
    return 1 if n == 0 else max(lcm(i, A000793(n - i)) for i in range(1, n + 1))


def A352715_gen():  # generator of terms
    yield 1
    l1, s, b, bli = 1, 2, set(), 0
    while True:
        i = s
        while True:
            if not (i in b or bin(i & l1).count("1") != bli):
                yield i
                l1 = i
                bli = l1.bit_length() // 2
                b.add(i)
                while s in b:
                    b.remove(s)
                    s += 1
                break
            i += 1


def A352716_gen():  # generator of terms
    yield 1
    l1, s, b = 1, 2, set()
    while True:
        i = s
        while True:
            if not (i in b or bin(i & l1).count("1") % 2):
                yield i
                l1 = i
                b.add(i)
                while s in b:
                    b.remove(s)
                    s += 1
                break
            i += 1


def A000037(n):
    return n + isqrt(n + isqrt(n))


def A000037_gen(startvalue=1):  # generator of terms
    k = isqrt(max(startvalue, 1))
    for m in count(k):
        yield from range(m**2 + 1, (m + 1) ** 2)


def A000217(n):
    return n * (n + 1) // 2


def A000196(n):
    return isqrt(n)


def A086849(n):
    return (m := n + isqrt(n + isqrt(n))) * (m + 1) // 2 - (k := isqrt(m)) * (k + 1) * (
        2 * k + 1
    ) // 6


def A086849_gen():  # generator of terms
    c, k = 0, 1
    while True:
        for n in range(k**2 + 1, (k + 1) ** 2):
            c += n
            yield c
        k += 1


def A352738_gen():  # generator of terms
    c, k, ks, m, ms = 0, 1, 2, 1, 1
    while True:
        for n in range(ks, ks + 2 * k):
            c += n
            if c == ms:
                yield c
            elif c > ms:
                ms += 2 * m + 1
                m += 1
        ks += 2 * k + 1
        k += 1


def A308485(n):
    return sum(
        p * e
        for m in range(prime(n) + 1, prime(n + 1))
        for p, e in factorint(m).items()
    )


def A351855_gen():  # generator of terms
    c, k, ks, m, p, q = 0, 1, 2, 1, 4, 5
    while True:
        for n in range(ks, ks + 2 * k):
            c += n
            if c == m:
                yield c
            else:
                while c > m:
                    m += p
                    p += 1
                    if p == q:
                        q = nextprime(q)
                        p += 1
        ks += 2 * k + 1
        k += 1


def A352813(n):
    m = factorial(2 * n)
    return (
        0
        if n == 0
        else min(
            abs((p := prod(d)) - m // p)
            for d in combinations(range(2, 2 * n + 1), n - 1)
        )
    )


def A038667(n):
    m = factorial(n)
    return (
        0
        if n == 0
        else min(
            abs((p := prod(d)) - m // p)
            for l in range(n, n // 2, -1)
            for d in combinations(range(1, n + 1), l)
        )
    )


def A061057(n):
    k = factorial(n)
    m = max(d for d in divisors(k, generator=True) if d <= isqrt(k))
    return k // m - m


def A263292(n):
    m = factorial(n)
    return (
        1
        if n == 0
        else len(
            set(
                abs((p := prod(d)) - m // p)
                for l in range(n, n // 2, -1)
                for d in combinations(range(1, n + 1), l)
            )
        )
    )


def A200744(n):
    m = factorial(n)
    return min(
        (abs((p := prod(d)) - m // p), max(p, m // p))
        for l in range(n, n // 2, -1)
        for d in combinations(range(1, n + 1), l)
    )[1]


def A200743(n):
    m = factorial(n)
    return min(
        (abs((p := prod(d)) - m // p), min(p, m // p))
        for l in range(n, n // 2, -1)
        for d in combinations(range(1, n + 1), l)
    )[1]


def A351744(n):
    return int(str(n).translate({48: 49, 50: 51, 52: 53, 54: 55, 56: 57}))


def A106747(n):
    return int(
        str(n).translate(
            {49: 48, 50: 49, 51: 49, 52: 50, 53: 50, 54: 51, 55: 51, 56: 52, 57: 52}
        )
    )


def A107130(n):
    return int(str(n).translate({49: 48, 51: 49, 53: 50, 55: 51, 57: 52}))


def A306436(n):
    return int(
        str(n).translate(
            {
                48: 49,
                49: 48,
                50: 51,
                51: 50,
                52: 53,
                53: 52,
                54: 55,
                55: 54,
                56: 57,
                57: 56,
            }
        )
    )


def A107128(n):
    return int(str(n).translate({50: 49, 52: 50, 54: 51, 56: 52}))


def A352788_gen():  # generator of terms
    c, m, ms = 0, 1, 1
    for n in count(1):
        c += 1 if n <= 2 else n * totient(n) // 2
        if c == ms:
            yield c
        else:
            while c > ms:
                ms += 2 * m + 1
                m += 1


def A352148_gen():  # generator of terms
    yield 0
    for l in count(0):
        for d in range(1, 10):
            for m in range(2**l, 2 ** (l + 1)):
                a, b = integer_nthroot(8 * d * int(bin(m)[2:]) + 1, 2)
                if b:
                    yield (a - 1) // 2


def A353243_gen():  # generator of terms
    k, c = Fraction(), 0
    for n in count(1):
        k += Fraction(1, n)
        if c < (m := max(continued_fraction(k))):
            c = m
            yield n


def A353244_gen():  # generator of terms
    k, c = Fraction(), 0
    for n in count(1):
        k += Fraction(1, n)
        if c < (m := max(continued_fraction(k))):
            yield (c := m)


def A023896(n):
    return 1 if n == 1 else n * totient(n) // 2


def A103181(n):
    return int("".join(str(int(d) % 2) for d in str(n)))


def A352881(n):
    from sympy.abc import y, z

    zc = Counter()
    for x in range(1, 10**n + 1):
        for d in diophantine(z * (x + y) - x * y):
            if x <= d[0] <= 10 ** n and d[1] >= 0:
                zc[d[1]] += 1
    return sorted(zc.items(), key=lambda x: (-x[1], x[0]))[0][0]


def A352635(n):
    cset, iset = set(), set()
    for i in range(n):
        if i not in iset:
            j, jset, jlist = i, set(), []
            while j not in jset:
                jset.add(j)
                jlist.append(j)
                iset.add(j)
                j = (j**2 + 1) % n
            cset.add(min(jlist[jlist.index(j) :]))
    return len(cset)


@lru_cache(maxsize=None)
def A352969_set(n):
    if n == 0:
        return {1}
    return set(
        sum(x) for x in combinations_with_replacement(A352969_set(n - 1), 2)
    ) | set(prod(x) for x in combinations_with_replacement(A352969_set(n - 1), 2))


def A353969(n):
    return len(A352969_set(n))


def A263995(n):
    return len(
        set(sum(x) for x in combinations_with_replacement(range(1, n + 1), 2))
        | set(prod(x) for x in combinations_with_replacement(range(1, n + 1), 2))
    )


def A352040(n):
    k = 10 * n - 1 + int(ceiling((10 * n - 1) * log(5, 2)))
    s = str(c := 2**k)
    while any(s.count(d) < n for d in "0123456789"):
        c *= 2
        k += 1
        s = str(c)
    return k


@lru_cache(maxsize=None)
def A352289(n):
    return 1 if n == 1 else 2 * prime(A352289(n - 1))


def A064989(n):
    return prod(1 if p == 2 else prevprime(p) * e for p, e in factorint(n).items())


def A252463(n):
    return A064989(n) if n % 2 else n // 2


def A353412(n):
    return int(
        bin(
            prod(1 if p == 2 else prevprime(p) * e for p, e in factorint(n).items())
            if n % 2
            else n // 2
        )[2:].rstrip("0"),
        2,
    )


def A051064(n):
    c = 1
    a, b = divmod(n, 3)
    while b == 0:
        a, b = divmod(a, 3)
        c += 1
    return c


def A352992(n):
    n10, n7 = 10**n, (10**n - 1) * 7 // 9
    for m in count(1):
        a, b = divmod(m**3, n10)
        if b == n7 and a % 10 != 7:
            return m


def A351374_gen():  # generator of terms
    for k in range(1, 157):
        a = tuple(i**k for i in range(20))
        yield from (
            x[0]
            for x in sorted(
                filter(
                    lambda x: x[0] > 0
                    and tuple(sorted(sympydigits(x[0], 20)[1:])) == x[1],
                    (
                        (sum(map(lambda y: a[y], b)), b)
                        for b in combinations_with_replacement(range(20), k)
                    ),
                )
            )
        )


def A010354_gen():  # generator of terms
    for k in range(1, 30):
        a = tuple(i**k for i in range(8))
        yield from (
            x[0]
            for x in sorted(
                filter(
                    lambda x: x[0] > 0
                    and tuple(int(d, 8) for d in sorted(oct(x[0])[2:])) == x[1],
                    (
                        (sum(map(lambda y: a[y], b)), b)
                        for b in combinations_with_replacement(range(8), k)
                    ),
                )
            )
        )


def A161953_gen():  # generator of terms
    for k in range(1, 74):
        a = tuple(i**k for i in range(16))
        yield from (
            x[0]
            for x in sorted(
                filter(
                    lambda x: x[0] > 0
                    and tuple(int(d, 16) for d in sorted(hex(x[0])[2:])) == x[1],
                    (
                        (sum(map(lambda y: a[y], b)), b)
                        for b in combinations_with_replacement(range(16), k)
                    ),
                )
            )
        )


def A352065(n):
    plist = [prime(k) for k in range(1, 2 * n + 2)]
    pd = prod(plist)
    while True:
        mlist = [nextprime(pd // (2 * n + 1) - 1)]
        for _ in range(n):
            mlist = [prevprime(mlist[0])] + mlist + [nextprime(mlist[-1])]
        if sum(mlist) <= pd:
            while (s := sum(mlist)) <= pd:
                if s == pd:
                    return plist[0]
                mlist = mlist[1:] + [nextprime(mlist[-1])]
        else:
            while (s := sum(mlist)) >= pd:
                if s == pd:
                    return plist[0]
                mlist = [prevprime(mlist[0])] + mlist[:-1]
        pd //= plist[0]
        plist = plist[1:] + [nextprime(plist[-1])]
        pd *= plist[-1]


def A353073_gen(startvalue=3):  # generator of terms
    q = nextprime(max(startvalue, 3) - 1)
    p, r = prevprime(q), nextprime(q)
    while True:
        if integer_nthroot(q - p, 2)[1] and integer_nthroot(r - q, 2)[1]:
            yield q
        t = q
        for i in count(1):
            t += 2 * i - 1
            if t >= r:
                break
            if integer_nthroot(r - t, 2)[1]:
                yield t
        p, q, r = q, r, nextprime(r)


def A007918(n):
    return nextprime(n - 1)


def A353088_gen():  # generator of terms
    p, q, g, h = 3, 5, True, False
    while True:
        if g and h:
            yield p
        p, q = q, nextprime(q)
        g, h = h, integer_nthroot(q - p, 2)[1]


def A353087(n):
    k, m, r = 1, 1, 10 ** (10 * n - 1)
    while m < r:
        k += 1
        m *= k
    s = str(m)
    while any(s.count(d) < n for d in "0123456789"):
        k += 1
        m *= k
        s = str(m)
    return k


def A353054_gen():  # generator of terms
    for l in count(1):
        a, b = 10**l - 2, 10 ** (l - 1) - 2
        for m in range(1, 10):
            q, r = divmod(m * a - 1, 19)
            if r == 0 and b <= q - 2 <= a:
                yield 10 * q + m


def A034180_gen():  # generator of terms
    for l in count(1):
        clist = []
        for k in range(1, 10):
            a, b = 10**l - k, 10 ** (l - 1) - k
            for m in range(1, 10):
                q, r = divmod(m * a - 1, 10 * k - 1)
                if r == 0 and b <= q - k <= a:
                    clist.append(10 * q + m)
        yield from sorted(clist)


def A035126_gen():  # generator of terms
    for l in count(0):
        l1, l2 = 10 ** (l + 1), 10**l
        yield from sorted(
            set(
                x**2
                for z in (diop_DN(10, m * (1 - l1)) for m in range(10))
                for x, y in z
                if l1 >= x**2 >= l2
            )
        )


def A035127_gen():  # generator of terms
    for l in count(0):
        l1, l2 = 10 ** (l + 1), 10**l
        yield from sorted(
            set(
                y**2
                for z in (diop_DN(10, m * (1 - l1)) for m in range(10))
                for x, y in z
                if l1 >= x**2 >= l2
            )
        )


def A045877_gen():  # generator of terms
    for l in count(0):
        l1, l2 = 10 ** (l + 1), 10**l
        yield from sorted(
            set(
                abs(x)
                for z in (diop_DN(10, m * (1 - l1)) for m in range(10))
                for x, y in z
                if l1 >= x**2 >= l2
            )
        )


def A045878_gen():  # generator of terms
    for l in count(0):
        l1, l2 = 10 ** (l + 1), 10**l
        yield from sorted(
            set(
                abs(y)
                for z in (diop_DN(10, m * (1 - l1)) for m in range(10))
                for x, y in z
                if l1 >= x**2 >= l2
            )
        )


def A353220(n):
    return reduce(lambda x, _: (3 * x + 1) // 2, range(n), n)


def A353215(n):
    return reduce(lambda x, _: (3 * x - 1) // 2, range(n), n)


def A353613_gen(startvalue=1):  # generator of terms
    for m in count(max(startvalue, 1)):
        m2, m5 = multiplicity(2, m), multiplicity(5, m)
        if set(
            str(10 ** (max(m2, m5) + n_order(10, m // 2**m2 // 5**m5)) // m)
        ) <= {"0", "2", "4", "6", "8"}:
            yield m


def A353614_gen(startvalue=1):  # generator of terms
    for n in count(max(startvalue, 1)):
        m2, m5 = multiplicity(2, n), multiplicity(5, n)
        k, m = 10 ** max(m2, m5), 10 ** (t := n_order(10, n // 2**m2 // 5**m5)) - 1
        c = k // n
        s = str(m * k // n - c * m).zfill(t)
        if set(str(c).lstrip("0") + ("" if int(s) == 0 else s)) <= {
            "1",
            "3",
            "5",
            "7",
            "9",
        }:
            yield n


def A338754(n):
    return int("".join(d * 2 for d in str(n)))


def A338086(n):
    return int("".join(d * 2 for d in gmpy2digits(n, 3)), 3)


def A351501(n):
    return comb(m := n**2 + n - 1, n) // m


def A099306(n):
    return A003415(A003415(A003415(n)))


def A068346(n):
    return A003415(A003415(n))


def A353691_helper(n):
    f = factorint(n).items()
    return prod(p**e * (p - 1) * (e + 1) for p, e in f), prod(
        p ** (e + 1) - 1 for p, e in f
    )


def A353691(n):
    Hnp, Hnq = A353691_helper(n)
    g = gcd(Hnp, Hnq)
    Hnp //= g
    Hnq //= g
    k = n + 1
    Hkp, Hkq = A353691_helper(k)
    while (Hkp * Hnq) % (Hkq * Hnp):
        k += 1
        Hkp, Hkq = A353691_helper(k)
    return k


def A352940(n):
    return (isqrt(n**2 * (n * (2 * n - 4) + 2) + 1) - 1) // 2


def A353709_gen():  # generator of terms
    s, a, b, c, ab = {0, 1}, 0, 1, 2, 1
    yield from (0, 1)
    while True:
        for n in count(c):
            if not (n & ab or n in s):
                yield n
                a, b = b, n
                ab = a | b
                s.add(n)
                while c in s:
                    c += 1
                break


def A000005(n):
    return divisor_count(n)


def A000010(n):
    return totient(n)


def A000027(n):
    return n


def A005117_gen(startvalue=1):
    return filter(
        lambda n: all(x == 1 for x in factorint(n).values()), count(max(startvalue, 1))
    )


if sys.version_info >= (3, 10):

    def A000069_gen(startvalue=0):
        return filter(lambda n: n.bit_count() % 2, count(max(startvalue, 0)))

    def A001969_gen(startvalue=0):
        return filter(lambda n: not n.bit_count() % 2, count(max(startvalue, 0)))

else:

    def A000069_gen(startvalue=0):
        return filter(lambda n: bin(n).count("1") % 2, count(max(startvalue, 0)))

    def A001969_gen(startvalue=0):
        return filter(lambda n: not bin(n).count("1") % 2, count(max(startvalue, 0)))


def A002654(n):
    return prod(
        1 if p == 2 else (e + 1 if p & 3 == 1 else (e + 1) & 1)
        for p, e in factorint(n).items()
    )


def A004018(n):
    return (
        prod(
            1 if p == 2 else (e + 1 if p & 3 == 1 else (e + 1) & 1)
            for p, e in factorint(n).items()
        )
        << 2
    )


def A353710_gen():  # generator of terms
    s, a, b, c, ab = {0, 1}, 0, 1, 2, 1
    yield from (0, 1)
    while True:
        for n in count(c):
            if not (n & ab or n in s):
                yield c
                a, b = b, n
                ab = a | b
                s.add(n)
                while c in s:
                    c += 1
                break


def A353718_gen():  # generator of terms
    s, a, b, c, ab, k = {0, 1}, 0, 1, 2, 1, 1
    yield from (1, 1)
    while True:
        for n in count(c):
            if not (n & ab or n in s):
                a, b = b, n
                ab = a | b
                s.add(n)
                if c in s:
                    yield k
                    k = 0
                    while c in s:
                        c += 1
                k += 1
                break


def A048785(n):
    return 0 if n == 0 else prod(3 * e + 1 for e in factorint(n).values())


def A353551(n):
    return sum(prod(3 * e + 1 for e in factorint(k).values()) for k in range(1, n + 1))


def A061503(n):
    return sum(prod(2 * e + 1 for e in factorint(k).values()) for k in range(1, n + 1))


def A353789(n):
    return prod(
        (q := nextprime(p)) ** (e - 1) * p**e * (q - 1)
        for p, e in factorint(n).items()
    )


def A003961(n):
    return prod(nextprime(p) ** e for p, e in factorint(n).items())


def A353906(n):
    return sum(
        (-1 if i % 2 else 1) * int(j) for i, j in enumerate(str(n)[::-1])
    ) ** len(str(n))


def A055017(n):
    return sum((-1 if i % 2 else 1) * int(j) for i, j in enumerate(str(n)[::-1]))


def A002997_gen():  # generator of terms
    p, q = 3, 5
    while True:
        for n in range(p + 2, q, 2):
            f = factorint(n)
            if max(f.values()) == 1 and not any((n - 1) % (p - 1) for p in f):
                yield n
        p, q = q, nextprime(q)


def A352970_gen():  # generator of terms
    p, q = 3, 5
    while True:
        for n in range(p + 11 - ((p + 2) % 10), q, 10):
            f = factorint(n)
            if max(f.values()) == 1 and not any((n - 1) % (p - 1) for p in f):
                yield n
        p, q = q, nextprime(q)


def A011782(n):
    return 1 if n == 0 else 2 ** (n - 1)


def A353715_gen():  # generator of terms
    s, a, b, c, ab = {0, 1}, 0, 1, 2, 1
    yield 1
    while True:
        for n in count(c):
            if not (n & ab or n in s):
                yield b + n
                a, b = b, n
                ab = a | b
                s.add(n)
                while c in s:
                    c += 1
                break


def A353724_gen():  # generator of terms
    s, a, b, c, ab = {0, 1}, 0, 1, 2, 1
    yield 0
    while True:
        for n in count(c):
            if not (n & ab or n in s):
                yield len(t := bin(b + n)) - len(t.rstrip("0"))
                a, b = b, n
                ab = a | b
                s.add(n)
                while c in s:
                    c += 1
                break


def A070939(n):
    return 1 if n == 0 else n.bit_length()


if sys.version_info >= (3, 10):

    def A353986_gen():  # generator of terms
        a, b, k, ah = 1, 1, 1, 1
        while True:
            if ah == (bh := b.bit_count()):
                yield k
            a, b, ah = b, a + b, bh
            k += 1

    def A353987_gen():  # generator of terms
        b, c, k, ah, bh = 1, 2, 1, 1, 1
        while True:
            if ah == (ch := c.bit_count()) == bh:
                yield k
            b, c, ah, bh = c, b + c, bh, ch
            k += 1

else:

    def A353986_gen():  # generator of terms
        a, b, k, ah = 1, 1, 1, 1
        while True:
            if ah == (bh := bin(b).count("1")):
                yield k
            a, b, ah = b, a + b, bh
            k += 1

    def A353987_gen():  # generator of terms
        b, c, k, ah, bh = 1, 2, 1, 1, 1
        while True:
            if ah == (ch := bin(c).count("1")) == bh:
                yield k
            b, c, ah, bh = c, b + c, bh, ch
            k += 1


def A353728_gen():  # generator of terms
    yield 1
    l1, s, b = 1, 2, set()
    while True:
        i = s
        while True:
            if i & l1 and not i in b:
                yield int(bin(i)[2:])
                l1 = i
                b.add(i)
                while s in b:
                    b.remove(s)
                    s += 1
                break
            i += 1


if sys.version_info >= (3, 10):

    def A352202_gen():  # generator of terms
        yield 1
        l1, s, b = 1, 2, set()
        while True:
            i = s
            while True:
                if i & l1 and not i in b:
                    yield i.bit_count()
                    l1 = i
                    b.add(i)
                    while s in b:
                        b.remove(s)
                        s += 1
                    break
                i += 1

else:

    def A352202_gen():  # generator of terms
        yield 1
        l1, s, b = 1, 2, set()
        while True:
            i = s
            while True:
                if i & l1 and not i in b:
                    yield bin(i).count("1")
                    l1 = i
                    b.add(i)
                    while s in b:
                        b.remove(s)
                        s += 1
                    break
                i += 1


def A352979(n):
    return (
        n**2
        * (
            n
            * (
                n
                * (
                    n
                    * (
                        n
                        * (
                            n
                            * (
                                n
                                * (n * (n * (n * (35 * n + 450) + 2293) + 5700) + 6405)
                                + 770
                            )
                            - 3661
                        )
                        - 240
                    )
                    + 2320
                )
                + 40
            )
            - 672
        )
        // 13440
    )


def A353021(n):
    return (
        n
        * (
            n
            * (
                n
                * (
                    n
                    * (
                        n
                        * (
                            n
                            * (
                                n
                                * (
                                    n
                                    * (
                                        8
                                        * n
                                        * (n * (70 * n * (5 * n + 84) + 40417) + 144720)
                                        + 2238855
                                    )
                                    + 2050020
                                )
                                + 207158
                            )
                            - 810600
                        )
                        - 58505
                    )
                    + 322740
                )
                + 7956
            )
            - 45360
        )
        // 5443200
    )


def A353618_gen():  # generator of terms
    for b in count(1):
        q, c = 2, 8
        while c < b:
            d = (b - c) ** 2 * (b + c)
            s, t = divmod(d, c)
            if t == 0:
                a, r = integer_nthroot(s, 2)
                if r and b - c < a < b + c and gcd(a, b, q) == 1:
                    yield from (a, b, c)
            c += q * (3 * q + 3) + 1
            q += 1


def A353729_gen(startvalue=1):  # generator of terms
    for n in count(max(startvalue, 1)):
        s = str(n)
        if not (
            "0" in s
            or any(int("0" + s[:i] + s[i + 1 :]) % int(s[i]) for i in range(len(s)))
        ):
            yield n


def A268631(n):
    return (
        1
        - 2 * n
        + prod(p ** (e - 1) * ((p - 1) * e + p) for p, e in factorint(n).items())
    )


def A006579(n):
    return prod(p ** (e - 1) * ((p - 1) * e + p) for p, e in factorint(n).items()) - n


def A352980(n):
    return (
        n**2
        * (
            n
            * (
                n
                * (
                    n
                    * (
                        n
                        * (
                            n
                            * (
                                n * (n * (n * (n * (35 * n - 30) - 347) + 180) + 1365)
                                - 350
                            )
                            - 2541
                        )
                        + 240
                    )
                    + 2160
                )
                - 40
            )
            - 672
        )
        // 13440
    )


def A045584_gen(startvalue=1):  # generator of terms
    kstart = max(startvalue, 1)
    k3, k4 = 3**kstart, 4**kstart
    for k in count(kstart):
        if (k3 + k4) % k == 0:
            yield k
        k3 *= 3
        k4 *= 4


def A088534(n):
    c = 0
    for y in range(n + 1):
        if y**2 > n:
            break
        for x in range(y + 1):
            z = x * (x + y) + y**2
            if z > n:
                break
            elif z == n:
                c += 1
    return c


def A198775_gen(startvalue=1):  # generator of terms
    for n in count(max(startvalue, 1)):
        c = 0
        for y in range(n + 1):
            if c > 4 or y**2 > n:
                break
            for x in range(y + 1):
                z = x * (x + y) + y**2
                if z > n:
                    break
                elif z == n:
                    c += 1
                    if c > 4:
                        break
        if c == 4:
            yield n


def A335951_T(n, k):
    z = (
        simplify(
            (bernoulli(2 * n, (sqrt(8 * symbolx + 1) + 1) / 2) - bernoulli(2 * n, 1))
            / (2 * n)
        )
        .as_poly()
        .all_coeffs()
    )
    return z[n - k] * lcm(*(d.q for d in z))


def A335951_gen():  # generator of terms
    yield from (A335951_T(n, k) for n in count(0) for k in range(n + 1))


def A335952(n):
    return lcm(
        *(
            d.q
            for d in simplify(
                (
                    bernoulli(2 * n, (sqrt(8 * symbolx + 1) + 1) / 2)
                    - bernoulli(2 * n, 1)
                )
                / (2 * n)
            )
            .as_poly()
            .all_coeffs()
        )
    )


if sys.version_info >= (3, 10):

    def A354112(n):
        return sum(d.bit_count() for d in divisors(2**n - 1, generator=True))

else:

    def A354112(n):
        return sum(bin(d).count("1") for d in divisors(2**n - 1, generator=True))


def A353943(n):
    return (
        2**10 + 1
        if n == 1
        else int(nthroot_mod(1, (p := prime(n)) - 1, p**10, True)[1])
    )


def A353942(n):
    return (
        2**9 + 1
        if n == 1
        else int(nthroot_mod(1, (p := prime(n)) - 1, p**9, True)[1])
    )


def A353941(n):
    return (
        2**8 + 1
        if n == 1
        else int(nthroot_mod(1, (p := prime(n)) - 1, p**8, True)[1])
    )


def A353940(n):
    return (
        2**7 + 1
        if n == 1
        else int(nthroot_mod(1, (p := prime(n)) - 1, p**7, True)[1])
    )


def A353939(n):
    return (
        2**6 + 1
        if n == 1
        else int(nthroot_mod(1, (p := prime(n)) - 1, p**6, True)[1])
    )


def A353938(n):
    return (
        2**5 + 1
        if n == 1
        else int(nthroot_mod(1, (p := prime(n)) - 1, p**5, True)[1])
    )


def A353937(n):
    return (
        2**4 + 1
        if n == 1
        else int(nthroot_mod(1, (p := prime(n)) - 1, p**4, True)[1])
    )


def A249275(n):
    return (
        2**3 + 1
        if n == 1
        else int(nthroot_mod(1, (p := prime(n)) - 1, p**3, True)[1])
    )


def A034939(n):
    return int(sqrt_mod(-1, 5**n))


def A257833_T(n, k):
    return (
        2**k + 1
        if n == 1
        else int(nthroot_mod(1, (p := prime(n)) - 1, p**k, True)[1])
    )


def A257833_gen():  # generator of terms
    yield from (A257833_T(n, i - n + 2) for i in count(1) for n in range(i, 0, -1))


def A352395(n):
    return sum(
        Fraction(-1 if k % 2 else 1, 2 * k + 1) for k in range(n + 1)
    ).denominator


def A263445(n):
    return (2 * n + 1) * factorial(n + 1) * bernoulli(2 * n)


def A039678(n):
    return (
        2**2 + 1
        if n == 1
        else int(nthroot_mod(1, (p := prime(n)) - 1, p**2, True)[1])
    )


def A185103(n):
    z = nthroot_mod(1, n - 1, n**2, True)
    return int(z[0] + n**2 if len(z) == 1 else z[1])


def A256517(n):
    z = nthroot_mod(1, (c := composite(n)) - 1, c**2, True)
    return int(z[0] + c**2 if len(z) == 1 else z[1])


def A255885(n):
    for b in count(1):
        if n == sum(
            1 for c in range(2, b + 1) if not isprime(c) and pow(b, c - 1, c**2) == 1
        ):
            return b


def A255885_gen():  # generator of terms
    A255885_dict, n = {}, 1
    for b in count(1):
        d = sum(
            1 for c in range(2, b + 1) if not isprime(c) and pow(b, c - 1, c**2) == 1
        )
        if d not in A255885_dict:
            A255885_dict[d] = b
        if n in A255885_dict:
            yield A255885_dict[n]
            n += 1


def A255901(n):
    for b in count(1):
        if n == sum(1 for p in primerange(2, b + 1) if pow(b, p - 1, p**2) == 1):
            return b


def A255901_gen():  # generator of terms
    A255901_dict, n = {}, 1
    for b in count(1):
        c = sum(1 for p in primerange(2, b + 1) if pow(b, p - 1, p**2) == 1)
        if c not in A255901_dict:
            A255901_dict[c] = b
        if n in A255901_dict:
            yield A255901_dict[n]
            n += 1


def A287147_gen():  # generator of terms
    c, p = 5, 3
    yield 2
    while True:
        d = nthroot_mod(1, p - 1, p**2, True)[1]
        if d > c:
            c = d
            yield p
        p = nextprime(p)


def A353730_gen():  # generator of terms
    aset, aqueue, c, f = {2}, deque([2]), 1, True
    yield 2
    while True:
        for m in count(c):
            if m not in aset and all(gcd(m, a) == 1 for a in aqueue):
                yield m
                aset.add(m)
                aqueue.append(m)
                if f:
                    aqueue.popleft()
                f = not f
                while c in aset:
                    c += 1
                break


def A247665_gen():  # generator of terms
    aset, aqueue, c, f = {2}, deque([2]), 3, True
    yield 2
    while True:
        for m in count(c):
            if m not in aset and all(gcd(m, a) == 1 for a in aqueue):
                yield m
                aset.add(m)
                aqueue.append(m)
                if f:
                    aqueue.popleft()
                f = not f
                while c in aset:
                    c += 1
                break


def A249559_gen():  # generator of terms
    aset, aqueue, c, f = {3}, deque([3]), 2, True
    yield 3
    while True:
        for m in count(c):
            if m not in aset and all(gcd(m, a) == 1 for a in aqueue):
                yield m
                aset.add(m)
                aqueue.append(m)
                if f:
                    aqueue.popleft()
                f = not f
                while c in aset:
                    c += 1
                break


def A352808_gen():  # generator of terms
    aset, aqueue, c, m, f = {0}, deque(), 1, 0, False
    yield 0
    for n in count(1):
        if f:
            m = aqueue.popleft()
        f = not f
        for a in count(c):
            if not (a & m or a in aset):
                yield a
                aset.add(a)
                aqueue.append(a)
                while c in aset:
                    c += 1
                break


def A354210(n):
    return int(isqrt(prod(fib2(n + 1))))


def A001654(n):
    return prod(fib2(n + 1))


def A353051(n):
    while n > 1 and len(f := factorint(n, multiple=True)) > 1:
        n -= sum(f)
    return n


def A075255(n):
    return n - sum(factorint(n, multiple=True))


def A351396_gen(startvalue=1):  # generator of terms
    return filter(
        lambda d: not (
            isprime(d)
            or (
                p := n_order(
                    10, d // 2 ** multiplicity(2, d) // 5 ** multiplicity(5, d)
                )
            )
            <= 1
            or (d - 1) % p
        ),
        count(max(startvalue, 1)),
    )


def A350220_gen():  # generator of terms
    pset = set()
    for d in count(1):
        if not (
            isprime(d)
            or (
                p := n_order(
                    10, d // 2 ** multiplicity(2, d) // 5 ** multiplicity(5, d)
                )
            )
            <= 1
            or (d - 1) % p
            or p in pset
        ):
            yield d
            pset.add(p)


def A350598_gen():  # generator of terms
    pset = set()
    for d in count(1):
        if not isprime(d):
            m2, m5 = multiplicity(2, d), multiplicity(5, d)
            r = max(m2, m5)
            k, m = 10**r, 10 ** (t := n_order(10, d // 2**m2 // 5**m5)) - 1
            c = k // d
            s = str(m * k // d - c * m).zfill(t)
            if not (t <= 1 or (d - 1) % t or s in pset):
                yield d
                pset.add(s)


def A353507(n):
    return (
        0 if n == 1 else prod(len(list(g)) for k, g in groupby(factorint(n).values()))
    )


def A353503_gen(startvalue=1):  # generator of terms
    return filter(
        lambda n: n == 1
        or prod((f := factorint(n)).values())
        == prod(primepi(p) ** e for p, e in f.items()),
        count(max(startvalue, 1)),
    )


def A353397(n):
    return prod(prime(2 ** primepi(p)) ** e for p, e in factorint(n).items())


def A090252_gen():  # generator of terms
    aset, aqueue, c, b, f = {1}, deque([1]), 2, 1, True
    yield 1
    while True:
        for m in count(c):
            if m not in aset and gcd(m, b) == 1:
                yield m
                aset.add(m)
                aqueue.append(m)
                if f:
                    aqueue.popleft()
                b = lcm(*aqueue)
                f = not f
                while c in aset:
                    c += 1
                break


def A354255_gen():  # generator of terms
    aset, aqueue, c, plist, f = {1}, deque([1]), 2, [], True
    yield 1
    while True:
        for m in count(c):
            if m not in aset and all(m % p for p in plist):
                if not m % 2:
                    yield m
                aset.add(m)
                aqueue.append(m)
                if f:
                    aqueue.popleft()
                plist = list(set().union(*(primefactors(a) for a in aqueue)))
                f = not f
                while c in aset:
                    c += 1
                break


def A319571_gen():  # generator of terms
    for n in count(0):
        for m in range(n + 1):
            yield from (m, n - m) if n % 2 else (n - m, m)


def A353029(n):
    return 2**n * n * (n * (n * (n * (n * (n - 6) + 11) - 4) - 6) + 4) // 6


def A351632(n):
    return 2**n * n * (n * (n * (n * (n - 7) + 17) - 17) + 6) // 6


def A234848_gen():
    return chain(
        (0,),
        (
            n
            for n in (
                int("".join(i))
                for l in count(1)
                for i in combinations_with_replacement("123456789", l)
            )
            if integer_nthroot(8 * n + 1, 2)[1]
        ),
    )


def A004647(n):
    return int(oct(2**n)[2:])


def A354256_gen():  # generator of terms
    for l in count(2, 2):
        for m in (1, 4, 5, 6, 9):
            for k in range(
                1 + isqrt(m * 10 ** (l - 1) - 1), 1 + isqrt((m + 1) * 10 ** (l - 1) - 1)
            ):
                if k % 10 and integer_nthroot(int(str(k * k)[::-1]), 2)[1]:
                    yield k * k


def A353990_gen():  # generator of terms
    yield 1
    a, s, b = 1, 2, set()
    while True:
        for i in count(s):
            if not (i == a + 1 or i & a or gcd(i, a) > 1 or i in b):
                yield i
                a = i
                b.add(i)
                while s in b:
                    s += 1
                break


def A114112(n):
    return n + (0 if n <= 2 else -1 + 2 * (n % 2))


def A114113(n):
    return 1 if n == 1 else (m := n // 2) * (n + 1) + (n + 1 - m) * (n - 2 * m)


def A033999(n):
    return -1 if n % 2 else 1


def A354008(n):
    return (
        1
        if n == 1
        else (k := (m := n // 2) * (n + 1) + (n + 1 - m) * (n - 2 * m)) // gcd(k, n)
    )


def A141310(n):
    return 2 if n % 2 else n + 1


def A130883(n):
    return n * (2 * n - 1) + 1


def A128918(n):
    return n * (n - 1) // 2 + 1 + (n - 1) * (n % 2)


def A131179(n):
    return n * (n + 1) // 2 + (1 - n) * (n % 2)


def A008836(n):
    return -1 if sum(factorint(n).values()) % 2 else 1


def A354334(n):
    return sum(Fraction(1, factorial(2 * k)) for k in range(n + 1)).numerator


def A354335(n):
    return sum(Fraction(1, factorial(2 * k)) for k in range(n + 1)).denominator


def A354332(n):
    return sum(
        Fraction(-1 if k % 2 else 1, factorial(2 * k + 1)) for k in range(n + 1)
    ).numerator


def A354333(n):
    return sum(
        Fraction(-1 if k % 2 else 1, factorial(2 * k + 1)) for k in range(n + 1)
    ).denominator


def A354211(n):
    return sum(Fraction(1, factorial(2 * k + 1)) for k in range(n + 1)).numerator


def A354331(n):
    return sum(Fraction(1, factorial(2 * k + 1)) for k in range(n + 1)).denominator


def A352962_gen():  # generator of terms
    a = 2
    yield a
    for n in count(2):
        yield (a := min(n, a) if gcd(n, a) == 1 else n + 2)


def A354354(n):
    return int(not n % 6 & 3 ^ 1)


def A120325(n):
    return int(not (n + 3) % 6 & 3 ^ 1)


def A232991(n):
    return int(not (n + 1) % 6 & 3 ^ 1)


def A000035(n):
    return n & 1


def A059841(n):
    return 1 - (n & 1)


def A000034(n):
    return 1 + (n & 1)


def A011655(n):
    return int(bool(n % 3))


def A088911(n):
    return int(n % 6 < 3)


def A010702(n):
    return 3 + (n & 1)


def A010718(n):
    return 5 + 2 * (n & 1)


def A010883(n):
    return 1 + (n & 3)


def A132429(n):
    return 3 - 2 * (n & 3)


def A010887(n):
    return 1 + (n & 7)


def A354404(n):
    return sum(
        Fraction(1 if k & 1 else -1, k * factorial(k)) for k in range(1, n + 1)
    ).denominator


def A354402(n):
    return sum(
        Fraction(1 if k & 1 else -1, k * factorial(k)) for k in range(1, n + 1)
    ).numerator


def A353545(n):
    return sum(Fraction(1, k * factorial(k)) for k in range(1, n + 1)).numerator


def A354401(n):
    return sum(Fraction(1, k * factorial(k)) for k in range(1, n + 1)).denominator


def A353848_gen(startvalue=1):  # generator of terms
    return filter(
        lambda n: n == 1
        or (
            sum((f := factorint(n)).values()) > 1
            and len(set(primepi(p) * e for p, e in f.items())) <= 1
        ),
        count(max(startvalue, 1)),
    )


def A000179(n):
    return (
        1
        if n == 0
        else sum(
            (-2 * n if k & 1 else 2 * n)
            * comb(m := 2 * n - k, k)
            * factorial(n - k)
            // m
            for k in range(n + 1)
        )
    )


def A354432(n):
    f = factorint(n)
    return (
        Fraction(
            prod(p ** (e + 1) - 1 for p, e in f.items()), prod(p - 1 for p in f) * n
        )
        - sum(Fraction(1, p) for p in f)
    ).numerator


def A354433(n):
    f = factorint(n)
    return (
        Fraction(
            prod(p ** (e + 1) - 1 for p, e in f.items()), prod(p - 1 for p in f) * n
        )
        - sum(Fraction(1, p) for p in f)
    ).denominator


def A354437(n):
    return sum(factorial(n) * (-k) ** (n - k) // factorial(k) for k in range(n + 1))


def A354436(n):
    return sum(factorial(n) * k ** (n - k) // factorial(k) for k in range(n + 1))


def A354154_gen():  # generator of terms
    aset, aqueue, c, b, f, p = {1}, deque([1]), 2, 1, True, 2
    yield 0
    while True:
        for m in count(c):
            if m not in aset and gcd(m, b) == 1:
                yield p - m
                p = nextprime(p)
                aset.add(m)
                aqueue.append(m)
                if f:
                    aqueue.popleft()
                b = lcm(*aqueue)
                f = not f
                while c in aset:
                    c += 1
                break


def A297330(n):
    s = str(n)
    return sum(abs(int(s[i]) - int(s[i + 1])) for i in range(len(s) - 1))


def A354212_gen(startvalue=1):  # generator of terms
    for n in count(max(startvalue, 1)):
        s = str(n)
        t = str(n * sum(abs(int(s[i]) - int(s[i + 1])) for i in range(len(s) - 1)))
        if s != t and sorted(s) == sorted(t):
            yield n


def A118478(n):
    return (
        1
        if n == 1
        else int(
            min(
                min(
                    crt((m, (k := primorial(n)) // m), (0, -1))[0],
                    crt((k // m, m), (0, -1))[0],
                )
                for m in (
                    prod(d)
                    for l in range(1, n // 2 + 1)
                    for d in combinations(sieve.primerange(prime(n) + 1), l)
                )
            )
        )
    )


def A215021(n):
    return (
        1
        if n == 1
        else (
            s := int(
                min(
                    min(
                        crt((m, (k := primorial(n)) // m), (0, -1))[0],
                        crt((k // m, m), (0, -1))[0],
                    )
                    for m in (
                        prod(d)
                        for l in range(1, n // 2 + 1)
                        for d in combinations(sieve.primerange(prime(n) + 1), l)
                    )
                )
            )
        )
        * (s + 1)
        // k
    )


def A214089(n):
    return (
        3
        if n == 1
        else int(
            min(
                filter(
                    isprime,
                    (
                        crt(tuple(sieve.primerange(prime(n) + 1)), t)[0]
                        for t in product((1, -1), repeat=n)
                    ),
                )
            )
        )
    )


def A345988(n):
    if n == 1:
        return 2
    plist = tuple(p**q for p, q in factorint(n).items())
    return (
        n * (n - 1)
        if len(plist) == 1
        else (
            s := int(
                min(
                    min(crt((m, n // m), (0, -1))[0], crt((n // m, m), (0, -1))[0])
                    for m in (
                        prod(d)
                        for l in range(1, len(plist) // 2 + 1)
                        for d in combinations(plist, l)
                    )
                )
            )
        )
        * (s + 1)
    )


def A215085(n):
    return (
        1
        if n == 1
        else (
            int(
                min(
                    filter(
                        isprime,
                        (
                            crt(tuple(sieve.primerange(prime(n) + 1)), t)[0]
                            for t in product((1, -1), repeat=n)
                        ),
                    )
                )
            )
            ** 2
            - 1
        )
        // 4
        // primorial(n)
    )


def A354160_gen():  # generator of terms
    aset, aqueue, c, b, f = {1}, deque([1]), 2, 1, True
    while True:
        for m in count(c):
            if m not in aset and gcd(m, b) == 1:
                if len(fm := factorint(m)) == sum(fm.values()) == 2:
                    yield m
                aset.add(m)
                aqueue.append(m)
                if f:
                    aqueue.popleft()
                b = lcm(*aqueue)
                f = not f
                while c in aset:
                    c += 1
                break


def A354161_gen():  # generator of terms
    aset, aqueue, c, b, f, i = {1}, deque([1]), 2, 1, True, 1
    while True:
        for m in count(c):
            if m not in aset and gcd(m, b) == 1:
                i += 1
                if len(fm := factorint(m)) == sum(fm.values()) == 2:
                    yield i
                aset.add(m)
                aqueue.append(m)
                if f:
                    aqueue.popleft()
                b = lcm(*aqueue)
                f = not f
                while c in aset:
                    c += 1
                break


def A354162_gen():  # generator of terms
    aset, aqueue, c, b, f = {1}, deque([1]), 2, 1, True
    while True:
        for m in count(c):
            if m not in aset and gcd(m, b) == 1:
                if m % 2 and len(fm := factorint(m)) == sum(fm.values()) == 2:
                    yield m
                aset.add(m)
                aqueue.append(m)
                if f:
                    aqueue.popleft()
                b = lcm(*aqueue)
                f = not f
                while c in aset:
                    c += 1
                break


def A354163_gen():  # generator of terms
    aset, aqueue, c, b, f, i = {1}, deque([1]), 2, 1, True, 1
    while True:
        for m in count(c):
            if m not in aset and gcd(m, b) == 1:
                i += 1
                if m % 2 and len(fm := factorint(m)) == sum(fm.values()) == 2:
                    yield i
                aset.add(m)
                aqueue.append(m)
                if f:
                    aqueue.popleft()
                b = lcm(*aqueue)
                f = not f
                while c in aset:
                    c += 1
                break


def A354443(n):
    return fibonacci(pow(n, n, A001175(n))) % n


def A060305(n):
    x, p = (1, 1), prime(n)
    for k in count(1):
        if x == (0, 1):
            return k
        x = (x[1], (x[0] + x[1]) % p)


def A345983_gen():  # generator of terms
    c = 1
    for n in count(2):
        yield c
        plist = tuple(p**q for p, q in factorint(n).items())
        c += (
            n - 1
            if len(plist) == 1
            else int(
                min(
                    min(crt((m, n // m), (0, -1))[0], crt((n // m, m), (0, -1))[0])
                    for m in (
                        prod(d)
                        for l in range(1, len(plist) // 2 + 1)
                        for d in combinations(plist, l)
                    )
                )
            )
        )


def A345984_gen():  # generator of terms
    c = 1
    for n in count(4, 2):
        yield c
        plist = tuple(p**q for p, q in factorint(n).items())
        c += (
            n - 1
            if len(plist) == 1
            else int(
                min(
                    min(crt((m, n // m), (0, -1))[0], crt((n // m, m), (0, -1))[0])
                    for m in (
                        prod(d)
                        for l in range(1, len(plist) // 2 + 1)
                        for d in combinations(plist, l)
                    )
                )
            )
        )


def A344875(n):
    return prod(
        (p ** (1 + e) if p == 2 else p**e) - 1 for p, e in factorint(n).items()
    )


def A345992(n):
    if n == 1:
        return 1
    plist = tuple(p**q for p, q in factorint(n).items())
    return (
        1
        if len(plist) == 1
        else gcd(
            n,
            int(
                min(
                    min(crt((m, n // m), (0, -1))[0], crt((n // m, m), (0, -1))[0])
                    for m in (
                        prod(d)
                        for l in range(1, len(plist) // 2 + 1)
                        for d in combinations(plist, l)
                    )
                )
            ),
        )
    )


def A214149(n):
    return (
        7
        if n == 1
        else int(
            min(
                filter(
                    lambda n: n > 3 and isprime(n),
                    (
                        crt(tuple(sieve.primerange(5, prime(n + 2) + 1)), t)[0]
                        for t in product((3, -3), repeat=n)
                    ),
                )
            )
        )
    )


def A214150(n):
    return (
        19
        if n == 1
        else int(
            min(
                filter(
                    lambda n: n > 5 and isprime(n),
                    (
                        crt(tuple(sieve.primerange(7, prime(n + 3) + 1)), t)[0]
                        for t in product((5, -5), repeat=n)
                    ),
                )
            )
        )
    )


def A354463(n):
    c, m = 0, 2**n
    while m >= 5:
        m //= 5
        c += m
    return c


def A070824(n):
    return 0 if n == 1 else divisor_count(n) - 2


def A078709(n):
    return n // divisor_count(n)


def A353960_gen():  # generator of terms
    adict, a = {}, 1
    yield a
    while True:
        if a in adict:
            adict[a] += 1
            a *= adict[a]
        else:
            adict[a] = 1
            a //= divisor_count(a)
        yield a


def A130290(n):
    return prime(n) // 2


def A005097(n):
    return prime(n + 1) // 2


def A354169_gen():  # generator of terms
    aset, aqueue, b, f = {0, 1, 2}, deque([2]), 2, False
    yield from (0, 1, 2)
    while True:
        for k in count(1):
            m, j, j2, r, s = 0, 0, 1, b, k
            while r > 0:
                r, q = divmod(r, 2)
                if not q:
                    s, y = divmod(s, 2)
                    m += y * j2
                j += 1
                j2 *= 2
            if s > 0:
                m += s * 2 ** b.bit_length()
            if m not in aset:
                yield m
                aset.add(m)
                aqueue.append(m)
                if f:
                    aqueue.popleft()
                b = reduce(or_, aqueue)
                f = not f
                break


def A354757_gen():  # generator of terms
    aset, aqueue, b, f = {0, 1, 2}, deque([2]), 2, False
    yield from (0, 0, 1)
    while True:
        for k in count(1):
            m, j, j2, r, s = 0, 0, 1, b, k
            while r > 0:
                r, q = divmod(r, 2)
                if not q:
                    s, y = divmod(s, 2)
                    m += y * j2
                j += 1
                j2 *= 2
            if s > 0:
                m += s * 2 ** b.bit_length()
            if m not in aset:
                yield sum(aqueue)
                aset.add(m)
                aqueue.append(m)
                if f:
                    aqueue.popleft()
                b = reduce(or_, aqueue)
                f = not f
                break


def A354680_gen():  # generator of terms
    aset, aqueue, b, f = {0, 1, 2}, deque([2]), 2, False
    yield 0
    while True:
        for k in count(1):
            m, j, j2, r, s = 0, 0, 1, b, k
            while r > 0:
                r, q = divmod(r, 2)
                if not q:
                    s, y = divmod(s, 2)
                    m += y * j2
                j += 1
                j2 *= 2
            if s > 0:
                m += s * 2 ** b.bit_length()
            if m not in aset:
                if bin(m).count("1") > 1:
                    yield m
                aset.add(m)
                aqueue.append(m)
                if f:
                    aqueue.popleft()
                b = reduce(or_, aqueue)
                f = not f
                break


def A354798_gen():  # generator of terms
    aset, aqueue, b, f, i = {0, 1, 2}, deque([2]), 2, False, 2
    yield 0
    while True:
        for k in count(1):
            m, j, j2, r, s = 0, 0, 1, b, k
            while r > 0:
                r, q = divmod(r, 2)
                if not q:
                    s, y = divmod(s, 2)
                    m += y * j2
                j += 1
                j2 *= 2
            if s > 0:
                m += s * 2 ** b.bit_length()
            if m not in aset:
                i += 1
                if bin(m).count("1") > 1:
                    yield i
                aset.add(m)
                aqueue.append(m)
                if f:
                    aqueue.popleft()
                b = reduce(or_, aqueue)
                f = not f
                break


def A054055(n):
    return max(int(d) for d in str(n))


def A095815(n):
    return n + max(int(d) for d in str(n))


def A016116(n):
    return 1 << n // 2


def A007590(n):
    return n**2 // 2


def A000212(n):
    return n**2 // 3


def A008615(n):
    return n // 2 - n // 3


def A074148(n):
    return n + n**2 // 2


def A098844_gen():  # generator of terms
    aqueue, f, b = deque([]), False, 1
    yield 1
    for i in count(2):
        yield (a := i * b)
        aqueue.append(a)
        if f:
            b = aqueue.popleft()
        f = not f


def A098844(n):
    return n * prod(n // 2**k for k in range(1, n.bit_length() - 1))


def A033485_gen():  # generator of terms
    aqueue, f, b, a = deque([2]), True, 1, 2
    yield from (1, 2)
    while True:
        a += b
        yield a
        aqueue.append(a)
        if f:
            b = aqueue.popleft()
        f = not f


def A040039_gen():  # generator of terms
    aqueue, f, b, a = deque([2]), True, 1, 2
    yield from (1, 1, 2, 2)
    while True:
        a += b
        yield from (a, a)
        aqueue.append(a)
        if f:
            b = aqueue.popleft()
        f = not f


def A178855_gen():  # generator of terms
    aqueue, f, b, a = deque([2]), True, 1, 2
    while True:
        a += b
        aqueue.append(a)
        if f:
            yield (a - 1) // 2
            b = aqueue.popleft()
        f = not f


def A094451_gen():  # generator of terms
    aqueue, f, b, a = deque([2]), True, 1, 2
    yield from (1, 2)
    while True:
        a = (a + b) % 3
        yield a
        aqueue.append(a)
        if f:
            b = aqueue.popleft()
        f = not f


def A008794(n):
    return (n // 2) ** 2


@lru_cache(maxsize=None)
def A320225(n):
    return 1 if n == 1 else sum(A320225(d) * (n // d - 1) for d in range(1, n))


def A320225_gen():  # generator of terms
    alist, a = [1], 1
    yield a
    for n in count(2):
        a = sum(alist[d - 1] * (n // d - 1) for d in range(1, n))
        yield a
        alist.append(a)


def A347027_gen():  # generator of terms
    aqueue, f, b, a = deque([3]), True, 1, 3
    yield from (1, 3)
    while True:
        a += 2 * b
        yield a
        aqueue.append(a)
        if f:
            b = aqueue.popleft()
        f = not f


def A346912_gen():  # generator of terms
    aqueue, f, b, a = deque([2]), True, 1, 2
    yield from (1, 3, 7)
    while True:
        a += b
        yield 4 * a - 1
        aqueue.append(a)
        if f:
            b = aqueue.popleft()
        f = not f


def A102378_gen():  # generator of terms
    aqueue, f, b, a = deque([2]), True, 1, 2
    yield from (1, 3)
    while True:
        a += b
        yield 2 * a - 1
        aqueue.append(a)
        if f:
            b = aqueue.popleft()
        f = not f


def A062187_gen():  # generator of terms
    aqueue, f, b, a = deque([1]), True, 0, 1
    yield from (0, 1)
    while True:
        a -= b
        yield a
        aqueue.append(a)
        if f:
            b = aqueue.popleft()
        f = not f


def A062186_gen():  # generator of terms
    aqueue, f, b, a = deque([0]), True, 1, 0
    yield from (1, 0)
    while True:
        a -= b
        yield a
        aqueue.append(a)
        if f:
            b = aqueue.popleft()
        f = not f


def A062188_gen():  # generator of terms
    aqueue, f, b, a = deque([1]), True, 0, 1
    yield from (0, 1)
    while True:
        a += b
        yield a
        aqueue.append(a)
        if f:
            b = aqueue.popleft()
        f = not f


def A022907_gen():  # generator of terms
    aqueue, f, b, a = deque([2]), True, 1, 2
    yield from (0, 2, 5)
    while True:
        a += b
        yield 3 * a - 1
        aqueue.append(a)
        if f:
            b = aqueue.popleft()
        f = not f


def A022905_gen():  # generator of terms
    aqueue, f, b, a = deque([2]), True, 1, 2
    yield 1
    while True:
        a += b
        aqueue.append(a)
        if f:
            yield (3 * a - 1) // 2
            b = aqueue.popleft()
        f = not f


def A022908_gen():  # generator of terms
    aqueue, f, b, a = deque([2]), True, 1, 2
    yield from (0, 2)
    while True:
        a += b
        aqueue.append(a)
        if f:
            yield (3 * a + 1) // 2
            b = aqueue.popleft()
        f = not f


def A352717_gen():  # generator of terms
    a, b = 1, 3
    while True:
        yield from (a,) * (b - a)
        a, b = b, a + b


def A130241_gen():  # generator of terms
    a, b = 1, 3
    for i in count(1):
        yield from (i,) * (b - a)
        a, b = b, a + b


def A130247_gen():  # generator of terms
    yield from (1, 0)
    a, b = 3, 4
    for i in count(2):
        yield from (i,) * (b - a)
        a, b = b, a + b


def A130242_gen():  # generator of terms
    yield from (0, 0, 0, 2)
    a, b = 3, 4
    for i in count(3):
        yield from (i,) * (b - a)
        a, b = b, a + b


def A130245_gen():  # generator of terms
    yield from (0, 1, 2)
    a, b = 3, 4
    for i in count(3):
        yield from (i,) * (b - a)
        a, b = b, a + b


def A130249_gen():  # generator of terms
    a, b = 0, 1
    for i in count(0):
        yield from (i,) * (b - a)
        a, b = b, 2 * a + b


def A130249(n):
    return (3 * n + 1).bit_length() - 1


def A276710_gen():  # generator of terms
    p, q = 3, 5
    while True:
        for m in range(p + 1, q):
            r = m ** (m - 1)
            c = 1
            for k in range(m + 1):
                c = c * comb(m, k) % r
            if c == 0:
                yield m
        p, q = q, nextprime(q)


def A353010_gen():  # generator of terms
    p, q = 3, 5
    while True:
        for m in range(p + 1, q):
            r = m ** (m - 1)
            c = 1
            for k in range(m + 1):
                c = c * comb(m, k) % r
            if c == 0:
                d, (e, f) = -m, divmod(prod(comb(m, k) for k in range(m + 1)), m)
                while f == 0:
                    d += 1
                    e, f = divmod(e, m)
                yield d
        p, q = q, nextprime(q)


def A351628_gen():  # generator of terms
    a, b, c = 1, 3, 0
    while True:
        yield from (c + i * a for i in range(1, b - a + 1))
        a, b, c = b, a + b, c + a * (b - a)


def A001250_gen():  # generator of terms
    yield from (1, 1)
    blist = (0, 2)
    while True:
        yield (blist := tuple(accumulate(reversed(blist), initial=0)))[-1]


def A348615_gen():  # generator of terms
    yield from (0, 0)
    blist, f = (0, 2), 1
    for n in count(2):
        f *= n
        yield f - (blist := tuple(accumulate(reversed(blist), initial=0)))[-1]


def A354862(n):
    f = factorial(n)
    return sum(
        f * (a := factorial(n // d)) // (b := factorial(d))
        + (f * b // a if d**2 < n else 0)
        for d in divisors(n, generator=True)
        if d**2 <= n
    )


def A354863(n):
    f = factorial(n)
    return sum(f * n // d // factorial(d) for d in divisors(n, generator=True))


def A067742(n):
    return sum(1 for d in divisors(n, generator=True) if n <= 2 * d**2 < 4 * n)


def A319529_gen(startvalue=1):  # generator of terms
    for k in count(max(1, startvalue + 1 - (startvalue & 1)), 2):
        if any((k <= 2 * d**2 < 4 * k for d in divisors(k, generator=True))):
            yield k


def A132049_gen():  # generator of terms
    yield 2
    blist = (0, 1)
    for n in count(2):
        yield Fraction(
            2 * n * blist[-1],
            (blist := tuple(accumulate(reversed(blist), initial=0)))[-1],
        ).numerator


def A132050_gen():  # generator of terms
    yield 1
    blist = (0, 1)
    for n in count(2):
        yield Fraction(
            2 * n * blist[-1],
            (blist := tuple(accumulate(reversed(blist), initial=0)))[-1],
        ).denominator


def A000708_gen():  # generator of terms
    yield -1
    blist = (0, 1)
    for n in count(2):
        yield -2 * blist[-1] + (blist := tuple(accumulate(reversed(blist), initial=0)))[
            -1
        ]


def A024255_gen():  # generator of terms
    yield from (0, 1)
    blist = (0, 1)
    for n in count(2):
        yield n * (
            blist := tuple(
                accumulate(
                    reversed(tuple(accumulate(reversed(blist), initial=0))), initial=0
                )
            )
        )[-1]


def A141479_gen():  # generator of terms
    yield from (2, 3)
    blist = (0, 1)
    for n in count(0):
        yield (blist := tuple(accumulate(reversed(blist), initial=0)))[-1] + (
            2,
            1,
            1,
            2,
        )[n & 3]


def A000756_gen():  # generator of terms
    yield from (1, 2)
    blist = (1, 2)
    while True:
        yield (blist := tuple(accumulate(reversed(blist), initial=0)))[-1]


def A180942_gen():  # generator of terms
    blist = (0, 1)
    for n in count(2):
        blist = tuple(accumulate(reversed(blist), initial=0))
        if (
            n & 1
            and (blist[-1] + (1 if (n - 1) // 2 & 1 else -1)) % n == 0
            and not isprime(n)
        ):
            yield n


def A166298_gen():  # generator of terms
    yield 0
    blist, c = (0, 1), 1
    for n in count(1):
        yield (blist := tuple(accumulate(reversed(blist), initial=0)))[-1] - c
        c = c * (4 * n + 2) // (n + 2)


def A338399_gen():  # generator of terms
    blist, a, b = tuple(), 0, 1
    while True:
        yield (
            blist := tuple(accumulate(reversed(blist), func=operator_sub, initial=a))
        )[-1]
        a, b = b, a + b


def A338398_gen():  # generator of terms
    blist = tuple()
    for i in count(1):
        yield (
            blist := tuple(
                accumulate(reversed(blist), func=operator_sub, initial=prime(i))
            )
        )[-1]


def A338400_gen():  # generator of terms
    blist = tuple()
    for i in count(0):
        yield (
            blist := tuple(
                accumulate(reversed(blist), func=operator_sub, initial=npartitions(i))
            )
        )[-1]


def A102590_gen():  # generator of terms
    blist, m = tuple(), 1
    while True:
        yield (
            blist := tuple(accumulate(reversed(blist), func=operator_sub, initial=m))
        )[-1]
        m *= 2


def A062162_gen():  # generator of terms
    blist, m = tuple(), -1
    while True:
        yield (blist := tuple(accumulate(reversed(blist), initial=(m := -m))))[-1]


def A097953_gen():  # generator of terms
    blist, m = tuple(), 1
    while True:
        yield (blist := tuple(accumulate(reversed(blist), initial=(m + 1) // 2)))[-1]
        m *= -2


def A000667_gen():  # generator of terms
    blist = tuple()
    while True:
        yield (blist := tuple(accumulate(reversed(blist), initial=1)))[-1]


def A061531_gen():  # generator of terms
    blist, m = tuple(), 1
    for i in count(1):
        yield (blist := tuple(accumulate(reversed(blist), initial=m)))[-1]
        m = mobius(i)


def A306822_gen():  # generator of terms
    blist, m = tuple(), 1
    for i in count(1):
        yield (blist := tuple(accumulate(reversed(blist), initial=m)))[-1]
        m = m * (4 * i - 2) // i


def A307595_gen():  # generator of terms
    blist = tuple()
    for i in count(0):
        yield (
            blist := tuple(
                accumulate(
                    reversed(blist), initial=hyperexpand(hyper((1 - i, -i), [], 1))
                )
            )
        )[-1]


def A308521_gen():  # generator of terms
    blist, m = tuple(), 1
    for i in count(1):
        yield (blist := tuple(accumulate(reversed(blist), initial=m)))[-1]
        m *= 2 * i


def A337445_gen():  # generator of terms
    blist, m = tuple(), 1
    for i in count(1):
        yield (
            blist := tuple(accumulate(reversed(blist), func=operator_sub, initial=m))
        )[-1]
        m *= i


def A308681_gen():  # generator of terms
    blist, m = tuple(), 1
    for i in count(1):
        yield (
            blist := tuple(accumulate(reversed(blist), func=operator_sub, initial=m))
        )[-1]
        m *= 2 * i - 1


def A337443_gen():  # generator of terms
    blist = tuple()
    for i in count(1):
        yield (
            blist := tuple(accumulate(reversed(blist), func=operator_sub, initial=i))
        )[-1]


def A337444_gen():  # generator of terms
    blist = tuple()
    for i in count(1, 2):
        yield (
            blist := tuple(accumulate(reversed(blist), func=operator_sub, initial=i))
        )[-1]


def A337446_gen():  # generator of terms
    blist, c = tuple(), 1
    for i in count(0):
        yield (
            blist := tuple(accumulate(reversed(blist), func=operator_sub, initial=c))
        )[-1]
        c = c * (4 * i + 2) // (i + 2)


def A347071_gen():  # generator of terms
    blist, m = tuple(), 1
    for i in count(1):
        yield (
            blist := tuple(accumulate(reversed(blist), func=operator_sub, initial=m))
        )[-1]
        m = m * i + 1


def A337447_gen():  # generator of terms
    yield from (1, 0)
    blist, alist = (1, 0), (1,)
    while True:
        yield (
            blist := tuple(
                accumulate(
                    reversed(blist),
                    func=operator_sub,
                    initial=(alist := list(accumulate(alist, initial=alist[-1])))[-1],
                )
            )
        )[-1]


def A230960_gen():  # generator of terms
    blist, m = tuple(), 1
    for i in count(1):
        yield (blist := tuple(accumulate(reversed(blist), initial=m)))[-1]
        m *= i


def A000738_gen():  # generator of terms
    blist, a, b = tuple(), 0, 1
    while True:
        yield (blist := tuple(accumulate(reversed(blist), initial=a)))[-1]
        a, b = b, a + b


def A000747_gen():  # generator of terms
    blist = tuple()
    for i in count(1):
        yield (blist := tuple(accumulate(reversed(blist), initial=prime(i))))[-1]


def A000753_gen():  # generator of terms
    blist, c = tuple(), 1
    for i in count(0):
        yield (blist := tuple(accumulate(reversed(blist), initial=c)))[-1]
        c = c * (4 * i + 2) // (i + 2)


def A231179_gen():  # generator of terms
    blist = tuple()
    for i in count(0):
        yield (blist := tuple(accumulate(reversed(blist), initial=i)))[-1]


def A000718_gen():  # generator of terms
    yield 1
    blist, c = (1,), 1
    for i in count(2):
        yield (blist := tuple(accumulate(reversed(blist), initial=c)))[-1]
        c += i


def A000674_gen():  # generator of terms
    yield 1
    blist = (1,)
    while True:
        yield (blist := tuple(accumulate(reversed(blist), initial=2)))[-1]


def A101473_gen():  # generator of terms
    blist, a, b = tuple(), 0, 1
    while True:
        yield (blist := tuple(accumulate(reversed(blist), initial=a)))[-1]
        a, b = b, 2 * a + b


def A101474_gen():  # generator of terms
    blist, a, b = tuple(), 0, -1
    while True:
        yield (blist := tuple(accumulate(reversed(blist), initial=a)))[-1]
        a, b = -b, -2 * a - b


def A307594_gen():  # generator of terms
    blist, a, b = tuple(), 1, -1
    for n in count(1):
        yield (blist := tuple(accumulate(reversed(blist), initial=a)))[-1]
        a, b = a * n + b, -b


def A306799_gen():  # generator of terms
    blist, a = tuple(), 1
    for i in count(1):
        yield (blist := tuple(accumulate(reversed(blist), initial=a)))[-1]
        a = 2 * a * i // (i + 1) if i & 1 else 2 * a


def A307592_gen():  # generator of terms
    blist = (1, 2)
    yield from blist
    for i in count(2):
        yield (blist := tuple(accumulate(reversed(blist), initial=i ** (i - 2))))[-1]


def A308520_gen():  # generator of terms
    blist = tuple()
    for i in count(0):
        yield (
            blist := tuple(accumulate(reversed(blist), initial=i * (i + 1) // 2 + 1))
        )[-1]


def A307593_gen():  # generator of terms
    blist, m = tuple(), 1
    for i in count(1):
        yield (blist := tuple(accumulate(reversed(blist), initial=m)))[-1]
        m = m * i + 1


def A306880_gen():  # generator of terms
    blist = tuple()
    for i in count(0):
        yield (blist := tuple(accumulate(reversed(blist), initial=i**i)))[-1]


def A306881_gen():  # generator of terms
    yield 0
    blist = (0,)
    for i in count(1):
        yield (blist := tuple(accumulate(reversed(blist), initial=i ** (i - 1))))[-1]


def A296792_gen():  # generator of terms
    blist, m = tuple(), 1
    for i in count(1, 2):
        yield (blist := tuple(accumulate(reversed(blist), initial=m)))[-1]
        m *= i


def A347072_gen():  # generator of terms
    blist, m = (0,), 1
    yield from blist
    for i in count(1):
        yield (blist := tuple(accumulate(reversed(blist), initial=m)))[-1]
        m *= i


def A307879_gen():  # generator of terms
    blist, m = tuple(), 1
    yield from blist
    while True:
        yield (blist := tuple(accumulate(reversed(blist), initial=m)))[-1]
        m *= 4


def A307878_gen():  # generator of terms
    blist, m = tuple(), 1
    yield from blist
    while True:
        yield (blist := tuple(accumulate(reversed(blist), initial=m)))[-1]
        m *= 3


def A306836_gen():  # generator of terms
    blist, a, b = (1,), 1, 1
    yield from blist
    for i in count(2):
        yield (blist := tuple(accumulate(reversed(blist), initial=b)))[-1]
        a, b = b, (b * (2 * i + 1) + (3 * i - 3) * a) // (i + 2)


def A306832_gen():  # generator of terms
    blist, a, b = (1,), 1, 1
    yield from blist
    for i in count(2):
        yield (blist := tuple(accumulate(reversed(blist), initial=b)))[-1]
        a, b = b, (b * (2 * i - 1) + (3 * i - 3) * a) // i


def A231894_gen():  # generator of terms
    blist, c = tuple(), 1
    for i in count(1):
        yield (blist := tuple(accumulate(reversed(blist), initial=c)))[-1]
        c = c * (4 * i + 2) // (i + 2)


def A000736_gen():  # generator of terms
    yield 1
    blist, c = (1,), 1
    for i in count(0):
        yield (blist := tuple(accumulate(reversed(blist), initial=c)))[-1]
        c = c * (4 * i + 2) // (i + 2)


def A230961_gen():  # generator of terms
    blist, m = tuple(), 1
    for i in count(1):
        yield (blist := tuple(accumulate(reversed(blist), initial=(m := m * i))))[-1]


def A231200_gen():  # generator of terms
    blist = tuple()
    for i in count(0, 2):
        yield (blist := tuple(accumulate(reversed(blist), initial=i)))[-1]


def A092090_gen():  # generator of terms
    blist, a, b = tuple(), 1, 2
    while True:
        yield (blist := tuple(accumulate(reversed(blist), initial=a)))[-1]
        a, b = b, a + b


def A062161_gen():  # generator of terms
    blist, m = tuple(), 1
    while True:
        yield (blist := tuple(accumulate(reversed(blist), initial=(m := 1 - m))))[-1]


def A062272_gen():  # generator of terms
    blist, m = tuple(), 0
    while True:
        yield (blist := tuple(accumulate(reversed(blist), initial=(m := 1 - m))))[-1]


def A000744_gen():  # generator of terms
    blist, a, b = tuple(), 1, 1
    while True:
        yield (blist := tuple(accumulate(reversed(blist), initial=a)))[-1]
        a, b = b, a + b


def A000660_gen():  # generator of terms
    yield 1
    blist = (1,)
    for i in count(1):
        yield (blist := tuple(accumulate(reversed(blist), initial=i)))[-1]


def A000733_gen():  # generator of terms
    yield 1
    blist = (1,)
    for i in count(0):
        yield (blist := tuple(accumulate(reversed(blist), initial=npartitions(i))))[-1]


def A000737_gen():  # generator of terms
    blist = tuple()
    for i in count(1):
        yield (blist := tuple(accumulate(reversed(blist), initial=i)))[-1]


def A000734_gen():  # generator of terms
    yield 1
    blist, m = (1,), 1
    while True:
        yield (blist := tuple(accumulate(reversed(blist), initial=m)))[-1]
        m *= 2


def A000751_gen():  # generator of terms
    blist = tuple()
    for i in count(0):
        yield (blist := tuple(accumulate(reversed(blist), initial=npartitions(i))))[-1]


def A000754_gen():  # generator of terms
    blist = tuple()
    for i in count(1, 2):
        yield (blist := tuple(accumulate(reversed(blist), initial=i)))[-1]


def A000732_gen():  # generator of terms
    yield 1
    blist = (1,)
    for i in count(1):
        yield (blist := tuple(accumulate(reversed(blist), initial=prime(i))))[-1]


def A000697_gen():  # generator of terms
    yield 1
    blist, m = (1,), 1
    for i in count(1):
        yield (blist := tuple(accumulate(reversed(blist), initial=m)))[-1]
        m += 2 * i + 1


def A000752_gen():  # generator of terms
    blist, m = tuple(), 1
    while True:
        yield (blist := tuple(accumulate(reversed(blist), initial=m)))[-1]
        m *= 2


def A230953_gen():  # generator of terms
    blist = tuple()
    for i in count(2):
        yield (blist := tuple(accumulate(reversed(blist), initial=prime(i))))[-1]


def A230954_gen():  # generator of terms
    blist = tuple()
    for i in count(1):
        yield (blist := tuple(accumulate(reversed(blist), initial=composite(i))))[-1]


def A230955_gen():  # generator of terms
    yield 1
    blist = (1,)
    for i in count(1):
        yield (blist := tuple(accumulate(reversed(blist), initial=composite(i))))[-1]


def A000746_gen():  # generator of terms
    blist, c = tuple(), 1
    for i in count(2):
        yield (blist := tuple(accumulate(reversed(blist), initial=c)))[-1]
        c += i


def A000745_gen():  # generator of terms
    blist, c = tuple(), 1
    for i in count(1):
        yield (blist := tuple(accumulate(reversed(blist), initial=c)))[-1]
        c += 2 * i + 1


if sys.version_info >= (3, 10):

    def A230952_gen():  # generator of terms
        blist = tuple()
        for i in count(0):
            yield (blist := tuple(accumulate(reversed(blist), initial=i.bit_count())))[
                -1
            ]

else:

    def A230952_gen():  # generator of terms
        blist = tuple()
        for i in count(0):
            yield (
                blist := tuple(accumulate(reversed(blist), initial=bin(i).count("1")))
            )[-1]


def A000764_gen():  # generator of terms
    blist, alist = (1, 2), (1,)
    yield from blist
    while True:
        yield (
            blist := tuple(
                accumulate(
                    reversed(blist),
                    initial=(alist := list(accumulate(alist, initial=alist[-1])))[-1],
                )
            )
        )[-1]


def A182665(n):
    if n == 1:
        return 0
    plist = tuple(p**q for p, q in factorint(n).items())
    return (
        1
        if len(plist) == 1
        else n
        - int(
            min(
                min(crt((m, n // m), (0, -1))[0], crt((n // m, m), (0, -1))[0])
                for m in (
                    prod(d)
                    for l in range(1, len(plist) // 2 + 1)
                    for d in combinations(plist, l)
                )
            )
        )
    )


def A354921_gen(startvalue=2):  # generator of terms
    for n in count(max(startvalue, 2)):
        plist = tuple(p**q for p, q in factorint(n).items())
        if (
            len(plist) == 1
            or (
                n
                - int(
                    min(
                        min(crt((m, n // m), (0, -1))[0], crt((n // m, m), (0, -1))[0])
                        for m in (
                            prod(d)
                            for l in range(1, len(plist) // 2 + 1)
                            for d in combinations(plist, l)
                        )
                    )
                )
            )
            & 1
        ):
            yield n


def A354922_gen(startvalue=1):  # generator of terms
    if startvalue <= 1:
        yield 1
    for n in count(max(startvalue, 2)):
        plist = tuple(p**q for p, q in factorint(n).items())
        if (
            len(plist) != 1
            and not (
                n
                - int(
                    min(
                        min(crt((m, n // m), (0, -1))[0], crt((n // m, m), (0, -1))[0])
                        for m in (
                            prod(d)
                            for l in range(1, len(plist) // 2 + 1)
                            for d in combinations(plist, l)
                        )
                    )
                )
            )
            & 1
        ):
            yield n


def A354920(n):
    if n == 1:
        return 0
    plist = tuple(p**q for p, q in factorint(n).items())
    return (
        1
        if len(plist) == 1
        else (
            n
            - int(
                min(
                    min(crt((m, n // m), (0, -1))[0], crt((n // m, m), (0, -1))[0])
                    for m in (
                        prod(d)
                        for l in range(1, len(plist) // 2 + 1)
                        for d in combinations(plist, l)
                    )
                )
            )
        )
        & 1
    )


def A354919_gen(startvalue=1):  # generator of terms
    if startvalue <= 1:
        yield 1
    for n in count(max(startvalue, 2)):
        plist = tuple(p**q for p, q in factorint(n).items())
        if len(plist) == 1:
            if (n - 1) & 1:
                yield n
        elif (
            int(
                min(
                    min(crt((m, n // m), (0, -1))[0], crt((n // m, m), (0, -1))[0])
                    for m in (
                        prod(d)
                        for l in range(1, len(plist) // 2 + 1)
                        for d in combinations(plist, l)
                    )
                )
            )
            & 1
        ):
            yield n


def A068311(n):
    return (
        sum(
            (
                factorial(n) * e // p
                for p, e in sum(
                    (Counter(factorint(m)) for m in range(2, n + 1)),
                    start=Counter({2: 0}),
                ).items()
            )
        )
        if n > 1
        else 0
    )


def A068327(n):
    return sum((n ** (n + 1) * e // p for p, e in factorint(n).items())) if n > 1 else 0


def A168386(n):
    return (
        sum(
            (
                factorial2(n) * e // p
                for p, e in sum(
                    (Counter(factorint(m)) for m in range(n, 1, -2)),
                    start=Counter({2: 0}),
                ).items()
            )
        )
        if n > 1
        else 0
    )


def A260620(n):
    s = prod(factorial(i) for i in range(2, n + 1))
    return (
        sum(
            s * e // p
            for p, e in sum(
                (
                    (lambda x: Counter({k: x[k] * (n - m + 1) for k in x}))(
                        factorint(m)
                    )
                    for m in range(2, n + 1)
                ),
                start=Counter({2: 0}),
            ).items()
        )
        if n > 1
        else 0
    )


def A260619(n):
    s = prod(i**i for i in range(2, n + 1))
    return (
        sum(
            s * e // p
            for p, e in sum(
                (
                    (lambda x: Counter({k: x[k] * m for k in x}))(factorint(m))
                    for m in range(2, n + 1)
                ),
                start=Counter({2: 0}),
            ).items()
        )
        if n > 1
        else 0
    )


def A068329(n):
    f = fibonacci(n)
    return sum((f * e // p for p, e in factorint(f).items())) if n > 2 else 0


def A354918(n):
    if n == 1:
        return 1
    plist = tuple(p**q for p, q in factorint(n).items())
    return (
        n - 1
        if len(plist) == 1
        else int(
            min(
                min(crt((m, n // m), (0, -1))[0], crt((n // m, m), (0, -1))[0])
                for m in (
                    prod(d)
                    for l in range(1, len(plist) // 2 + 1)
                    for d in combinations(plist, l)
                )
            )
        )
    ) & 1


def A354927(n):
    return int(n == 1 or divisor_count(n) == 4)


def A354966(n):
    a, s = gcd(n, 24), sum(sieve[j] ** 2 for j in range(1, n + 1))
    for i in count(1):
        (b, c), p = divmod(s, a), sieve[i]
        if c == 0 and isprime(b):
            return p
        s += sieve[i + n] ** 2 - p**2


def A354950(n):
    plist = list(primerange(2, p := prime(n)))
    return sum(
        1
        for l in range(1, n)
        for d in combinations(plist, l)
        if isprime(q := prod(d) * p - 1) and isprime(q + 2)
    )


def A049240(n):
    return int(isqrt(n) ** 2 != n)


def A067280(n):
    return len(
        (a := continued_fraction_periodic(0, 1, n))[:1] + (a[1] if a[1:] else [])
    )


def A003285(n):
    a = continued_fraction_periodic(0, 1, n)
    return len(a[1]) if a[1:] else 0


def A068717(n):
    return (
        0
        if (a := isqrt(n) ** 2 == n)
        else (-1 if len(continued_fraction_periodic(0, 1, n)[1]) & 1 else 1 - int(a))
    )


def A068718_gen():  # generator of terms
    yield 1
    blist = (1,)
    for n in count(2):
        yield (
            blist := tuple(
                accumulate(
                    reversed(blist),
                    initial=0
                    if (a := isqrt(n) ** 2 == n)
                    else (
                        1
                        if len(continued_fraction_periodic(0, 1, n)[1]) & 1
                        else int(a) - 1
                    ),
                )
            )
        )[-1]


def A104854_gen():  # generator of terms
    yield 1
    blist = (0, 1)
    while True:
        yield -blist[-1] + 2 * (blist := tuple(accumulate(reversed(blist), initial=0)))[
            -1
        ]


def A231895_gen():  # generator of terms
    yield 3
    blist = (0, 1)
    while True:
        yield blist[-1] + 2 * (blist := tuple(accumulate(reversed(blist), initial=0)))[
            -1
        ]


def A344000_gen():  # generator of terms
    for n in count(1):
        plist = tuple(p**q for p, q in factorint(2 * n).items())
        if (
            len(plist) > 1
            and min(
                min(crt((m, 2 * n // m), (0, -1))[0], crt((2 * n // m, m), (0, -1))[0])
                for m in (
                    prod(d)
                    for l in range(1, len(plist) // 2 + 1)
                    for d in combinations(plist, l)
                )
            )
            & 1
            == 0
        ):
            yield n


def A344001_gen():  # generator of terms
    for n in count(1):
        plist = tuple(p**q for p, q in factorint(2 * n).items())
        if (
            len(plist) == 1
            or min(
                min(crt((m, 2 * n // m), (0, -1))[0], crt((2 * n // m, m), (0, -1))[0])
                for m in (
                    prod(d)
                    for l in range(1, len(plist) // 2 + 1)
                    for d in combinations(plist, l)
                )
            )
            & 1
        ):
            yield n


def A344763(n):
    plist = tuple(p**q for p, q in factorint(2 * n).items())
    return (
        1 - n
        if len(plist) == 1
        else n
        - int(
            min(
                min(crt((m, 2 * n // m), (0, -1))[0], crt((2 * n // m, m), (0, -1))[0])
                for m in (
                    prod(d)
                    for l in range(1, len(plist) // 2 + 1)
                    for d in combinations(plist, l)
                )
            )
        )
    )


def A344878(n):
    return lcm(*(p ** (e + int(p == 2)) - 1 for p, e in factorint(n).items()))


def A344879(n):
    return prod(
        a := tuple(p ** (e + int(p == 2)) - 1 for p, e in factorint(n).items())
    ) // lcm(*a)


def A226295(n):
    return n_order(prime(n), prime(n + 1))


def A355039_gen():  # generator of terms
    p, q = 3, 5
    while True:
        yield from (
            n
            for n in range(p + 2, q, 2)
            if max((f := factorint(n)).values()) == 1
            and not any((n - 1) % (p - 1) for p in f)
            and isprime(len(f))
        )
        p, q = q, nextprime(q)


def A355023(n):
    return 7 * comb(n, n - 8) * factorial(n - 2)


def A345993(n):
    if n == 1:
        return 1
    plist = tuple(p**q for p, q in factorint(n).items())
    return (
        n
        if len(plist) == 1
        else gcd(
            n,
            1
            + int(
                min(
                    min(crt((m, n // m), (0, -1))[0], crt((n // m, m), (0, -1))[0])
                    for m in (
                        prod(d)
                        for l in range(1, len(plist) // 2 + 1)
                        for d in combinations(plist, l)
                    )
                )
            ),
        )
    )


def A354988(n):
    if n == 1:
        return 0
    plist = tuple(p**q for p, q in factorint(n).items())
    return (
        n - 1
        if len(plist) == 1
        else -gcd(
            n,
            s := int(
                min(
                    min(crt((m, n // m), (0, -1))[0], crt((n // m, m), (0, -1))[0])
                    for m in (
                        prod(d)
                        for l in range(1, len(plist) // 2 + 1)
                        for d in combinations(plist, l)
                    )
                )
            ),
        )
        + gcd(n, s + 1)
    )


def A345995_gen():
    for n in count(2):
        plist = tuple(p**q for p, q in factorint(n).items())
        if len(plist) > 1 and gcd(
            n,
            s := int(
                min(
                    min(crt((m, n // m), (0, -1))[0], crt((n // m, m), (0, -1))[0])
                    for m in (
                        prod(d)
                        for l in range(1, len(plist) // 2 + 1)
                        for d in combinations(plist, l)
                    )
                )
            ),
        ) < gcd(n, s + 1):
            yield n


def A354989(n):
    if n == 1:
        return 0
    plist = tuple(p**q for p, q in factorint(n).items())
    return (
        0
        if len(plist) == 1
        else int(
            gcd(
                n,
                s := int(
                    min(
                        min(crt((m, n // m), (0, -1))[0], crt((n // m, m), (0, -1))[0])
                        for m in (
                            prod(d)
                            for l in range(1, len(plist) // 2 + 1)
                            for d in combinations(plist, l)
                        )
                    )
                ),
            )
            > gcd(n, s + 1)
        )
    )


def A345994(n):
    if n == 1:
        return 1
    plist = tuple(p**q for p, q in factorint(n).items())
    return (
        1
        if len(plist) == 1
        else min(
            gcd(
                n,
                s := int(
                    min(
                        min(crt((m, n // m), (0, -1))[0], crt((n // m, m), (0, -1))[0])
                        for m in (
                            prod(d)
                            for l in range(1, len(plist) // 2 + 1)
                            for d in combinations(plist, l)
                        )
                    )
                ),
            ),
            gcd(n, s + 1),
        )
    )


def A346596(n):
    if n == 1:
        return 1
    plist = tuple(p**q for p, q in factorint(n).items())
    return (
        n
        if len(plist) == 1
        else max(
            gcd(
                n,
                s := int(
                    min(
                        min(crt((m, n // m), (0, -1))[0], crt((n // m, m), (0, -1))[0])
                        for m in (
                            prod(d)
                            for l in range(1, len(plist) // 2 + 1)
                            for d in combinations(plist, l)
                        )
                    )
                ),
            ),
            gcd(n, s + 1),
        )
    )


def A354411(n):
    if n == 1:
        return 2
    k = prod(plist := tuple(sieve.primerange(prime(n) + 1)))
    return (
        t := int(
            min(
                min(crt((m, k // m), (0, -1))[0], crt((k // m, m), (0, -1))[0])
                for m in (
                    prod(d)
                    for l in range(1, len(plist) // 2 + 1)
                    for d in combinations(plist, l)
                )
            )
        )
    ) * (t + 1)


def A354970_gen():  # generator of terms
    aqueue, f, a, b = deque([]), False, 1, 2
    yield from (1, 2)
    while True:
        c = b * (b - 1) // 2 + 1 + (b if f else a)
        yield c
        aqueue.append(c)
        if f:
            a, b = b, aqueue.popleft()
        f = not f


def A355017(n):
    return sum(1 for b in range(2, n) if isprime(sum(sympydigits(n, b)[1:])))


def A001923_gen():  # generator of terms
    yield from accumulate((k**k for k in count(1)), initial=0)


def A062970_gen():  # generator of terms
    yield from accumulate((k**k for k in count(1)), initial=1)


def A061789_gen():  # generator of terms
    yield from accumulate(((p := prime(k)) ** p for k in count(1)))


def A060946_gen():  # generator of terms
    yield from accumulate((k ** (k - 1) for k in count(1)))


def A001099_gen():  # generator of terms
    yield from accumulate((k**k for k in count(1)), func=lambda x, y: y - x)


def A185353_gen():  # generator of terms
    yield from accumulate(
        (pow(k, k, 10) for k in count(1)), func=lambda x, y: (x + y) % 10
    )


def A229784_gen():  # generator of terms
    yield from accumulate(
        (pow(k, k**k, 10) for k in count(1)), func=lambda x, y: (x + y) % 10
    )


def A128981_gen():  # generator of terms
    yield 1
    for i, j in enumerate(accumulate(k**k for k in count(1)), start=2):
        if j % i == 0:
            yield i


def A326501_gen():  # generator of terms
    yield from accumulate((-k) ** k for k in count(0))


def A343931_gen():  # generator of terms
    yield 1
    for i, j in enumerate(accumulate((-k) ** k for k in count(1)), start=2):
        if j % i == 0:
            yield i


def A188776_gen():  # generator of terms
    yield 1
    for i, j in enumerate(accumulate(k**k for k in count(2)), start=2):
        if not j % i:
            yield i


def A343932(n):
    return sum(pow(k, k, n) for k in range(1, n + 1)) % n


def A354894(n):
    return (comb(2 * n - 1, n - 1) * (harmonic(2 * n - 1) - harmonic(n - 1))).p


def A354895(n):
    return (comb(2 * n - 1, n - 1) * (harmonic(2 * n - 1) - harmonic(n - 1))).q


def A355057_gen():  # generator of terms
    aset, aqueue, c, b, f = {1}, deque([1]), 2, 1, True
    yield 1
    while True:
        for m in count(c):
            if m not in aset and gcd(m, b) == 1:
                yield prod(primefactors(b))
                aset.add(m)
                aqueue.append(m)
                if f:
                    aqueue.popleft()
                b = lcm(*aqueue)
                f = not f
                while c in aset:
                    c += 1
                break


def A354765_gen():  # generator of terms
    aset, aqueue, c, b, f = {1}, deque([1]), 2, 1, True
    yield 0
    while True:
        for m in count(c):
            if m not in aset and gcd(m, b) == 1:
                yield sum(2 ** (primepi(p) - 1) for p in primefactors(b))
                aset.add(m)
                aqueue.append(m)
                if f:
                    aqueue.popleft()
                b = lcm(*aqueue)
                f = not f
                while c in aset:
                    c += 1
                break


def A354764_gen():  # generator of terms
    aset, aqueue, c, b, f = {1}, deque([1]), 2, 1, True
    yield 1
    while True:
        for m in count(c):
            if m not in aset and gcd(m, b) == 1:
                yield prod(primefactors(m))
                aset.add(m)
                aqueue.append(m)
                if f:
                    aqueue.popleft()
                b = lcm(*aqueue)
                f = not f
                while c in aset:
                    c += 1
                break


def A343983_gen():  # generator of terms
    yield 1
    for k in count(1):
        if sum(pow(j, j, k) for j in divisors(k, generator=True)) % k == 1:
            yield k


def A062796(n):
    return sum(d**d for d in divisors(n, generator=True))


def A262843(n):
    return sum(d ** (d - 1) for d in divisors(n, generator=True))


def A283498(n):
    return sum(d ** (d + 1) for d in divisors(n, generator=True))


def A342628(n):
    return sum(d ** (n - d) for d in divisors(n, generator=True))


def A342629(n):
    return sum((n // d) ** (n - d) for d in divisors(n, generator=True))


def A308668(n):
    return sum(d ** (n // d + n) for d in divisors(n, generator=True))


def A308594(n):
    return sum(d ** (d + n) for d in divisors(n, generator=True))


def A023887(n):
    return divisor_sigma(n, n)


def A354975(n):
    return sum(prime(i + n) % prime(i) for i in range(1, n + 1))


def A355076(n):
    return sum(
        Fraction(
            reduce(
                lambda x, y: (x[0], x[0] + x[1]) if int(y) else (x[0] + x[1], x[1]),
                bin(k)[-1:1:-1],
                (1, 0),
            )[1],
            reduce(
                lambda x, y: (x[0], x[0] + x[1]) if int(y) else (x[0] + x[1], x[1]),
                bin(k + 1)[-1:1:-1],
                (1, 0),
            )[1],
        )
        for k in range(n + 1)
    ).denominator


def A355075(n):
    return sum(
        Fraction(
            reduce(
                lambda x, y: (x[0], x[0] + x[1]) if int(y) else (x[0] + x[1], x[1]),
                bin(k)[-1:1:-1],
                (1, 0),
            )[1],
            reduce(
                lambda x, y: (x[0], x[0] + x[1]) if int(y) else (x[0] + x[1], x[1]),
                bin(k + 1)[-1:1:-1],
                (1, 0),
            )[1],
        )
        for k in range(n + 1)
    ).numerator


def A324294(n):
    return reduce(
        lambda x, y: (x[0], x[0] + x[1]) if int(y) else (x[0] + x[1], x[1]),
        bin(divisor_sigma(n) + 1)[-1:1:-1],
        (1, 0),
    )[1]


def A244476(n):
    return sorted(
        set(
            sum(
                reduce(
                    lambda x, y: (x[0], x[0] + x[1]) if y else (x[0] + x[1], x[1]),
                    k,
                    (1, 0),
                )
            )
            for k in product((False, True), repeat=n)
        ),
        reverse=True,
    )[5]


def A244475(n):
    return sorted(
        set(
            sum(
                reduce(
                    lambda x, y: (x[0], x[0] + x[1]) if y else (x[0] + x[1], x[1]),
                    k,
                    (1, 0),
                )
            )
            for k in product((False, True), repeat=n)
        ),
        reverse=True,
    )[4]


def A244474(n):
    return sorted(
        set(
            sum(
                reduce(
                    lambda x, y: (x[0], x[0] + x[1]) if y else (x[0] + x[1], x[1]),
                    k,
                    (1, 0),
                )
            )
            for k in product((False, True), repeat=n)
        ),
        reverse=True,
    )[3]


def A002487(n):
    return (
        0
        if n == 0
        else sum(
            reduce(
                lambda x, y: (x[0], x[0] + x[1]) if int(y) else (x[0] + x[1], x[1]),
                bin(n)[-1:2:-1],
                (1, 0),
            )
        )
    )


def A240388(n):
    return (
        sum(
            reduce(
                lambda x, y: (x[0], x[0] + x[1]) if int(y) else (x[0] + x[1], x[1]),
                bin(3 * n)[-1:2:-1],
                (1, 0),
            )
        )
        // 2
    )


def A293957(n):
    return (
        0
        if n <= 2
        else max(
            Counter(
                m
                for m in (
                    sum(
                        reduce(
                            lambda x, y: (x[0], x[0] + x[1])
                            if y
                            else (x[0] + x[1], x[1]),
                            chain(k, (1,)),
                            (1, 0),
                        )
                    )
                    for k in product((False, True), repeat=n - 2)
                )
                if m != 1 and m != 2
            ).values()
        )
    )


def A293160(n):
    return (
        n
        if n <= 1
        else len(
            {1}
            | set(
                sum(
                    reduce(
                        lambda x, y: (x[0], x[0] + x[1]) if y else (x[0] + x[1], x[1]),
                        chain(k, (1,)),
                        (1, 0),
                    )
                )
                for k in product((False, True), repeat=n - 2)
            )
        )
    )


def A101624(n):
    return sum(int(not k & ~(n - k)) * 2**k for k in range(n // 2 + 1))


def A006921(n):
    return sum(int(not r & ~(n - r)) * 2 ** (n // 2 - r) for r in range(n // 2 + 1))


def A260022(n):
    return sum(int(not r & ~(2 * n - r)) * 2 ** (n - r) for r in range(n + 1))


def A168081(n):
    return sum(int(not r & ~(2 * n - 1 - r)) * 2 ** (n - 1 - r) for r in range(n))


def A257971(n):
    return (
        sum(
            int(not r & ~(n + 2 - r)) * 2 ** (n // 2 + 1 - r) for r in range(n // 2 + 2)
        )
        if n & 1
        else -sum(
            int(not r & ~(n - 1 - r)) * 2 ** (n // 2 - 1 - r) for r in range(n // 2)
        )
    )


def A355009_gen():  # generator of terms
    return filter(
        isprime,
        (sum(prime(i + n) % prime(i) for i in range(1, n + 1)) for n in count(1)),
    )


def A354972_gen():  # generator of terms
    for n in count(1):
        if isprime(sum(prime(i + n) % prime(i) for i in range(1, n + 1))):
            yield n


def A353196(n):
    return prod((1 << i) + 1 for i in range(1, n + 1)) << n


def A028362(n):
    return prod((1 << i) + 1 for i in range(1, n))


def A355140(n):
    return (2 * n + (d := divisor_count(n))) // (2 * d)


def A334762(n):
    return (a := divmod(n, divisor_count(n)))[0] + int((a[1] > 0) == True)


def A090395(n):
    return n // gcd(n, divisor_count(n))


def A090387(n):
    return (d := divisor_count(n)) // gcd(n, d)


def A353172(n):
    a = primeomega(n)
    for k in count(2):
        if (m := n % k) > 0 and primeomega(m) == a:
            return k


def A003956(n):
    return prod((1 << i) - 1 for i in range(2, 2 * n + 1, 2)) << n * (n + 2) + 3


def A014115(n):
    return (
        2
        if n == 0
        else ((1 << n) - 1) * prod((1 << i) - 1 for i in range(2, 2 * n - 1, 2))
        << n * (n + 1) + 1
    )


def A014116(n):
    return (
        2 + 696729598 * (n // 3)
        if n == 0 or n == 3
        else ((1 << n) - 1) * prod((1 << i) - 1 for i in range(2, 2 * n - 1, 2))
        << n * (n + 1) + 1
    )


def A001309(n):
    return (
        2
        if n == 0
        else ((1 << n) - 1) * prod((1 << i) - 1 for i in range(2, 2 * n - 1, 2))
        << n * (n + 1) + 2
    )


def A003053(n):
    return (1 << (n // 2) ** 2) * prod(
        (1 << i) - 1 for i in range(2, 2 * ((n - 1) // 2) + 1, 2)
    )


def A090770(n):
    return prod((1 << i) - 1 for i in range(2, 2 * n + 1, 2)) << (n + 1) ** 2


def A003923(n):
    return (1 << n**2) * prod((1 << i) - 1 for i in range(2, 2 * n + 1, 2))


def A144545(n):
    return ((1 << n) + 1) * prod((1 << i) - 1 for i in range(2, 2 * n - 1, 2)) << n * (
        n - 1
    )


def A000296_gen():
    yield from (1, 0)
    blist, a, b = (1,), 0, 1
    while True:
        blist = list(accumulate(blist, initial=(b := blist[-1])))
        yield (a := b - a)


def A105479_gen():  # generator of terms
    yield from (0, 0, 1)
    blist, b, c = (1,), 1, 1
    for n in count(2):
        c += n
        blist = list(accumulate(blist, initial=(b := blist[-1])))
        yield b * c


def A064299_gen():  # generator of terms
    yield from (1, 1)
    blist, b, m = (1, 2), 1, 1
    for n in count(1):
        blist = list(accumulate(blist, initial=(b := blist[-1])))
        yield b * (m := m * (4 * n + 2) // (n + 2))


def A064299(n):
    return bell(n) * catalan(n)


def A099977_gen():  # generator of terms
    yield 1
    blist, b = (1, 2), 1
    while True:
        for _ in range(2):
            blist = list(accumulate(blist, initial=(b := blist[-1])))
        yield b


def A020557_gen():  # generator of terms
    yield 1
    blist, b = (1,), 1
    while True:
        for _ in range(2):
            blist = list(accumulate(blist, initial=(b := blist[-1])))
        yield b


def A070906_gen():  # generator of terms
    yield 1
    blist, b = (1,), 1
    while True:
        for _ in range(3):
            blist = list(accumulate(blist, initial=(b := blist[-1])))
        yield b


def A135084(n):
    return bell(2**n - 1)


def A135085(n):
    return bell(2**n)


def A193274_gen():  # generator of terms
    yield 0
    blist, b = (1,), 1
    while True:
        blist = list(accumulate(blist, initial=(b := blist[-1])))
        yield b * (b - 1) // 2


def A068939(n):
    return bell(n**2)


def A092460_gen():  # generator of terms
    yield 0
    blist, b = (1,), 1
    while True:
        blist = list(accumulate(blist, initial=b))
        yield from range(b + 1, b := blist[-1])


def A325630_gen():  # generator of terms
    blist, b = (1,), 1
    for k in count(1):
        blist = list(accumulate(blist, initial=(b := blist[-1])))
        if b % k == 0:
            yield k


def A091772_gen():  # generator of terms
    yield 1
    blist, b, c = (1, 2), 1, 1
    for n in count(1):
        blist = list(accumulate(blist, initial=(b := blist[-1])))
        yield gcd(b, c := c * (4 * n + 2) // (n + 2))


def A113865(n):
    return len(str(bell(n)))


if sys.version_info >= (3, 10):

    def A166266(n):
        return int(bell(n)).bit_count()

else:

    def A166266(n):
        return bin(bell(n)).count("1")


def A204618_gen():  # generator of terms
    yield 0
    blist, b = (1,), 1
    for n in count(1):
        blist = list(accumulate(blist, initial=(b := blist[-1])))
        yield b * n**2


def A217143_gen():  # generator of terms
    yield 1
    blist, b, c = (1,), 1, 1
    while True:
        blist = list(accumulate(blist, initial=(b := blist[-1])))
        yield (c := c + b**2)


def A217144_gen():  # generator of terms
    yield 1
    blist, b, c, f = (1,), 1, 1, 1
    while True:
        blist = list(accumulate(blist, initial=(b := blist[-1])))
        yield (f := -f) * (c := c + f * b**2)


def A278973(n):
    return divisor_count(bell(n))


def A070907_gen():  # generator of terms
    yield 1
    blist, b = (1,), 1
    while True:
        for _ in range(4):
            blist = list(accumulate(blist, initial=(b := blist[-1])))
        yield b


def A070908_gen():  # generator of terms
    yield 1
    blist, b = (1,), 1
    while True:
        for _ in range(5):
            blist = list(accumulate(blist, initial=(b := blist[-1])))
        yield b


def A003422_gen():  # generator of terms
    yield from (0, 1)
    c, f = 1, 1
    for n in count(1):
        yield (c := c + (f := f * n))


def A006472(n):
    return n * factorial(n - 1) ** 2 >> n - 1


def A355171(n):
    f = factorial(n + 1)
    return sum(f * comb(n, k + 1) // (k + 2) // (k + 1) for k in range(n + 1))


def A009003_gen():  # generator of terms
    return filter(lambda n: any(map(lambda p: p % 4 == 1, primefactors(n))), count(1))


def A001705(n):
    f = factorial(n)
    return sum(f * (k + 1) // (n - k) for k in range(n))


def A157037_gen():  # generator of terms
    return filter(
        lambda n: isprime(sum(n * e // p for p, e in factorint(n).items())), count(2)
    )


def A353704_gen():  # generator of terms
    return filter(
        lambda n: isprime(sum(n * e // p for p, e in factorint(n).items())),
        (d * (10**l - 1) // 9 for l in count(1) for d in (1, 2, 3, 5, 6, 7)),
    )


def A353703_gen():  # generator of terms
    return filter(
        lambda n: isprime(sum(n * e // p for p, e in factorint(n).items())),
        chain.from_iterable(
            chain(
                (int((s := str(d)) + s[-2::-1]) for d in range(10**l, 10 ** (l + 1))),
                (int((s := str(d)) + s[::-1]) for d in range(10**l, 10 ** (l + 1))),
            )
            for l in count(0)
        ),
    )


def A029803_gen():  # generator of terms
    return chain(
        (0,),
        chain.from_iterable(
            chain(
                (
                    int((s := oct(d)[2:]) + s[-2::-1], 8)
                    for d in range(8**l, 8 ** (l + 1))
                ),
                (
                    int((s := oct(d)[2:]) + s[::-1], 8)
                    for d in range(8**l, 8 ** (l + 1))
                ),
            )
            for l in count(0)
        ),
    )


def A029733_gen():  # generator of terms
    return filter(
        lambda k: (s := hex(k**2)[2:])[: (t := (len(s) + 1) // 2)]
        == s[: -t - 1 : -1],
        count(0),
    )


def A029805_gen():  # generator of terms
    return filter(
        lambda k: (s := oct(k**2)[2:])[: (t := (len(s) + 1) // 2)]
        == s[: -t - 1 : -1],
        count(0),
    )


def A002778_gen():  # generator of terms
    return filter(
        lambda k: (s := str(k**2))[: (t := (len(s) + 1) // 2)] == s[: -t - 1 : -1],
        count(0),
    )


def A136522(n):
    return int((s := str(n))[: (t := (len(s) + 1) // 2)] == s[: -t - 1 : -1])


def A029983_gen():  # generator of terms
    return filter(
        lambda k: (s := bin(k)[2:])[: (t := (len(s) + 1) // 2)] == s[: -t - 1 : -1],
        (k**2 for k in count(0)),
    )


def A003166_gen():  # generator of terms
    return filter(
        lambda k: (s := bin(k**2)[2:])[: (t := (len(s) + 1) // 2)]
        == s[: -t - 1 : -1],
        count(0),
    )


def A128921_gen():  # generator of terms
    return filter(
        lambda n: is_square(int(str(n**2)[::-1])),
        chain(
            (0,),
            chain.from_iterable(
                chain(
                    (
                        int((s := str(d)) + s[-2::-1])
                        for d in range(10**l, 10 ** (l + 1))
                    ),
                    (
                        int((s := str(d)) + s[::-1])
                        for d in range(10**l, 10 ** (l + 1))
                    ),
                )
                for l in count(0)
            ),
        ),
    )


def A319483_gen():  # generator of terms
    return filter(
        lambda n: is_square(int(str(n)[::-1])),
        map(
            lambda n: n**2,
            chain(
                (0,),
                chain.from_iterable(
                    chain(
                        (
                            int((s := str(d)) + s[-2::-1])
                            for d in range(10**l, 10 ** (l + 1))
                        ),
                        (
                            int((s := str(d)) + s[::-1])
                            for d in range(10**l, 10 ** (l + 1))
                        ),
                    )
                    for l in count(0)
                ),
            ),
        ),
    )


def A302864(n):
    for k in count(0, 2):
        if (s := str(k + 1 << n))[: (t := (len(s) + 1) // 2)] == s[: -t - 1 : -1]:
            return k + 1 << n


def A280876_gen():  # generator of terms
    return filter(
        lambda n: isprime(n) and isprime(primepi(n)),
        chain.from_iterable(
            chain(
                (int((s := str(d)) + s[-2::-1]) for d in range(10**l, 10 ** (l + 1))),
                (int((s := str(d)) + s[::-1]) for d in range(10**l, 10 ** (l + 1))),
            )
            for l in count(0)
        ),
    )


def A309325_gen():  # generator of terms
    c = 0
    for a in chain.from_iterable(
        chain(
            (int((s := str(d)) + s[-2::-1]) for d in range(10**l, 10 ** (l + 1))),
            (int((s := str(d)) + s[::-1]) for d in range(10**l, 10 ** (l + 1))),
        )
        for l in count(0)
    ):
        yield c + (c := a)


def A076612_gen():  # generator of terms
    return chain(
        (1, 4, 6, 8, 9),
        chain.from_iterable(
            (
                int((s := str(d)) + e + s[::-1])
                for d in range(10**l, 10 ** (l + 1))
                for e in "014689"
            )
            for l in count(0)
        ),
    )


def A089717_gen():  # generator of terms
    return map(
        lambda n: n * (n + 1) // 2,
        chain(
            (0,),
            chain.from_iterable(
                chain(
                    (
                        int((s := str(d)) + s[-2::-1])
                        for d in range(10**l, 10 ** (l + 1))
                    ),
                    (
                        int((s := str(d)) + s[::-1])
                        for d in range(10**l, 10 ** (l + 1))
                    ),
                )
                for l in count(0)
            ),
        ),
    )


def A082208_gen():  # generator of terms
    return filter(
        lambda n: (s := str(sum(int(d) for d in str(n))))[: (t := (len(s) + 1) // 2)]
        == s[: -t - 1 : -1],
        chain(
            (0,),
            chain.from_iterable(
                chain(
                    (
                        int((s := str(d)) + s[-2::-1])
                        for d in range(10**l, 10 ** (l + 1))
                    ),
                    (
                        int((s := str(d)) + s[::-1])
                        for d in range(10**l, 10 ** (l + 1))
                    ),
                )
                for l in count(0)
            ),
        ),
    )


def A083851_gen():  # generator of terms
    return filter(
        lambda n: n % 11,
        chain.from_iterable(
            (int((s := str(d)) + s[-2::-1]) for d in range(10**l, 10 ** (l + 1)))
            for l in count(0)
        ),
    )


def A027829_gen():  # generator of terms
    return filter(
        lambda n: (s := str(n))[: (t := (len(s) + 1) // 2)] == s[: -t - 1 : -1],
        map(
            lambda n: n**2,
            (
                d
                for l in count(2, 2)
                for d in range(isqrt(10 ** (l - 1)) + 1, isqrt(10**l) + 1)
            ),
        ),
    )


def A353217_gen():  # generator of terms
    return chain(
        (0, 1),
        filter(
            lambda m: (s := str(sum((m * e // p for p, e in factorint(m).items()))))[
                : (t := (len(s) + 1) // 2)
            ]
            == s[: -t - 1 : -1],
            (n * (n + 1) // 2 for n in count(2)),
        ),
    )


def A068312(n):
    return (
        0
        if n <= 1
        else (
            (n + 1) * sum((n * e // p for p, e in factorint(n).items()))
            + sum(((n + 1) * e // p for p, e in factorint(n + 1).items())) * n
            - (n * (n + 1) // 2)
        )
        // 2
    )


def A324989_gen():  # generator of terms
    return filter(
        lambda n: (
            s := str(isqrt(n) ** d if (d := divisor_count(n)) & 1 else n ** (d // 2))
        )[: (t := (len(s) + 1) // 2)]
        == s[: -t - 1 : -1],
        chain.from_iterable(
            chain(
                (int((s := str(d)) + s[-2::-1]) for d in range(10**l, 10 ** (l + 1))),
                (int((s := str(d)) + s[::-1]) for d in range(10**l, 10 ** (l + 1))),
            )
            for l in count(0)
        ),
    )


def A175317(n):
    return sum(
        isqrt(d) ** c if (c := divisor_count(d)) & 1 else d ** (c // 2)
        for d in divisors(n, generator=True)
    )


def A322671(n):
    return sum(
        isqrt(d) ** (c - 2) if (c := divisor_count(d)) & 1 else d ** (c // 2 - 1)
        for d in divisors(n, generator=True)
    )


def A174933(n):
    return sum(
        isqrt(d) ** (c + 2) if (c := divisor_count(d)) & 1 else d ** (c // 2 + 1)
        for d in divisors(n, generator=True)
    )


def A174939(n):
    return sum(k ** divisor_count(k) for k in range(1, n + 1))


def A174932(n):
    return n * sum(
        isqrt(d) ** (c - 2) if (c := divisor_count(d)) & 1 else d ** (c // 2 - 1)
        for d in divisors(n, generator=True)
    )


def A055067(n):
    return factorial(n) // (
        isqrt(n) ** c if (c := divisor_count(n)) & 1 else n ** (c // 2)
    )


def A072046(n):
    return gcd(
        p := isqrt(n) ** c if (c := divisor_count(n)) & 1 else n ** (c // 2),
        factorial(n) // p,
    )


def A280581(n):
    return (lambda m: isqrt(m) ** c if (c := divisor_count(m)) & 1 else m ** (c // 2))(
        divisor_sigma(n)
    )


def A048740(n):
    return (lambda m: isqrt(m) ** c if (c := divisor_count(m)) & 1 else m ** (c // 2))(
        composite(n)
    )


def A056924(n):
    return divisor_count(n) // 2


def A056925(n):
    return n ** (divisor_count(n) // 2)


def A219364_gen():  # generator of terms
    return filter(
        lambda n: (
            f := (
                lambda m: isqrt(m) ** c
                if (c := divisor_count(m)) & 1
                else m ** (c // 2)
            )
        )(n)
        > f(divisor_sigma(n)),
        count(1),
    )


def A280420(n):
    return (lambda m: (isqrt(m) if (c := divisor_count(m)) & 1 else 1) * m ** (c // 2))(
        factorial(n)
    )


def A027423(n):
    return prod(
        e + 1
        for e in sum(
            (Counter(factorint(i)) for i in range(2, n + 1)), start=Counter()
        ).values()
    )


def A355224(n):
    return int("".join(accumulate(str(n)[::-1], func=max))[::-1])


def A355223(n):
    return int("".join(accumulate(str(n)[::-1], func=min))[::-1])


def A355222(n):
    return int("".join(accumulate(str(n), func=max)))


def A355221(n):
    return int("".join(accumulate(str(n), func=min)))


def A280583(n):
    return (lambda m: (isqrt(m) if (c := divisor_count(m)) & 1 else 1) * m ** (c // 2))(
        divisor_count(n)
    )


def A353929(n):
    return len(set(sum(map(int, y[1])) for y in groupby(bin(n)[2:])))


def A280685(n):
    return divisor_sigma(
        (isqrt(n) if (c := divisor_count(n)) & 1 else 1) * n ** (c // 2)
    )


def A157195(n):
    return (
        0
        if (c := divisor_count(n)) <= 2
        else (isqrt(n) if (c := divisor_count(n)) & 1 else 1) * n ** (c // 2 - 1)
    )


def A309377(n):
    return (
        isqrt(n**n)
        if (c := prod(n * e + 1 for e in factorint(n).values())) & 1
        else 1
    ) * n ** (n * (c // 2))


def A325838(n):
    return (lambda m: (isqrt(m) if (c := divisor_count(m)) & 1 else 1) * m ** (c // 2))(
        n * (n + 1) // 2
    )


def A084190(n):
    return lcm(*(d - 1 for d in divisors(n, generator=True) if d > 1))


def A162947_gen():  # generator of terms
    return chain((1,), filter(lambda n: divisor_count(n) == 6, count(2)))


def A344687(n):
    return (
        prod(
            e + 1
            for e in sum(
                (Counter(factorint(i)) for i in range(2, n + 1)), start=Counter()
            ).values()
        )
        // 2
    )


def A157672(n):
    return (
        prod(
            e + 1
            for e in sum(
                (Counter(factorint(i)) for i in range(2, n + 1)), start=Counter()
            ).values()
        )
        // 2
        - 1
    )


def A338576(n):
    return (isqrt(n) if (c := divisor_count(n)) & 1 else 1) * n ** (c // 2 + 1)


def A283995(n):
    return (
        lambda n: prod(
            prime(i + 1) ** e
            for i, e in enumerate(sorted(factorint(n).values(), reverse=True))
        )
    )((isqrt(n) if (c := divisor_count(n)) & 1 else 1) * n ** (c // 2))


def A184390(n):
    return (
        (m := ((isqrt(n) if (c := divisor_count(n)) & 1 else 1) * n ** (c // 2)))
        * (m + 1)
        // 2
    )


def A184391(n):
    return factorial((isqrt(n) if (c := divisor_count(n)) & 1 else 1) * n ** (c // 2))


def A354773_gen():  # generator of terms
    aset, aqueue, b, f = {0, 1, 2}, deque([2]), 2, False
    while True:
        for k in count(1):
            m, j, j2, r, s = 0, 0, 1, b, k
            while r > 0:
                r, q = divmod(r, 2)
                if not q:
                    s, y = divmod(s, 2)
                    m += y * j2
                j += 1
                j2 *= 2
            if s > 0:
                m += s * 2 ** b.bit_length()
            if m not in aset:
                if (s := bin(m)[:1:-1]).count("1") == 2:
                    yield s.index("1")
                aset.add(m)
                aqueue.append(m)
                if f:
                    aqueue.popleft()
                b = reduce(or_, aqueue)
                f = not f
                break


def A354774_gen():  # generator of terms
    aset, aqueue, b, f = {0, 1, 2}, deque([2]), 2, False
    while True:
        for k in count(1):
            m, j, j2, r, s = 0, 0, 1, b, k
            while r > 0:
                r, q = divmod(r, 2)
                if not q:
                    s, y = divmod(s, 2)
                    m += y * j2
                j += 1
                j2 *= 2
            if s > 0:
                m += s * 2 ** b.bit_length()
            if m not in aset:
                if (s := bin(m)[3:]).count("1") == 1:
                    yield len(s)
                aset.add(m)
                aqueue.append(m)
                if f:
                    aqueue.popleft()
                b = reduce(or_, aqueue)
                f = not f
                break


def A354775_gen():  # generator of terms
    aset, aqueue, b, f, i = {0, 1, 2}, deque([2]), 2, False, 2
    while True:
        for k in count(1):
            m, j, j2, r, s = 0, 0, 1, b, k
            while r > 0:
                r, q = divmod(r, 2)
                if not q:
                    s, y = divmod(s, 2)
                    m += y * j2
                j += 1
                j2 *= 2
            if s > 0:
                m += s * 2 ** b.bit_length()
            if m not in aset:
                i += 1
                if "11" in (s := bin(m)[2:]) and s.count("1") == 2:
                    yield i
                aset.add(m)
                aqueue.append(m)
                if f:
                    aqueue.popleft()
                b = reduce(or_, aqueue)
                f = not f
                break


def A001481_gen():  # generator of terms
    return filter(
        lambda n: (lambda m: all(d & 3 != 3 or m[d] & 1 == 0 for d in m))(factorint(n)),
        count(0),
    )


def A354776_gen():  # generator of terms
    return filter(
        lambda n: (lambda m: all(d & 3 != 3 or m[d] & 1 == 0 for d in m))(
            factorint(n // 2)
        ),
        count(0, 2),
    )


def A071011_gen():  # generator of terms
    return filter(
        lambda n: (
            lambda f: all(p & 3 != 3 or e & 1 == 0 for p, e in f)
            and prod((p ** (e + 1) - 1) // (p - 1) & 3 for p, e in f) & 3 == 0
        )(factorint(n).items()),
        count(0),
    )


def A155563_gen():  # generator of terms
    return filter(
        lambda n: all(
            e & 1 == 0 or (p & 3 != 3 and p % 3 < 2) for p, e in factorint(n).items()
        ),
        count(0),
    )


def A173256_gen():  # generator of terms
    return accumulate(
        filter(
            lambda n: all(p & 3 != 3 or e & 1 == 0 for p, e in factorint(n).items()),
            count(0),
        )
    )


def A250310_gen():  # generator of terms
    return filter(
        lambda n: all(
            p & 3 != 3 or e & 1 == 0 for p, e in factorint(n**2 - 3).items()
        ),
        count(2),
    )


def A124132_gen():  # generator of terms
    return filter(
        lambda n: all(
            p & 3 != 3 or e & 1 == 0 for p, e in factorint(fibonacci(2 * n)).items()
        ),
        count(1),
    )


def A124130_gen():  # generator of terms
    return filter(
        lambda n: all(p & 3 != 3 or e & 1 == 0 for p, e in factorint(lucas(n)).items()),
        count(0),
    )


def A125110_gen():  # generator of terms
    return map(
        lambda m: m**3,
        filter(
            lambda n: all(p & 3 != 3 or e & 1 == 0 for p, e in factorint(n).items()),
            count(0),
        ),
    )


def A269833_gen():  # generator of terms
    return filter(
        lambda n: all(
            p & 3 != 3 or e & 1 == 0
            for p, e in factorint((1 << n) + factorial(n)).items()
        ),
        count(0),
    )


def A002479_gen():  # generator of terms
    return filter(
        lambda n: all(p & 7 < 5 or e & 1 == 0 for p, e in factorint(n).items()),
        count(0),
    )


def A155562_gen():  # generator of terms
    return filter(
        lambda n: all(
            (p & 3 != 3 and p & 7 < 5) or e & 1 == 0 for p, e in factorint(n).items()
        ),
        count(0),
    )


def A124134_gen():  # generator of terms
    return filter(
        lambda n: n & 1
        or all(p & 3 != 3 or e & 1 == 0 for p, e in factorint(fibonacci(n)).items()),
        count(1),
    )


def A236264_gen():  # generator of terms
    return filter(
        lambda n: all(
            p & 3 != 3 or e & 1 == 0 for p, e in factorint(fibonacci(n)).items()
        ),
        count(0, 2),
    )


def A180590_gen():  # generator of terms
    return filter(
        lambda n: all(
            p & 3 != 3 or e & 1 == 0 for p, e in factorint(4 * factorial(n) + 1).items()
        ),
        count(0),
    )


def A000118(n):
    return (
        1
        if n == 0
        else 8 * divisor_sigma(n)
        if n % 2
        else 24 * divisor_sigma(int(bin(n)[2:].rstrip("0"), 2))
    )


def A333911_gen():  # generator of terms
    return filter(
        lambda n: all(
            p & 3 != 3 or e & 1 == 0
            for p, e in sum(
                (
                    Counter(factorint((p ** (e + 1) - 1) // (p - 1)))
                    for p, e in factorint(n).items()
                ),
                start=Counter(),
            ).items()
        ),
        count(1),
    )


def A333910_gen():  # generator of terms
    return filter(
        lambda n: all(
            p & 3 != 3 or e & 1 == 0
            for p, e in sum(
                (
                    Counter(factorint(1 + p)) + Counter({p: e - 1})
                    for p, e in factorint(n).items()
                ),
                start=Counter(),
            ).items()
        ),
        count(1),
    )


def A333909_gen():  # generator of terms
    return filter(
        lambda n: all(
            p & 3 != 3 or e & 1 == 0 for p, e in factorint(totient(n)).items()
        ),
        count(1),
    )


def A268379_gen():  # generator of terms
    return filter(
        lambda n: sum((f := factorint(n)).values()) - f.get(2, 0)
        < 2 * sum(f[p] for p in f if p & 3 == 1),
        count(1),
    )


def A263715_gen():  # generator of terms
    return filter(
        lambda n: n & 3 != 2
        or all(p & 3 != 3 or e & 1 == 0 for p, e in factorint(n).items()),
        count(0),
    )


def A022544_gen():  # generator of terms
    return filter(
        lambda n: any(p & 3 == 3 and e & 1 for p, e in factorint(n).items()), count(0)
    )


def A263737_gen():  # generator of terms
    return filter(
        lambda n: n & 3 != 2
        and any(p & 3 == 3 and e & 1 for p, e in factorint(n).items()),
        count(0),
    )


def A260728(n):
    return reduce(or_, (e for p, e in factorint(n).items() if p & 3 == 3), 0)


def A229062(n):
    return int(all(p & 3 != 3 or e & 1 == 0 for p, e in factorint(n).items()))


def A102548_gen():  # generator of terms
    return accumulate(
        int(all(p & 3 != 3 or e & 1 == 0 for p, e in factorint(n).items()))
        for n in count(1)
    )


def A097706(n):
    return prod(p**e for p, e in factorint(n).items() if p & 3 == 3)


def A102574(n):
    return prod(
        (q := int(p & 3 == 3)) * (p ** (2 * (e + 1)) - 1) // (p**2 - 1)
        + (1 - q) * (p ** (2 * e + 1) - 1) // (p - 1)
        for p, e in factorint(n).items()
    )


def A057653_gen():  # generator of terms
    return filter(
        lambda n: all(p & 3 != 3 or e & 1 == 0 for p, e in factorint(n).items()),
        count(1, 2),
    )


def A097269_gen():  # generator of terms
    return filter(
        lambda n: all(p & 3 != 3 or e & 1 == 0 for p, e in factorint(n // 2).items()),
        count(2, 4),
    )


def A073613_gen():  # generator of terms
    return filter(
        lambda n: all(p & 3 != 3 or e & 1 == 0 for p, e in factorint(n).items()),
        (m * (m + 1) // 2 for m in count(0)),
    )


def A035251_gen():  # generator of terms
    return filter(
        lambda n: all(not ((2 < p & 7 < 7) and e & 1) for p, e in factorint(n).items()),
        count(1),
    )


def A232531_gen():  # generator of terms
    return filter(
        lambda n: any((2 < p & 7 < 7) and e & 1 for p, e in factorint(n).items()),
        count(1),
    )


def A046711_gen():  # generator of terms
    return filter(
        lambda n: 0 < n & 3 < 3
        and all(p & 3 != 3 or e & 1 == 0 for p, e in factorint(n).items()),
        count(0),
    )


def A031363_gen():  # generator of terms
    return filter(
        lambda n: all(not ((1 < p % 5 < 4) and e & 1) for p, e in factorint(n).items()),
        count(1),
    )


def A020893_gen():  # generator of terms
    return filter(
        lambda n: all(p & 3 != 3 and e == 1 for p, e in factorint(n).items()), count(1)
    )


def A014198_gen():  # generator of terms
    return accumulate(
        map(
            lambda n: prod(
                e + 1 if p & 3 == 1 else (e + 1) & 1
                for p, e in factorint(n).items()
                if p > 2
            )
            << 2,
            count(1),
        ),
        initial=0,
    )


def A355175(n):
    return Matrix(
        n, n, [(i - j) ** 2 + int(i == j) for i in range(n) for j in range(n)]
    ).det()


def A048727(n):
    return n ^ n << 1 ^ n << 2


def A048730(n):
    return 7 * n - (n ^ n << 1 ^ n << 2)


def A284557(n):
    return (n ^ n << 1 ^ n << 2) % 3


def A269160(n):
    return n ^ (n << 1 | n << 2)


def A048725(n):
    return n ^ n << 2


def A269161(n):
    return n << 2 ^ (n << 1 | n)


def A213370(n):
    return n & n << 1


def A048735(n):
    return n & n >> 1


def A353168_gen():  # generator of terms
    return chain(
        (0,),
        chain.from_iterable(
            (
                sorted(n ^ n << 1 ^ n << 2 for n in range(2**l, 2 ** (l + 1)))
                for l in count(0)
            )
        ),
    )


def A355326(n):
    return Matrix(
        n, n, [1 if i == j else (i - j) ** 3 for i in range(n) for j in range(n)]
    ).det()


def A292272(n):
    return n & ~(n >> 1)


def A003188(n):
    return n ^ n >> 1


def A048728(n):
    return 3 * n - (n ^ n << 1)


def A229762(n):
    return ~n & n >> 1


def A229763(n):
    return n & ~(n << 1)


def A269170(n):
    return n | n >> 1


def A213064(n):
    return n << 1 & ~n


def A006068(n):
    k, m = n, n >> 1
    while m > 0:
        k ^= m
        m >>= 1
    return k


def A268717(n):
    k, m = n - 1, n - 1 >> 1
    while m > 0:
        k ^= m
        m >>= 1
    return k + 1 ^ k + 1 >> 1


def A268718(n):
    if n == 0:
        return 0
    k, m = n, n >> 1
    while m > 0:
        k ^= m
        m >>= 1
    return 1 + (k - 1 ^ k - 1 >> 1)


def A055975(n):
    return (n ^ n >> 1) - (n - 1 ^ n - 1 >> 1)


def A064706(n):
    return n ^ n >> 2


def A065621(n):
    return n ^ (n & ~-n) << 1


def A277823(n):
    return (m := n ^ (n & ~-n) << 1) ^ m << 1


def A245471(n):
    return (m := n + 1) ^ (m & ~-m) << 1 if n & 1 else n >> 1


def A114390(n):
    return (m := n**2) ^ (m & ~-m) << 1


def A284552(n):
    return (n ^ (n & ~-n) << 1) % n


def A048724(n):
    return n ^ n << 1


def A105081(n):
    return 1 + (n - 1 ^ n - 1 >> 1)


def A048726(n):
    return (n ^ n << 1) << 1


def A284574(n):
    return (n ^ n << 1) % 3


def A178729(n):
    return n ^ 3 * n


def A142149(n):
    return n if n & 1 else (n ^ n >> 1)


def A178734(n):
    return n ^ n << 3


def A277825(n):
    return (m := n ^ (n & ~-n) << 1) ^ m << 2


def A269137(n):
    return (n ^ n << 1) | (n ^ n << 2)


def A338524(n):
    k = prime(n)
    m = k >> 1
    while m > 0:
        k ^= m
        m >>= 1
    return k


def A143292(n):
    return (p := prime(n)) ^ p >> 1


def A292204_gen():  # generator of terms
    for n in count(0):
        k, m = n, n >> 1
        while m > 0:
            k ^= m
            m >>= 1
        if isprime(k):
            yield k


def A292600(n):
    k, m = n >> 1, n >> 2
    while m > 0:
        k ^= m
        m >>= 1
    return k


def A292601(n):
    k, m = n >> 1, n >> 2
    while m > 0:
        k ^= m
        m >>= 1
    return n - k


def A286546(n):
    k, m = n, n >> 1
    while m > 0:
        k ^= m
        m >>= 1
    return k - n


def A268716(n):
    k, m = n, n >> 1
    while m > 0:
        k ^= m
        m >>= 1
    return k << 1


def A268723(n):
    k, m = n, n >> 1
    while m > 0:
        k ^= m
        m >>= 1
    return (a := k**2) ^ a >> 1


def A268722(n):
    k, m = n, n >> 1
    while m > 0:
        k ^= m
        m >>= 1
    return (a := 3 * k) ^ a >> 1


def A268384_gen():  # generator of terms
    a = -1
    for n in count(0):
        b = int("".join(str(int(not (~n & k))) for k in range(n + 1)), 2)
        yield from (0,) * (b - a - 1)
        yield 1
        a = b


def A059905(n):
    return int(bin(n)[:1:-2][::-1], 2)


def A059906(n):
    return 0 if n < 2 else int(bin(n)[-2:1:-2][::-1], 2)


def A292371(n):
    return int(bin(n & ~(n >> 1))[:1:-2][::-1], 2)


def A292372(n):
    return 0 if (m := n & ~(n << 1)) < 2 else int(bin(m)[-2:1:-2][::-1], 2)


def A292373(n):
    return int(bin(n & n >> 1)[:1:-2][::-1], 2)


def A309952(n):
    return int(
        "".join(
            map(
                lambda x: str(xor(*x)),
                zip_longest(
                    (s := tuple(int(d) for d in bin(n)[2:]))[::-2],
                    s[-2::-2],
                    fillvalue=0,
                ),
            )
        )[::-1],
        2,
    )


def A057643(n):
    return lcm(*(d + 1 for d in divisors(n, generator=True)))


def A020696(n):
    return prod(d + 1 for d in divisors(n, generator=True))


def A355331_gen(startvalue=1):  # generator of terms
    return filter(
        lambda n: reduce(
            lambda a, b: a * b % n, (d + 1 for d in divisors(n, generator=True))
        )
        % n
        == 0,
        count(max(startvalue, 1)),
    )


def A062383(n):
    return 1 << n.bit_length()


def A142151(n):
    return (
        0
        if n == 0
        else reduce(or_, (k ^ n - k for k in range(n + 1)))
        if n % 2
        else (1 << n.bit_length() - 1) - 1 << 1
    )


def A153587(n):
    return n % ((1 << n.bit_length()) - n)


def A080079(n):
    return (1 << n.bit_length()) - n


def A029837(n):
    return (n - 1).bit_length()


def A035928_gen(startvalue=1):  # generator of terms
    return filter(
        lambda n: n
        == int(
            format(~n & (1 << (m := n.bit_length())) - 1, "0" + str(m) + "b")[::-1], 2
        ),
        count(max(startvalue, 1)),
    )


def A072376(n):
    return n if n < 2 else 1 << n.bit_length() - 2


def A176997_gen(startvalue=1):  # generator of terms
    if startvalue <= 1:
        yield 1
    k = 1 << (s := max(startvalue, 1)) - 1
    for n in count(s):
        if k % n == 1:
            yield n
        k <<= 1


def A355329_gen():  # generator of terms
    p = 2
    for m in count(6, 6):
        while q := (p - 1) % m:
            p = nextprime(p + m - q - 1)
        yield p
        p = nextprime(p)


def A007814(n):
    return (~n & n - 1).bit_length()


def A001511(n):
    return (~n & n - 1).bit_length() + 1


def A000404_gen(startvalue=1):  # generator of terms
    for n in count(max(startvalue, 1)):
        c = False
        for p in (f := factorint(n)):
            if (q := p & 3) == 3 and f[p] & 1:
                break
            elif q == 1:
                c = True
        else:
            if c or f.get(2, 0) & 1:
                yield n


def A355237(n):
    m = 2
    for k in count(2):
        c = False
        for p in (f := factorint(k)):
            if (q := p & 3) == 3 and f[p] & 1:
                break
            elif q == 1:
                c = True
        else:
            if c or f.get(2, 0) & 1:
                if k - m == n:
                    return m
                m = k


def A355238(n):
    m = 2
    for k in count(2):
        c = False
        for p in (f := factorint(k)):
            if (q := p & 3) == 3 and f[p] & 1:
                break
            elif q == 1:
                c = True
        else:
            if c or f.get(2, 0) & 1:
                if k - m == n:
                    return k
                m = k


def A346070(n):
    return (~n & n - 1).bit_length() & 3


def A007733(n):
    return n_order(2, n >> (~n & n - 1).bit_length())


def A336937(n):
    return (~(m := int(divisor_sigma(n))) & m - 1).bit_length()


def A336842(n):
    return (
        ~((m := prod(nextprime(p) ** e for p, e in factorint(n).items())) + 1) & m
    ).bit_length()


def A335021(n):
    return (
        0
        if n == 1
        else (1 - (m := (~n & n - 1).bit_length())) * divisor_count(n >> m)
        - ((n & 1) << 1)
    )


def A331739(n):
    return n - (n >> (~n & n - 1).bit_length())


def A331700(n):
    return reduce(xor, (d**2 for d in divisors(n, generator=True)))


def A330569(n):
    return 1 + (0 if n & 1 else 1 << (~n & n - 1).bit_length() - 1)


def A326714(n):
    return (n * (n - 1) >> 1) + (~n & n - 1).bit_length()


def A324902(n):
    return (~(m := n | int(divisor_sigma(n)) - n) & m - 1).bit_length()


def A318456(n):
    return n | divisor_sigma(n) - n


def A324904(n):
    return (~(m := n << 1 | int(divisor_sigma(n))) & m - 1).bit_length()


def A324468(n):
    return (
        (~n & n - 1).bit_length()
        + (~(n + 1) & n).bit_length()
        + (~(n + 2) & n + 1).bit_length()
    )


def A066194(n):
    k, m = n - 1, n - 1 >> 1
    while m > 0:
        k ^= m
        m >>= 1
    return k + 1


def A094290(n):
    return prime((~n & n - 1).bit_length() + 1)


def A087230(n):
    return (~(m := 6 * n + 4) & m - 1).bit_length()


def A115364(n):
    return (m := ((~n & n - 1).bit_length() + 1)) * (m + 1) >> 1


def A082903(n):
    return 1 << (~(m := int(divisor_sigma(n))) & m - 1).bit_length()


def A036554_gen(startvalue=1):
    return filter(lambda n: (~n & n - 1).bit_length() & 1, count(max(startvalue, 1)))


def A079523_gen(startvalue=1):
    return filter(lambda n: (~(n + 1) & n).bit_length() & 1, count(max(startvalue, 1)))


def A072939_gen(startvalue=2):
    return filter(
        lambda n: (~(n - 1) & (n - 2)).bit_length() & 1, count(max(startvalue, 2))
    )


def A037227(n):
    return ((~n & n - 1).bit_length() << 1) + 1


def A003973(n):
    return prod(
        ((q := nextprime(p)) ** (e + 1) - 1) // (q - 1) for p, e in factorint(n).items()
    )


def A336932(n):
    return (
        ~(
            m := prod(
                ((q := nextprime(p)) ** (e + 1) - 1) // (q - 1)
                for p, e in factorint(n).items()
            )
        )
        & m - 1
    ).bit_length()


def A295664(n):
    return (~(m := int(divisor_count(n))) & m - 1).bit_length()


def A336931(n):
    return (
        ~(
            m := prod(
                ((q := nextprime(p)) ** (e + 1) - 1) // (q - 1)
                for p, e in factorint(n).items()
            )
        )
        & m - 1
    ).bit_length() - (~(k := int(divisor_count(n))) & k - 1).bit_length()


def A336930_gen(startvalue=1):  # generator of terms
    return filter(
        lambda n: (
            ~(
                m := prod(
                    ((q := nextprime(p)) ** (e + 1) - 1) // (q - 1)
                    for p, e in factorint(n).items()
                )
            )
            & m - 1
        ).bit_length()
        == (~(k := int(divisor_count(n))) & k - 1).bit_length(),
        count(max(startvalue, 1)),
    )


def A038712(n):
    return n ^ (n - 1)


def A023534_gen(startvalue=1):  # generator of terms
    return filter(
        lambda n: (~n & n - 1).bit_length() == primenu(n), count(max(startvalue, 1))
    )


def A337985(n):
    return (n % 3 > 1) * (1 + ((n + 3) // 6 & 1))


def A309773(n):
    return (
        n >> 1
        if (m := (~n & n - 1).bit_length() + 1) == n.bit_length()
        else n + (1 << m)
    )


def A048855(n):
    return (
        factorial(n) * prod(Fraction(p - 1, p) for p in primerange(n + 1))
    ).numerator


def A055597(n):
    return (
        ~(
            m := (
                factorial(n) * prod(Fraction(p - 1, p) for p in primerange(n + 1))
            ).numerator
        )
        & m - 1
    ).bit_length()


def A055656(n):
    return (
        ~(
            m := (
                (f := factorial(n))
                * prod(Fraction(p - 1, p) for p in primerange(n + 1))
            ).numerator
        )
        & m - 1
    ).bit_length() - (~f & f - 1).bit_length()


def A122840(n):
    return len(s := str(n)) - len(s.rstrip("0"))


def A006519(n):
    return n & -n


def A135481(n):
    return ~(n + 1) & n


def A136013(n):
    return sum(
        map(
            lambda x: (x[0] + 1) * (1 << x[0]),
            filter(lambda x: x[1] == "1", enumerate(bin(n)[-2:1:-1])),
        )
    )


def A036987(n):
    return int(not (n & (n + 1)))


def A135560(n):
    return (m := (~n & n - 1)).bit_length() + int(m == n - 1) + 1


def A135561(n):
    return (1 << (m := (~n & n - 1)).bit_length() + int(m == n - 1) + 1) - 1


def A135534(n):
    return (
        1
        if n == 1
        else 0
        if n & 1
        else (1 << (m := (~(k := n >> 1) & k - 1)).bit_length() + int(m == k - 1) + 1)
        - 1
    )


def A135416(n):
    return int(not (n & (n + 1))) * (n + 1) >> 1


def A128311(n):
    return (pow(2, n - 1, n) - 1) % n


def A355058_gen():  # generator of terms
    return map(
        lambda n: n**2,
        filter(
            lambda n: prod((2 * e + 1) % 6 for e in factorint(n).values()) % 6 == 3,
            count(1),
        ),
    )


def A352798(n):
    return int(
        1
        / (
            continued_fraction_reduce([0] + [n] * n)
            - continued_fraction_reduce([0] + [n] * (n - 1))
        )
    )


def A127802(n):
    return 3 * int(not (n & (n + 1))) if n else 1


def A355418_gen():  # generator of terms
    p, q = 0, 2
    for i in count(0):
        s = set(str(i))
        yield from filter(lambda n: set(str(n)) == s, range(p, q))
        p, q = q, nextprime(q)


def A355317_gen():  # generator of terms
    p = 2
    for i in count(1):
        if int("".join(sorted(str(p)))) == int("".join(sorted(str(i)))):
            yield p
        p = nextprime(p)


def A355318_gen():  # generator of terms
    p = 2
    for i in count(1):
        if int("".join(sorted(str(p)))) == int("".join(sorted(str(i)))):
            yield i
        p = nextprime(p)


def A008619(n):
    return (n >> 1) + 1


def A004526(n):
    return n >> 1


def A002620(n):
    return (n**2) >> 2


def A023520(n):
    return (~(m := prime(n) * prime(n - 1) - 1) & m - 1).bit_length()


def A001223(n):
    return prime(n + 1) - prime(n)


def A080378(n):
    return (prime(n + 1) - prime(n)) & 3


def A023506(n):
    return (~(m := prime(n) - 1) & m - 1).bit_length()


def A025426(n):
    return (
        (
            m := prod(
                1 if p == 2 else (e + 1 if p & 3 == 1 else (e + 1) & 1)
                for p, e in factorint(n).items()
            )
        )
        + ((((~n & n - 1).bit_length() & 1) << 1) - 1 if m & 1 else 0)
    ) >> 1


def A005087(n):
    return len(primefactors(n)) + (n & 1) - 1


def A050603(n):
    return ((m := n >> 1) & ~(m + 1)).bit_length() + 1


def A355539_gen():  # generator of terms
    p, s, k = 2, set(), 0
    for i in count(1):
        if int(a := "".join(sorted(str(p)))) == int(b := "".join(sorted(str(i)))):
            k += 1
            if (q := (a.count("0"), b.count("0"))) not in s:
                yield k
                s.add(q)
        p = nextprime(p)


def A023528(n):
    return 0 if n == 1 else (~(m := prime(n) * prime(n - 1) + 1) & m - 1).bit_length()


def A023579(n):
    return (~(m := prime(n) + 3) & m - 1).bit_length()


def A086223(n):
    return (-(k := (m := (10**n - 1) // 9) & ~(m + 1)) + m + 1) // ((k + 1) << 1)


def A324466(n):
    return (~(m := factorial(3 * n) // factorial(n) ** 3) & m - 1).bit_length()


def A291982(n):
    return euler(n, n + 1) * (n + 1 & -n - 1)


def A291897(n):
    return euler((n << 1) - 1, n).p


def A259897(n):
    return (~(m := totient(comb(2 * n, n))) & m - 1).bit_length()


def A275019(n):
    return (~(m := n * (n + 1) * (n + 2) // 6) & m - 1).bit_length()


def A354782(n):
    return int(str(1 << n)[1])


def A008952(n):
    return int(str(1 << n)[0])


def A093049(n):
    return n - 1 - (~n & n - 1).bit_length() if n else 0


def A091311(n):
    return (int(bin(n)[2:], 3) << 1) - n


def A092525(n):
    return (n + 1) * (~n & n - 1) + n


def A093052(n):
    return n + (~(m := 3**n - 1) & m - 1).bit_length() if n else 0


def A093048(n):
    return n - (~n & n - 1).bit_length() if n else 0


def A100892(n):
    return ((~n & n - 1) << 2) + 2


def A119387(n):
    return (n + 1).bit_length() - (n + 1 & -n - 1).bit_length()


def A209229(n):
    return int(not (n & -n) ^ n) if n else 0


def A135523(n):
    return (~n & n - 1).bit_length() + int(not (n & -n) ^ n)


def A136480(n):
    return (~(m := n + (n & 1)) & m - 1).bit_length()


def A153733(n):
    return n >> (~(n + 1) & n).bit_length()


def A137780(n):
    return 1 + (1 << (prime(n + 1) - prime(n)))


def A177424(n):
    return (~(m := comb(n**2, n)) & m - 1).bit_length()


def A160467(n):
    return max(1, (n & -n) >> 1)


def A140670(n):
    return max(1, (n & -n) - 1)


def A186034_gen():  # generator of terms
    a, b = 1, 1
    yield from (0, 0)
    for n in count(2):
        a, b = b, (b * (2 * n + 1) + a * 3 * (n - 1)) // (n + 2)
        yield (~b & b - 1).bit_length()


def A186035_gen():  # generator of terms
    a, b = 1, 1
    yield from (1, 1)
    for n in count(2):
        a, b = b, (b * (2 * n + 1) + a * 3 * (n - 1)) // (n + 2)
        yield 1 - (((~b & b - 1).bit_length() & 1) << 1)


def A181741_gen():  # generator of terms
    m = 2
    for t in count(1):
        r = 1 << t - 1
        for k in range(t - 1, 0, -1):
            if isprime(s := m - r - 1):
                yield s
            r >>= 1
        m <<= 1


def A181743_gen():  # generator of terms
    m = 2
    for t in count(1):
        r = 1 << t - 1
        for k in range(t - 1, 0, -1):
            if isprime(m - r - 1):
                yield k
            r >>= 1
        m <<= 1


def A179504(n):
    return divisor_sigma(n << 1, n) if n else 1


def A201555(n):
    return comb((m := n**2) << 1, m)


def A007843(n):
    c = 0
    for k in count(1):
        c += (~k & k - 1).bit_length()
        if c >= n:
            return k


def A003602(n):
    return (n >> (n & -n).bit_length()) + 1


def A220779(n):
    return (~(m := int(harmonic(n, -n))) & m - 1).bit_length()


def A237881(n):
    return (~(m := prime(n) + prime(n + 1)) & m - 1).bit_length()


def A235062(n):
    return prod(
        map(lambda n: n >> (~n & n - 1).bit_length(), accumulate(range(1, n + 1), mul))
    )


def A234957(n):
    return 1 << ((~n & n - 1).bit_length() & -2)


def A235127(n):
    return (~n & n - 1).bit_length() >> 1


def A323921(n):
    return ((1 << ((~n & n - 1).bit_length() & -2) + 2) - 1) // 3


def A277549_gen(startvalue=1):  # generator of terms
    return filter(
        lambda n: (n >> ((~n & n - 1).bit_length() & -2)) & 3 == 1,
        count(max(startvalue, 1)),
    )


def A055039_gen(startvalue=1):  # generator of terms
    return filter(
        lambda n: (m := (~n & n - 1).bit_length()) & 1 and (n >> m) & 7 == 7,
        count(max(startvalue, 1)),
    )


def A004215_gen(startvalue=1):  # generator of terms
    return filter(
        lambda n: not (m := (~n & n - 1).bit_length()) & 1 and (n >> m) & 7 == 7,
        count(max(startvalue, 1)),
    )


def A272405_gen(startvalue=1):  # generator of terms
    return filter(
        lambda n: not (m := (~(s := int(divisor_sigma(n))) & s - 1).bit_length()) & 1
        and (s >> m) & 7 == 7,
        count(max(startvalue, 1)),
    )


def A234000_gen(startvalue=1):  # generator of terms
    return filter(
        lambda n: not (m := (~n & n - 1).bit_length()) & 1 and (n >> m) & 7 == 1,
        count(max(startvalue, 1)),
    )


def A055046_gen(startvalue=1):  # generator of terms
    return filter(
        lambda n: not (m := (~n & n - 1).bit_length()) & 1 and (n >> m) & 7 == 3,
        count(max(startvalue, 1)),
    )


def A055045_gen(startvalue=1):  # generator of terms
    return filter(
        lambda n: not (m := (~n & n - 1).bit_length()) & 1 and (n >> m) & 7 == 5,
        count(max(startvalue, 1)),
    )


def A131323_gen(startvalue=1):  # generator of terms
    return filter(
        lambda n: n & 1 and not (~(n + 1) & n).bit_length() & 1,
        count(max(startvalue, 1)),
    )


def A225822_gen(startvalue=1):  # generator of terms
    return map(
        lambda m: (m << 1) + 1,
        filter(
            lambda n: n & 1 and not (~(n + 1) & n).bit_length() & 1,
            count(max(startvalue, 1)),
        ),
    )


def A199398(n):
    return reduce(xor, range(1, n << 1, 2))


def A126084(n):
    return reduce(xor, primerange(2, prime(n) + 1)) if n else 0


if sys.version_info >= (3, 10):

    def A011371(n):
        return n - n.bit_count()

    def A090616(n):
        return (n - n.bit_count()) >> 1

    def A090617(n):
        return (n - n.bit_count()) // 3

    def A090621(n):
        return (n - n.bit_count()) >> 2

    def A324465(n):
        return (
            3 * n.bit_count()
            - (~(n + 1) & n).bit_length()
            - (~(n + 2) & n + 1).bit_length()
            - (~(n + 3) & n + 2).bit_length()
            if n
            else 0
        )

    def A064394_gen(startvalue=3):  # generator of terms
        return filter(
            lambda n: n - n.bit_count() == prevprime(n), count(max(startvalue, 3))
        )

    def A064503_gen():  # generator of terms
        return islice(
            filter(lambda n: n - n.bit_count() == prevprime(n), count(3)), 0, None, 2
        )

    def A084953_gen(startvalue=1):  # generator of terms
        return filter(
            lambda n: (factorial(n) >> ((n - n.bit_count()) & -2)) & 7 == 7,
            count(max(startvalue, 1)),
        )

else:

    def A011371(n):
        return n - bin(n).count("1")

    def A090616(n):
        return (n - bin(n).count("1")) >> 1

    def A090617(n):
        return (n - bin(n).count("1")) // 3

    def A090621(n):
        return (n - bin(n).count("1")) >> 2

    def A324465(n):
        return (
            3 * bin(n).count("1")
            - (~(n + 1) & n).bit_length()
            - (~(n + 2) & n + 1).bit_length()
            - (~(n + 3) & n + 2).bit_length()
            if n
            else 0
        )

    def A064394_gen(startvalue=3):  # generator of terms
        return filter(
            lambda n: n - bin(n).count("1") == prevprime(n), count(max(startvalue, 3))
        )

    def A064503_gen():  # generator of terms
        return islice(
            filter(lambda n: n - bin(n).count("1") == prevprime(n), count(3)),
            0,
            None,
            2,
        )

    def A084953_gen(startvalue=1):  # generator of terms
        return filter(
            lambda n: (factorial(n) >> ((n - bin(n).count("1")) & -2)) & 7 == 7,
            count(max(startvalue, 1)),
        )


def A065883(n):
    return n >> ((~n & n - 1).bit_length() & -2)


def A000534_gen(startvalue=0):  # generator of terms
    return filter(
        lambda n: n in {0, 1, 3, 5, 9, 11, 17, 29, 41}
        or n >> ((~n & n - 1).bit_length() & -2) in {2, 6, 14},
        count(max(startvalue, 0)),
    )


def A000414_gen(startvalue=0):  # generator of terms
    return filter(
        lambda n: not (
            n in {0, 1, 3, 5, 9, 11, 17, 29, 41}
            or n >> ((~n & n - 1).bit_length() & -2) in {2, 6, 14}
        ),
        count(max(startvalue, 0)),
    )


def A000378_gen(startvalue=0):  # generator of terms
    return filter(
        lambda n: (m := (~n & n - 1).bit_length()) & 1 or (n >> m) & 7 < 7,
        count(max(startvalue, 0)),
    )


def A244413(n):
    return (~n & n - 1).bit_length() // 3


def A010877(n):
    return n & 7


def A168181(n):
    return int(bool(n & 7))


def A053829(n):
    return sum(int(d) for d in oct(n)[2:])


def A054897(n):
    return (n - sum(int(d) for d in oct(n)[2:])) // 7


def A253513(n):
    return int(not (n & 7))


def A268355(n):
    return (m := (~n & n - 1)) + 1 >> (m.bit_length() % 3)


def A068504(n):
    return (m := prime(n) + 1) & -m


def A003484(n):
    return (((m := (~n & n - 1).bit_length()) & -4) << 1) + (1 << (m & 3))


def A101119(n):
    return (
        (1 << (m := (~n & n - 1).bit_length() + 4)) - ((m & -4) << 1) - (1 << (m & 3))
    )


def A101120(n):
    return (1 << (n + 3)) - (1 << ((n - 1) & 3)) - (((n + 3) & -4) << 1)


def A318466(n):
    return (n << 1) | int(divisor_sigma(n))


def A324906(n):
    return ((m := (n << 1) | int(divisor_sigma(n))) & ~(m + 1)).bit_length()


def A101121(n):
    return ((1 << (n + 2)) - (1 << ((n - 2) & 3)) - (((n + 2) & -4) << 1)) ^ (
        (1 << (n + 3)) - (1 << ((n - 1) & 3)) - (((n + 3) & -4) << 1)
    )


def A101122(n):
    return reduce(
        xor,
        (
            (
                (1 << (m := (~(k + 1) & k).bit_length() + 4))
                - ((m & -4) << 1)
                - (1 << (m & 3))
            )
            & -int(not k & ~(n - 1))
            for k in range(n)
        ),
    )


def A336066_gen(startvalue=2):  # generator of terms
    return filter(
        lambda n: n % (~n & n - 1).bit_length() == 0,
        count(max(startvalue + startvalue & 1, 2), 2),
    )


def A329486(n):
    return (3 * (n & -n) + n) >> 1
