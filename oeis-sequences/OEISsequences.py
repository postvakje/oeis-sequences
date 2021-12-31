# -*- coding: utf-8 -*-
"""
Created on Thu Dec  2 11:43:37 2021

@author: Chai Wah Wu

Python functions to generate The On-Line Encyclopedia of Integer Sequences (OEIS) sequences

Requires python >= 3.8

Installation: pip install OEISsequences

After installation, `import OEISsequences` will import all the functions accessible via `OEISsequences.Axxxxxx`.
Alternatively, invidividual functions can be imported as `from OEISsequences import Axxxxxx`.

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
    
Examples:
    
   from OEISsequences import A131546
   print(A131546(5))
   >> 721
  
   from itertools import islice
   from OEISsequences import A153695_gen
   print(list(islice(A153695_gen(),10)))
   >> [1, 2, 3, 4, 5, 6, 13, 17, 413, 555]
   
   from OEISsequences import A235811_gen 
   print(list(islice(A235811_gen(startvalue=1475),10)))
   >> [1475, 1484, 1531, 1706, 1721, 1733, 1818, 1844, 1895, 1903]

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
)
from fractions import Fraction
from collections import Counter
from math import factorial, floor, comb, prod, isqrt
from operator import mul, xor
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
    sin,
    cos,
    tan,
    fibonacci,
    lucas,
    pi,
    hyperexpand,
    expand,
    Poly,
)
from sympy.functions import hyper, partition
from sympy.ntheory import mobius, legendre_symbol
from sympy.ntheory.factor_ import (
    digits as sympydigits,
    udivisor_sigma,
    sieve,
    reduced_totient,
    core as numbercore,
    antidivisors,
    udivisors,
)
from sympy.combinatorics.partitions import IntegerPartition
from sympy.utilities.iterables import (
    partitions,
    multiset_permutations,
    multiset_combinations,
    multiset_partitions,
)
from sympy.functions.combinatorial.numbers import stirling, bell
from sympy.ntheory.continued_fraction import continued_fraction_periodic
from sympy.ntheory.modular import crt
from sympy.combinatorics.subsets import Subset
from sympy.abc import x as symbolx
from gmpy2 import (
    mpz,
    fac,
    popcount,
    is_prime,
    is_square,
    next_prime,
    c_divmod,
    lucas2,
    fib2,
    isqrt_rem,
    iroot_rem,
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
    return (s := sympydigits(n, b)[1:]) == s[::-1]


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
        for y in range(10 ** (x - 1), 10 ** x):
            s = str(y)
            yield int(s + s[-2::-1])
        for y in range(10 ** (x - 1), 10 ** x):
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
        for y in range(b ** (x - 1), b ** x):
            s = gmpy2digits(y, b)
            yield int(s + s[-2::-1])
        for y in range(b ** (x - 1), b ** x):
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
    while b ** kmax <= n:
        kmax *= 2
    while True:
        kmid = (kmax + kmin) // 2
        if b ** kmid > n:
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
        y = lunar_add(y, int("".join(min(j, c) for j in sn)) * 10 ** i)
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


def A348169_gen():  # generator of terms
    for n in count(1):
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
    return (abs(x + y) for x in A349544helper_(k - 1, n) for y in (2 ** n, -(2 ** n)))


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
    return filter(lambda n: set(str(n)) <= {"0", "1", "3"}, (n ** 3 for n in count(0)))


def A050251(n):
    return (
        4 * n if n <= 1 else 1 + sum(1 for i in pal_odd_gen((n + 1) // 2) if isprime(i))
    )


def A229629_gen():  # generator of terms
    n = 1
    while True:
        s, sn = str(n ** n), str(n)
        l, ln = len(s), len(sn)
        if (ln - l) % 2 == 0 and s[l // 2 - ln // 2 : l // 2 + (ln + 1) // 2] == sn:
            yield n
        n += 1


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


def A179993_gen():  # generator of terms
    for m in count(1):
        if all(
            isprime(m // a - a) for a in takewhile(lambda x: x * x <= m, divisors(m))
        ):
            yield m


def A349327_gen():  # generator of terms
    n = 2
    while True:
        if isprime(n ** 2 - 2) and isprime(2 * n ** 2 - 1):
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
    s, k = set(Matrix(n, n, p).det() for p in product([0, 1], repeat=n ** 2)), 1
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
    l, c, nmin, k = 9 * n, 0, 10 ** n - 1, 10 ** (n - 1)
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


def A348658_gen():  # generator of terms
    k = 1
    while True:
        a, b = divisor_sigma(k), divisor_sigma(k, 0) * k
        c = gcd(a, b)
        n1, n2 = 5 * (a // c) ** 2 - 4, 5 * (b // c) ** 2 - 4
        if (integer_nthroot(n1, 2)[1] or integer_nthroot(n1 + 8, 2)[1]) and (
            integer_nthroot(n2, 2)[1] or integer_nthroot(n2 + 8, 2)[1]
        ):
            yield k
        k += 1


def A108861_gen():  # generator of terms
    k2, kf = 1, 1
    for k in count(1):
        k2 *= 2
        kf *= k
        if not sum(int(d) for d in str(k2 * kf)) % k:
            yield k


def A244060(n):
    return sum(int(d) for d in str(factorial(2 ** n)))


def A008906(n):
    return len(str(factorial(n)).rstrip("0"))


def A301861(n):
    return sum(int(d) for d in str(factorial(factorial(n))))


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
    m, s = 10 ** n, set()
    for k in range(m):
        c, k2, kset = 0, k, set()
        while k2 not in kset:
            kset.add(k2)
            c += 1
            k2 = 2 * k2 % m
        s.add(c)
    return len(s)


def A348339(n):
    m, s = 10 ** n, set()
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


def A348428_gen():  # generator of terms
    for n in count(1):
        s = [int(d) for d in str(n)]
        m = len(s)
        if n == Matrix(m, m, lambda i, j: s[(i + j) % m]).det():
            yield n


def A306853_gen():  # generator of terms
    for n in count(1):
        s = [int(d) for d in str(n)]
        m = len(s)
        if n == Matrix(m, m, lambda i, j: s[(i - j) % m]).per():
            yield n


def A219325_gen():  # generator of terms
    for n in count(1):
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
        if m ** 2 != 24 * n + 1
        else ((-1) ** ((m - 1) // 6) if m % 6 == 1 else (-1) ** ((m + 1) // 6))
    )


if sys.version_info >= (3, 10):

    def A000120(n):
        return n.bit_count()

else:

    def A000120(n):
        return bin(n).count("1")


def A000110_gen():
    yield 1
    yield 1
    blist, b = [1], 1
    while True:
        blist = list(accumulate([b] + blist))
        b = blist[-1]
        yield b


@lru_cache(maxsize=None)
def A000009(n):
    return (
        1
        if n == 0
        else A010815(n)
        + 2 * sum((-1) ** (k + 1) * A000009(n - k ** 2) for k in range(1, isqrt(n) + 1))
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
    return n ** 3


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


def A001700_gen():  # generator of terms
    b = 1
    for n in count(0):
        yield b
        b = b * (4 * n + 6) // (n + 2)


def A003418(n):
    return prod(p ** integerlog(n, p) for p in sieve.primerange(1, n + 1))


def A000111_gen():  # generator of terms
    yield 1
    yield 1
    blist = [1]
    for n in count(0):
        blist = (
            list(reversed(list(accumulate(reversed(blist))))) + [0]
            if n % 2
            else [0] + list(accumulate(blist))
        )
        yield sum(blist)


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
    yield 1
    yield 2
    yield 3
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


if sys.version_info >= (3, 10):

    def A029837(n):
        return n.bit_length() - (1 if n.bit_count() == 1 else 0)

else:

    def A029837(n):
        return n.bit_length() - (1 if bin(n).count("1") == 1 else 0)


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
    b = primepi(n ** 2) + primepi((n + 1) ** 2) + 1
    return (prime(b // 2) + prime((b + 1) // 2)) // 2 if b % 2 else prime(b // 2)


def A000188(n):
    return isqrt(n // numbercore(n))


def A020449_gen():
    return filter(isprime, (int(format(n, "b")) for n in count(1)))


def A033676(n):
    d = divisors(n)
    return d[(len(d) - 1) // 2]


def A047994(n):
    return prod(p ** e - 1 for p, e in factorint(n).items())


def d(n, m):
    return not n % m


def A007678(n):
    return (
        1176 * d(n, 12) * n
        - 3744 * d(n, 120) * n
        + 1536 * d(n, 18) * n
        - d(n, 2) * (5 * n ** 3 - 42 * n ** 2 + 40 * n + 48)
        - 2304 * d(n, 210) * n
        + 912 * d(n, 24) * n
        - 1728 * d(n, 30) * n
        - 36 * d(n, 4) * n
        - 2400 * d(n, 42) * n
        - 4 * d(n, 6) * n * (53 * n - 310)
        - 9120 * d(n, 60) * n
        - 3744 * d(n, 84) * n
        - 2304 * d(n, 90) * n
        + 2 * n ** 4
        - 12 * n ** 3
        + 46 * n ** 2
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
    return isqrt(2 * n ** 2)


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
    return n ** 2 + sum(
        totient(i) * (n + 1 - i) * (2 * n + 2 - i) for i in range(2, n + 1)
    )


def A316524(n):
    fs = [primepi(p) for p in factorint(n, multiple=True)]
    return sum(fs[::2]) - sum(fs[1::2])


def A048050(n):
    return 0 if n == 1 else divisor_sigma(n) - n - 1


def A349806(n):
    for i in count(n ** 2 + (n % 2) + 1, 2):
        if len(fs := factorint(i)) == 2 == sum(fs.values()):
            return i - n ** 2


def A099610(n):
    for i in count(n ** 2 + (n % 2) + 1, 2):
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
        a = [i ** k for i in range(10)]
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
            3 * gcd(comb(n * (n * (n + 6) - 6) + 2, 6 * n * (n - 1) + 3), n ** 3)
            == n ** 3
        ):
            yield n


def A349509(n):
    return n ** 3 // gcd(comb(n * (n * (n + 6) - 6) + 2, 6 * n * (n - 1) + 3), n ** 3)


def A099611(n):
    for i in count(n ** 2 - (n % 2) - 1, -2):
        fs = factorint(i)
        if len(fs) == 2 == sum(fs.values()):
            return i


def A349809(n):
    for i in count(n ** 2 - (n % 2) - 1, -2):
        fs = factorint(i)
        if len(fs) == 2 == sum(fs.values()):
            return n ** 2 - i


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
                sieve.primerange(10 ** n, 10 ** (n + 1)), 2
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
        int((isqrt(5 * n ** 2) + n) // 2 - (isqrt(5 * (n - 4) ** 2) + n) // 2 - 4)
        if n > 3
        else 1 - (n % 2)
    )


def A348209(n):
    if n > 2 and bin(n).count("1") == 1:
        return 0
    k, m, n1, n2, n3 = 1, 2, n ** (n - 2), n ** (n - 1), n ** n
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
    return filter(lambda p: isprime((2 ** p + 1) // 3), (prime(n) for n in count(2)))


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
    return n * (n ** 2 * (n * (6 * n + 15) + 10) - 1) // 30


def A330151(n):
    return 8 * n * (n ** 2 * (n * (6 * n + 15) + 10) - 1) // 15


def A259317(n):
    return n * (n * (n ** 2 * (n * (16 * n + 48) + 40) - 11) - 3) // 45


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
    return accumulate((k ** k for k in count(0)), mul)


def A002109(n):
    return prod(k ** k for k in range(1, n + 1))


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
    yield from filter(lambda n: isprime(divisor_sigma(n)), (n ** 2 for n in count(1)))


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
    return 0 if n <= 1 else isqrt(n ** 3 - 1) - n


def A349993(n):
    return isqrt(n ** 3) - n + 1


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


def A308533_gen():  # generator of terms
    for n in count(3):
        a = antidivisors(n)
        if int("".join(str(s) for s in a)) % sum(a) == 0:
            yield n


def A130846(n):
    return int("".join(str(s) for s in antidivisors(n)))


def A003278(n):
    return int(format(n - 1, "b"), 3) + 1


def A000539(n):
    return n ** 2 * (n ** 2 * (n * (2 * n + 6) + 5) - 1) // 12


def A027868_gen():
    yield from [0] * 5
    p5 = 0
    for n in count(5, 5):
        p5 += multiplicity(5, n)
        yield from [p5] * 5


def A187950(n):
    return int((isqrt(5 * (n + 4) ** 2) + n) // 2 - (isqrt(5 * n ** 2) + n) // 2 - 4)


def A018900_gen():
    return (2 ** a + 2 ** b for a in count(1) for b in range(a))


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


def A007629_gen():  # generator of terms
    for n in count(10):
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
    return 2 * n + isqrt(2 * n ** 2)


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
        2 ** a + 2 ** b + 2 ** c
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
    return sum(Fraction(1, k ** 2) for k in range(1, n + 1)).denominator


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
        for i in range(1, 2 ** n):
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
            n ** 4
            - 6 * n ** 3
            + 11 * n ** 2
            + 18 * n
            - (not n % 2) * (5 * n ** 3 - 45 * n ** 2 + 70 * n - 24)
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


def A349775sumsetgen(n):  # generate sums of 2 subsets A,B with |A|,|B| >= 2 for A349775
    for l in range(2, n + 2):
        for a in combinations(range(n + 1), l):
            amax = max(a)
            bmax = min(amax, n - amax)
            for lb in range(2, bmax + 2):
                for b in combinations(range(bmax + 1), lb):
                    yield tuple(sorted(set(x + y for x in a for y in b)))


def A349775(n):
    c = Counter()
    for s in set(A349775sumsetgen(n)):
        c[len(s)] += 1
    for i in range(n + 1, 1, -1):
        if c[i] < comb(n + 1, i):
            return i


def A002779_gen():
    return filter(lambda n: str(n) == str(n)[::-1], (n ** 2 for n in count(0)))


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
            n ** 4
            - 6 * n ** 3
            + 11 * n ** 2
            - 6 * n
            - (not n % 2) * (5 * n ** 3 - 45 * n ** 2 + 70 * n - 24)
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
        lambda p: all((isprime(2 ** m * (p + 1) - 1) for m in range(1, 6))),
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
            Fraction(b * d * (c - b) * (d - c), e ** 2),
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
    return str(2 ** n).count("0")


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
    return int(str(2 ** n)[::-1])


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
    return n * (n ** 2 * (n ** 2 * (n * (6 * n + 21) + 21) - 7) + 1) // 42


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
    k, r, m = (10 ** n - 1) // 9, 2 ** n - 1, 0
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


def A233466_gen():
    return filter(lambda n: 2 * totient(n) == n - 5, count(1, 2))


def A078971_gen():  # generator of terms
    for t in count(0):
        yield (2 ** (2 * t) - 1) // 3
        yield from ((2 ** (2 * t + 1) + 2 ** (2 * j + 1) - 1) // 3 for j in range(t))


def A048054(n):
    return len(
        [p for p in primerange(10 ** (n - 1), 10 ** n) if isprime(int(str(p)[::-1]))]
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
    l, k = n - 1, 2 ** n
    while True:
        for d in combinations(range(l - 1, -1, -1), l - n + 1):
            m = k - 1 - sum(2 ** (e) for e in d)
            if isprime(m):
                return m
        l += 1
        k *= 2


def A106737(n):
    return sum(int(not (~(n + k) & (n - k)) | (~n & k)) for k in range(n + 1))


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
                        s2 = set(str(n ** 2))
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


def A065197_gen():
    return filter(
        lambda n: n
        == reduce(lambda m, k: m + (k if (m // k) % 2 else -k), range(n, 1, -1), n),
        count(1),
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
            for p in primerange(10 ** (n - 1), 10 ** n)
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
    return n * (n ** 2 - 1) - c + j


def A078241(n):
    if n > 0:
        for i in range(1, 2 ** n):
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


def A031423_gen():  # generator of terms
    for n in count(1):
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
        4 * n ** 2
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
    return n ** 2 * (n ** 2 * (n ** 2 * (n * (3 * n + 12) + 14) - 7) + 2) // 24


def A001287(n):
    return comb(n, 10)


def A022842(n):
    return isqrt(8 * n ** 2)


def A031286(n):
    ap = 0
    while n > 9:
        n = sum(int(d) for d in str(n))
        ap += 1
    return ap


def A055165(n):
    return sum(1 for s in product([0, 1], repeat=n ** 2) if Matrix(n, n, s).det() != 0)


def A145768(n):
    return reduce(xor, (x ** 2 for x in range(n + 1)))


def A145829_gen():  # generator of terms
    m = 0
    for n in count(1):
        m ^= n ** 2
        a, b = integer_nthroot(m, 2)
        if b:
            yield a


def A249155_gen():
    return filter(lambda n: is_pal(n, 15), pal_gen(6))


def A145828_gen():  # generator of terms
    m = 0
    for n in count(0):
        m ^= n ** 2
        if isqrt(m) ** 2 == m:
            yield m


def A193232(n):
    return reduce(xor, (x * (x + 1) for x in range(n + 1))) // 2


def A062700_gen():  # generator of terms
    yield 3
    yield from filter(isprime, (divisor_sigma(d ** 2) for d in count(1)))


def A065710(n):
    return str(2 ** n).count("2")


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
        lambda m: str(m) == str(m)[::-1], (n * (n + 1) // 2 for n in range(10 ** 5))
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
        - (not n % 2) * (5 * n ** 3 - 42 * n ** 2 + 40 * n + 48)
        - 2304 * (not n % 210) * n
        + 912 * (not n % 24) * n
        - 1728 * (not n % 30) * n
        - 36 * (not n % 4) * n
        - 2400 * (not n % 42) * n
        - 4 * (not n % 6) * n * (53 * n - 310)
        - 9120 * (not n % 60) * n
        - 3744 * (not n % 84) * n
        - 2304 * (not n % 90) * n
        + 2 * n ** 4
        - 12 * n ** 3
        + 46 * n ** 2
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


def A037015_gen():  # generator of terms
    for n in count(0):
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
    return sum(ord(d) - 96 for d in sub("\sand\s|[^a-z]", "", num2words(n)))


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
    return nextprime((10 ** n - 1) // 9)


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
        p ** e if p == 2 else (p ** (e + 1) - 1) // (p - 1)
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
        n, blist = 2 ** g - 1, []
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
    m, n1, n2 = n, 10 ** n, 10 ** (n - 1)
    while (k := pow(n, m, n1)) != m:
        m = k
    return k // n2


def A309081(n):
    return n + sum((1 if k % 2 else -1) * (n // k ** 2) for k in range(2, isqrt(n) + 1))


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
        * (n ** 2 * (n ** 2 * (n ** 2 * (n * (10 * n + 45) + 60) - 42) + 20) - 3)
        // 90
    )


def A002796_gen(startvalue=1):
    return filter(
        lambda n: all((d == "0" or n % int(d) == 0) for d in set(str(n))),
        count(max(startvalue, 1)),
    )


def A004167(n):
    return int(str(3 ** n)[::-1])


def A014312_gen():
    return (
        2 ** a + 2 ** b + 2 ** c + 2 ** d
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
    return 1 if n <= 1 else reduce(mul, [p ** (e % 3) for p, e in factorint(n).items()])


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
    return n * (n ** 3 - 1) - c + j


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
    return (n * (n ** 2 - 1) - c + j) // 6


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
    return int("".join(sorted(str(2 ** n))))


def A028910(n):
    return int("".join(sorted(str(2 ** n), reverse=True)))


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
    return str(2 ** n).count("1")


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
    return (Fraction(2 ** n) / n).numerator


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
        a, b = 1, 1 + a ** 2
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
    return min(factorint(2 ** n - 1))


def A061040(n):
    return 9 * n ** 2 // gcd(n ** 2 - 9, 9 * n ** 2)


def A064614(n):
    return (
        prod((5 - p if 2 <= p <= 3 else p) ** e for p, e in factorint(n).items())
        if n > 1
        else n
    )


def A065715(n):
    return str(2 ** n).count("4")


def A065719(n):
    return str(2 ** n).count("8")


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


def A237600_gen():  # generator of terms
    n = 2
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
        l, L, dm, xlist, q = 1, 1, [d ** m for d in range(10)], [0], 9 ** m
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
        else 8 * n ** 2
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
    return int((n ** 2 * sin(n)).round())


def A274088(n):
    return int((n ** 2 * sin(sqrt(n))).round())


def A274090(n):
    return int((n ** 2 * cos(sqrt(n))).round())


def A274091(n):
    k, j = divmod(n, 2)
    return int((k ** 2 * sin(sqrt(k) + j * pi / 2)).round())


def A274092(n):
    k, j = divmod(n, 3)
    return int((k ** 2 * sin(sqrt(k) + j * pi / 2)).round())


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
    k, n1, n2, pset = 0, 10 ** (n - 1) // 2 - 18, 10 ** n // 2 - 18, set()
    while 50 * k ** 2 + 60 * k < n2:
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
        n ** 2 * u
        for u, v, w in (igcdex(x, y) for x in range(1, n + 1) for y in range(1, n + 1))
    )


def A003512(n):
    return 2 * n + int(isqrt(3 * n ** 2))


def A004720(n):
    l = len(str(n - 1))
    m = (10 ** l - 1) // 9
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
        n ** 2
        * (n ** 2 * (n ** 2 * (n ** 2 * (n * (2 * n + 10) + 15) - 14) + 10) - 3)
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
        (n ** 2 for n in count(0)),
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
        lambda i: i % 10 and max(str(i ** 2)) < "3", count(max(startvalue, 0))
    )


def A064834(n):
    x, y = str(n), 0
    lx2, r = divmod(len(x), 2)
    for a, b in zip(x[:lx2], x[: lx2 + r - 1 : -1]):
        y += abs(int(a) - int(b))
    return y


def A065714(n):
    return str(2 ** n).count("3")


def A065716(n):
    return str(2 ** n).count("5")


def A065717(n):
    return str(2 ** n).count("6")


def A065718(n):
    return str(2 ** n).count("7")


def A065744(n):
    return str(2 ** n).count("9")


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
        lambda n: len(set(str(n)) & set(str(n ** 4))) == 0, count(max(startvalue, 1))
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
    return filter(lambda n: len(set(str(n ** 3))) == 9, count(max(startvalue, 0)))


def A235809_gen(startvalue=0):
    return filter(lambda n: len(set(str(n ** 3))) == 7, count(max(startvalue, 0)))


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


def A177029_gen():  # generator of terms
    for m in count(1):
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
    c, b, b2, n10 = 0, 1, 2, 10 ** n
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
    return sum(totient(d) * d ** n for d in divisors(n, generator=True))


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

    f, g, blist = 1 / x ** 2 + 1 / x + 1 + x + x ** 2, 1, [1]
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

    f, g, blist, c = 1 / x ** 2 + 1 / x + 1 + x + x ** 2, 1, [1], 1
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
            if isprime((10 ** n - 1) // 3 + d * 10 ** i)
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
            if isprime(7 * (10 ** n - 1) // 9 + d * 10 ** i)
        )
    )


def A266148(n):
    return sum(
        1 for d in range(-9, 1) for i in range(n) if isprime(10 ** n - 1 + d * 10 ** i)
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
        n ** 2 * v
        for u, v, w in (igcdex(x, y) for x in range(1, n + 1) for y in range(1, n + 1))
    )


def A004721(n):
    l = len(str(n))
    m = 2 * (10 ** l - 1) // 9
    k = n + l - int(n + l < m)
    return 1 if k == m else int(str(k).replace("2", ""))


def A004722(n):
    l = len(str(n))
    m = (10 ** l - 1) // 3
    k = n + l - int(n + l < m)
    return 2 if k == m else int(str(k).replace("3", ""))


def A004724(n):
    l = len(str(n))
    m = 5 * (10 ** l - 1) // 9
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
        p = prevprime((n3 := n ** 3) // 2)
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
    return min(n - a ** 3, (a + 1) ** 3 - n)


def A082491_gen():  # generator of terms
    m, x = 1, 1
    for n in count(0):
        x, m = x * n ** 2 + m, -(n + 1) * m
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


def A094519_gen():  # generator of terms
    for n in count(1):
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
            for n in range(a, isqrt(10 ** l - 1) + 1):
                for g in fs:
                    if not is_square(
                        sum(int(str(n ** 2)[h : h + g]) for h in range(0, l, g))
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
    return int(isqrt(3 * n ** 2) - isqrt(3 * (n - 1) ** 2)) - 1


def A201053(n):
    return (
        a ** 3
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


def A219327_gen():  # generator of terms
    for n in count(1):
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
                    if {"2", "6"} <= set(str(n ** 2)) <= {"2", "3", "4", "5", "6"}:
                        yield n


def A287055_gen():  # generator of terms
    a = 1
    for n in count(1):
        b = prod(p ** e - 1 for p, e in factorint(n + 1).items())
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
        n ** 2 * abs(u)
        for u, v, w in (igcdex(x, y) for x in range(1, n + 1) for y in range(1, n + 1))
    )


def A003221_gen():  # generator terms
    m, x = -1, 0
    for n in count(0):
        x, m = x * n + m * (n * (n - 1) // 2 - 1), -m
        yield x


def A004723(n):
    l = len(str(n))
    m = 4 * (10 ** l - 1) // 9
    k = n + l - int(n + l < m)
    return 3 if k == m else int(str(k).replace("4", ""))


def A004725(n):
    l = len(str(n))
    m = 2 * (10 ** l - 1) // 3
    k = n + l - int(n + l < m)
    return 5 if k == m else int(str(k).replace("6", ""))


def A004726(n):
    l = len(str(n))
    m = 7 * (10 ** l - 1) // 9
    k = n + l - int(n + l < m)
    return 6 if k == m else int(str(k).replace("7", ""))


def A004727(n):
    l = len(str(n))
    m = 8 * (10 ** l - 1) // 9
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
    while 3 ** kmax <= n:
        kmax *= 2
    while True:
        kmid = (kmax + kmin) // 2
        if 3 ** kmid > n:
            kmax = kmid
        else:
            kmin = kmid
        if kmax - kmin <= 1:
            break
    return min(n - 3 ** kmin, 3 * 3 ** kmin - n)


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
    return n * (n ** 4 - 1) - c + j


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
        x = i * (10 ** n - 1) // 9
        for j in range(n - 1, -1, -1):
            for k in range(i, -1, -1):
                if j < n - 1 or k < i:
                    y = x - k * (10 ** j)
                    if isprime(y):
                        return y
        for j in range(n):
            for k in range(1, 9 - i + 1):
                y = x + k * (10 ** j)
                if isprime(y):
                    return y


def A266141(n):
    return 4 if n == 1 else sum(1 for d in "1379" if isprime(int("2" * (n - 1) + d)))


def A266144(n):
    return (
        4
        if n == 1
        else sum(1 for d in [-4, -2, 2, 4] if isprime(5 * (10 ** n - 1) // 9 + d))
    )


def A266145(n):
    return (
        4
        if n == 1
        else sum(1 for d in [-5, -3, 1, 3] if isprime(2 * (10 ** n - 1) // 3 + d))
    )


def A266147(n):
    return (
        4
        if n == 1
        else sum(1 for d in [-7, -5, -1, 1] if isprime(8 * (10 ** n - 1) // 9 + d))
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
    for i in range(2 ** k):
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
        2 * n ** 2
        - n
        + 1
        + 2
        * sum(totient(i) * (n + 1 - 2 * i) * (n + 1 - i) for i in range(2, n // 2 + 1))
    )


def A342632(n):
    return 2 * sum(t for t in sieve.totientrange(1, 2 ** n + 1)) - 1


@lru_cache(maxsize=None)
def A343978(n):
    if n == 0:
        return 0
    c, j, k1 = 1, 2, n // 2
    while k1 > 1:
        j2 = n // k1 + 1
        c += (j2 - j) * A343978(k1)
        j, k1 = j2, n // j2
    return n * (n ** 5 - 1) - c + j


def A344866(n):
    return n * (n * (n * (2 * n - 11) + 23) - 21) + 7


def A345690(n):
    return pvariance(
        n ** 2 * abs(v)
        for u, v, w in (igcdex(x, y) for x in range(1, n + 1) for y in range(1, n + 1))
    )


def A004728(n):
    l = len(str(n))
    m = 10 ** l - 1
    k = n + l - int(n + l < m)
    return 8 if k == m else int(str(k).replace("9", ""))


def A014957_gen(startvalue=1):
    return filter(lambda n: n == 1 or pow(16, n, n) == 1, count(max(startvalue, 1)))


def A023002(n):
    return (
        n
        * (
            n ** 2
            * (n ** 2 * (n ** 2 * (n ** 2 * (n * (6 * n + 33) + 55) - 66) + 66) - 33)
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
    return 24 * 24 ** n + 64 * 2 ** (4 * n) - 81 * 18 ** n - 6 * 12 ** n


def A029455_gen():  # generator of terms
    r = 0
    for n in count(1):
        r = r * 10 ** len(str(n)) + n
        if not (r % n):
            yield n


def A052045_gen():
    return filter(lambda n: not str(n).count("0"), (n ** 3 for n in count(1)))


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
    n2 = n ** 2
    a = integer_nthroot(n2, 3)[0]
    a2, a3 = a ** 3, (a + 1) ** 3
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


def A210503_gen():  # generator of terms
    for n in count(2):
        nd = sum(n * e // p for p, e in factorint(n).items())
        if is_square(nd ** 2 + n ** 2) and gcd(n, nd, isqrt(nd ** 2 + n ** 2)) == 1:
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
                    if {"3", "7"} <= set(str(n ** 2)) <= {"3", "4", "5", "6", "7"}:
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
        for s in filter(lambda s: max(s) < "9", (str(i ** 2) for i in count(0)))
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
    plist = [p ** q for p, q in factorint(2 * n).items()]
    if len(plist) == 1:
        return n - 1 if plist[0] % 2 else 2 * n - 1
    return min(
        min(crt([m, 2 * n // m], [0, -1])[0], crt([2 * n // m, m], [0, -1])[0])
        for m in (
            prod(d)
            for l in range(1, len(plist) // 2 + 1)
            for d in combinations(plist, l)
        )
    )


def A344590(n):
    m = A011772(n)
    return sum(1 for d in divisors(n) if A011772(d) == m)


def A345691(n):
    return pvariance(
        n ** 2 * (u ** 2 + v ** 2)
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
    return filter(lambda n: len(set(str(n ** 3))) <= 2, count(max(startvalue, 0)))


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
    return integer_nthroot(3 * n ** 3, 3)[0]


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
        lambda i: prevprime(i ** 3 // 2) + nextprime(i ** 3 // 2) == i ** 3,
        count(max(startvalue + startvalue % 2, 2), 2),
    )


def A088104(n):
    return nextprime((p := prime(n)) * 10 ** (n - len(str(p))) - 1)


def A090693_gen():
    return (
        i
        for i, n in filter(
            lambda x: x[0] > 0 and isprime(x[1] + 2),
            enumerate(accumulate(range(10 ** 5), lambda x, y: x + 2 * y - 3)),
        )
    )


def A091938(n):
    for i in range(n, -1, -1):
        q = 2 ** n
        for d in multiset_permutations("0" * (n - i) + "1" * i):
            p = q + int("".join(d), 2)
            if isprime(p):
                return p


def A099906(n):
    return comb(2 * n - 1, n - 1) % (n ** 2)


def A099908(n):
    return comb(2 * n - 1, n - 1) % (n ** 4)


@lru_cache(maxsize=None)
def A100613(n):  # based on second formula in A018805
    if n == 0:
        return 0
    c, j = 1, 2
    k1 = n // j
    while k1 > 1:
        j2 = n // k1 + 1
        c += (j2 - j) * (k1 ** 2 - A100613(k1))
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
        if not b % (n ** 2):
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
        x = i * (10 ** n - 1) // 9
        for j in range(n - 1, -1, -1):
            for k in range(9 - i, -1, -1):
                y = x + k * (10 ** j)
                if isprime(y):
                    return y
        for j in range(n):
            for k in range(1, i + 1):
                if j < n - 1 or k < i:
                    y = x - k * (10 ** j)
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
        for d in filter(lambda d: max(d) < "3", (str(i ** 2) for i in count(0)))
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
    return filter(lambda k: min(str(k ** 2)) == "1", count(max(startvalue, 1)))


def A291630_gen(startvalue=1):
    return filter(lambda k: min(str(k ** 2)) == "5", count(max(startvalue, 1)))


def A291644_gen(startvalue=1):
    return filter(lambda k: min(str(k ** 3)) == "5", count(max(startvalue, 1)))


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
        u ** 2 + v ** 2
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
            u = prod(p ** e - 1 for p, e in factorint(d).items())
            if u in pset:
                break
            pset.add(u)
        else:
            yield n


def A001962(n):
    return 3 * n + isqrt(5 * n ** 2)


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
    y, x, n2 = n * (n + 2), 2 * n + 3, n ** 2
    m, r = divmod(y, n2)
    while r:
        y += x
        x += 2
        m, r = divmod(y, n2)
    return m


def A071220_gen():  # generator of terms
    for i in count(2):
        n = i ** 3
        m = n // 2
        if not isprime(m) and prevprime(m) + nextprime(m) == n:
            yield primepi(m)


def A071295(n):
    return bin(n)[1:].count("0") * bin(n).count("1")


def A078567(n):
    return (
        (m := isqrt(n - 1)) ** 2 * (1 + m) ** 2 // 4
        - m ** 2 * n
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
        isqrt(2 ** n), 2 ** n
    )


def A088754(n):
    p = prime(n)
    m = n - len(str(p))
    return primepi((p + 1) * 10 ** m) - primepi(p * 10 ** m)


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
            if not i in b and i & l1:
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
                x = sum(d ** d for d in n)
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
        return (n ** 3).bit_count()

else:

    def A192085(n):
        return bin(n ** 3).count("1")


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
            not (isprime(b ** 2 - 1) and isprime(b ** 2 + 1))
            and (min(factorint(b ** 2 + 1)) > min(factorint(b ** 2 - 1)) >= b - 1)
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
        for s in (str(i ** 2) for i in count(0))
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
        for n in (int(gmpy2digits(m, 3), 6) for m in range(10 ** 6))
        if max(gmpy2digits(n, 5)) <= "2" and max(gmpy2digits(n, 4)) <= "2"
    )


def A276854(n):
    return n + isqrt(5 * n ** 2)


def A289676(n):
    c, k, r, n2, cs, ts = (
        0,
        1 + (n - 1) // 3,
        2 ** ((n - 1) % 3),
        2 ** (n - 1),
        set(),
        set(),
    )
    for i in range(2 ** k):
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
    return (k for k in count(max(startvalue, 1)) if "0" in str(k ** 2))


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
    return A304176_helper(n ** 3 - n, n)


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
        n2 = n ** 2
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
        lambda n: len(s := set(str(n ** 2))) == 2
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
    m, tlist, s = 10 ** n, [1, 2], 0
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
    i, j = isqrt_rem(n ** 3 if n % 2 else n)
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
        x = int(str((n + 1) ** 2) + str(n ** 2))
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
    return filter(lambda n: len(set(str(n ** 4))) == 4, count(max(startvalue, 1)))


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
    p, k, m = 2, 73 ** n, 10
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
    return isqrt(5 * n ** 2) - isqrt(5 * (n - 1) ** 2) - 2


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
    l = len(str(3 ** n)) - 1
    l10, result = 10 ** l, 2 * 10 ** l
    while result >= 2 * l10:
        l += 1
        l102, result = l10, 20 * l10
        l10 *= 10
        q, qn = 2, 2 ** n
        while qn <= l10:
            s, sn = 2, 2 ** n
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
                sn = s ** n
            q = nextprime(q)
            qn = q ** n
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
        if not prod(int(d) for d in str(n ** 2) if d != "0") % n
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
    return filter(lambda n: len(set(str(n ** 3))) == 5, count(max(startvalue, 0)))


def A236437_gen():
    return (p for n in range(1, 10 ** 6) if A236174(n) == (p := prime(n)))


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
        y = 2 ** l - 1
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
            divisors(n, generator=False),
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
    return int(str((n + 1) ** 2) + str(n ** 2))


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
    for i in range(2 ** n):
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
        if set(str(n)) & set(str(n ** 4)) == set() and isprime(n)
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
        int("".join(format(x, "02d") for x in sympydigits(3 ** i, 60)[1:]))
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
        if not "0" in str(n) and set(str(n)) == set(str(n ** 2))
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
    return ((n ** 2 + 5) // 3 for n in count(0) if not (n ** 2 + 5) % 3)


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
            if x ** 2 < nd + d:
                return int(x)
            d *= 2
            nd *= 2


def A276466(n):
    return sum(Fraction(d, 10 ** len(str(d))) for d in divisors(n)).numerator


def A277561(n):
    return sum(int(not (~(n + 2 * k) & 2 * k) | (~n & k)) for k in range(n + 1))


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
    return (k for k in count(max(startvalue, 1)) if min(str(k ** 4)) == "4")


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
        m = b ** 2 + n ** 2
        b = (isqrt(m) + 1) ** 2 - m


def A347754_gen():  # generator of terms
    a = 1
    for n in count(1):
        m = a ** 2 + n ** 2
        k = isqrt(m) + 1
        a = k ** 2 - m
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
        ff(n, n - k) * expand(ff(symbolx, k)).coeff(symbolx ** 2)
        for k in range(2, n + 1)
    )


def A348064(n):
    return sum(
        ff(n, n - k) * expand(ff(symbolx, k)).coeff(symbolx ** 3)
        for k in range(3, n + 1)
    )


def A348065(n):
    return sum(
        ff(n, n - k) * expand(ff(symbolx, k)).coeff(symbolx ** 4)
        for k in range(4, n + 1)
    )


def A348068(n):
    return sum(
        ff(n, n - k) * expand(ff(symbolx, k)).coeff(symbolx ** 5)
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
    d, nd = 10, 10 * n ** 2
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
    d = divisors((10 ** n - 1) // 9)
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
        for i in range(10 ** (l - 1), 10 ** l):
            if i % 10:
                p = int(str(i ** 3)[::-1])
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
            x = sum(int(d) for d in str(m ** n))
            if x > 1 and not any(map(lambda x: x % n, factorint(x).values())):
                return m
            m += 1


def A071268(n):
    s = "".join(str(i) for i in range(1, n + 1))
    return (
        sum(int(d) for d in s)
        * factorial(len(s) - 1)
        * (10 ** len(s) - 1)
        // (9 * reduce(mul, (factorial(d) for d in (s.count(w) for w in set(s)))))
    )


def A070306_gen(startvalue=3):  # generator of terms
    for i in count(max(startvalue, 3)):
        n = i ** 3
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
        for i in range(1, 2 ** n):
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
    return filter(isprime, (int(str(n ** 2) + str((n + 1) ** 2)) for n in count(1)))


def A104265(n):
    m, a = integer_nthroot((10 ** n - 1) // 9, 2)
    if not a:
        m += 1
    k = m ** 2
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
            n ** 2
            * (
                n ** 2
                * (
                    n ** 2
                    * (n ** 2 * (n ** 2 * (n * (210 * n + 1365) + 2730) - 5005) + 8580)
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
        n ** 2
        * (
            n ** 2
            * (n ** 2 * (n ** 2 * (n ** 2 * (n * (2 * n + 12) + 22) - 33) + 44) - 33)
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
        n ** 2
        * (
            n ** 2
            * (
                n ** 2
                * (
                    n ** 2
                    * (n ** 2 * (n ** 2 * (n * (30 * n + 210) + 455) - 1001) + 2145)
                    - 3003
                )
                + 2275
            )
            - 691
        )
        // 420
    )


def A187338(n):
    return 3 * n + isqrt(2 * n ** 2)


def A187393(n):
    return 4 * n + isqrt(8 * n ** 2)


def A187946(n):
    return int(
        (isqrt(5 * (n + 5) ** 2) + n + 1) // 2 - (isqrt(5 * n ** 2) + n) // 2 - 6
    )


def A188374(n):
    return int(isqrt((n + 2) ** 2 // 2) - isqrt(n ** 2 // 2)) - 1


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
        x ** 4
        + 4 * x ** 3 * y
        + 4 * x ** 3 * z
        + 4 * x ** 2 * y ** 2
        + 8 * x ** 2 * y * z
        + 4 * x ** 2 * z ** 2
        + y ** 4
        + 6 * y ** 2 * z ** 2
        + z ** 4
    )


def A211034(n):
    x, y, z = n // 3 + 1, (n - 1) // 3 + 1, (n - 2) // 3 + 1
    return (
        x ** 2 * y ** 2
        + 2 * x ** 2 * y * z
        + x ** 2 * z ** 2
        + 2 * x * y ** 3
        + 6 * x * y ** 2 * z
        + 6 * x * y * z ** 2
        + 2 * x * z ** 3
        + 2 * y ** 3 * z
        + 2 * y * z ** 3
    )


def A211158(n):
    return n * (n + 1) * (3 * n + 1 + 3 * n ** 2 - (-1) ** n * (2 * n + 1))


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
    t = 2 * n ** 2
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
            for n in (d ** 2 for d in range(1, 10 ** 4))
            if isprime(divisor_sigma(n)) and isprime(divisor_sigma(n ** 2))
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
            s = str(n ** q * (isqrt(n) if r else 1))
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
        for p in (prime(n) for n in range(1, 10 ** 5))
        if all(isprime(4 + p ** z) for z in (1, 2, 3, 5))
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
        p2, x = p ** 2, 1
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
        for i in range(1, 2 ** n):
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
            n = sum(d ** m for d in c)
            r = sum(int(q) ** m for q in str(n))
            rlist = sorted(int(d) for d in str(r))
            rlist = [0] * (m + 1 - len(rlist)) + rlist
            if n < r and rlist == list(c):
                yield n


def A262092_gen():  # generator of terms
    for m in count(2):
        for c in combinations_with_replacement(range(10), m + 1):
            n = sum(d ** m for d in c)
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
        for d in (str(i ** 2) for i in count(1))
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
    return 1 + isqrt(5 * n ** 2) - isqrt(5 * (n - 1) ** 2)


def A278161(n):
    return sum(int(not (~(n + 3 * k) & 6 * k) | (~n & k)) for k in range(n + 1))


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
    return comb(2 * c - 1, c - 1) % c ** 4


def A301278(n):
    return (
        (Fraction(int(comb(2 * n, n))) / n - Fraction(4 ** n) / (n * (n + 1))).numerator
        if n > 0
        else 0
    )


def A301279(n):
    return (
        (
            Fraction(int(comb(2 * n, n))) / n - Fraction(4 ** n) / (n * (n + 1))
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
    t = 10 ** l
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
            m //= 2 ** c
            r = max(r, c)
    return r


def A347607(n):
    return partition(n ** n)


def A007356_gen(startvalue=0):
    return (k for k in count(max(startvalue, 0)) if "666" in str(2 ** k))


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
    i, j = iroot_rem(10 ** n, 5)
    return int(i) + int(32 * j >= 10 * i * (4 * i * (2 * i * (i + 1) + 1) + 1) + 1)


def A023969(n):
    i, j = isqrt_rem(n)
    return int(4 * (j - i) >= 1)


def A027603(n):
    return n * (n * (4 * n + 18) + 42) + 36
