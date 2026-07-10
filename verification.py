"""Independent sanity check: exact rational computation of a_n.

Verifies that a_n is a positive integer for n <= 26 (a_26 already has
~24,000 digits; the terms grow doubly exponentially, so exact computation
beyond n ~ 28 is impractical -- that is what the certified 2-adic argument
of the proof is for).
"""
from fractions import Fraction as Fr

a = [Fr(1)] * 4
for n in range(4, 27):
    a.append((a[-1] + 1) * (a[-2] + 1) * (a[-3] + 1) / a[-4])

assert all(x.denominator == 1 and x > 0 for x in a)
print("a_n is a positive integer for all n <= 26")
print("first terms:", [int(x) for x in a[:9]])
print("bits of a_26:", a[26].numerator.bit_length())
