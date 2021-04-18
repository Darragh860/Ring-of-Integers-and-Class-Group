#!/usr/bin/env sage -python
import sys
from sage.all import *

import math
import numpy as np
import sympy
import random
import cmath

# K.<x> = NumberField(x**2 + 5)
print("Run: ", random.randint(0, 100))

Qx = QQ['x']
# P = Qx([1791, 585, 24, 0, 1])
# P = Qx([-82, 0, 1]) # Z4
# P = Qx([-6, -9, 0, 1]) # trivial
# P = Qx([-1, 14, 0, 1]) # Z2 x Z4
# P = Qx([-22, 1, -1, 1]) # Z2 x Z4
# P = Qx([-30, 26, -1, 1]) # Z2 x Z4
# P = Qx([-65, 0, 0, 1]) # didn't work with final alg!
# P = Qx([90, 0, 61, 0, 8, 0, 1]) # didn't work with final alg!
# P = Qx([1444, 0, 73, 0, 1]) # Z7 x Z14 # also didn't work with final alg!
# P = Qx([390, 0, 1, -2, 1]) # Z2 x Z4 x Z8
# P = Qx([7569, 0, 134, 0, 1]) # Z2 x Z8 x Z16 -- worked after 5-10 minutes!!!
# P = Qx([1001, 0, 1])
# P = Qx([-182, 0, 0, 1]) # doesn't work (yet)
P = Qx([5, 0, 1])


# Implementation of Algorithm 6.5.7 of [2]
# for the regulator R and the fundamental unit matrix F

def real(x): return x.real()


def rgcd(a, b):
    a = float(a)
    b = float(b)
    u = 1
    d = a

    if b < 0.2:
        return a, b, u, 0

    v1 = 0
    v3 = b

    while True:
        if v3 < 0.2:
            v = (d - a * u) / b
            return d, v3, u, v

        q = math.floor(d / v3)
        t3 = d % v3

        t1 = u - q * v1
        u = v1
        d = v3
        v1 = t1
        v3 = t3


def regulator_and_F(C):
    R = 0
    j = ru - 3
    r = C.ncols()

    while True:
        j += 1

        if j >= r:
            break

        i = random.randint(0, ru - 1)

        A = C.delete_rows([i])
        A = A.matrix_from_columns(range(j - ru + 2, j + 1))
        A = A.apply_map(real)

        R1 = A.determinant()
        d, err, u, v = rgcd(R, R1)

        R = d

        if (j - ru + 1) == -1:
            Cj = v * C.column(j)

        else:
            Cj = v * C.column(j) + ((-1) ** ru) * u * C.column(j - ru + 1)

        if j != -1:
            C.set_column(j, Cj)

    F = C.matrix_from_columns(range(C.ncols() - (ru - 1), C.ncols()))
    return R, F


# A function for the vector Delta_C(a) in Steps 7 and 8
# of the matrix of relations algorithm
def deltaC(a):
    deltaC = []
    maps = K.places()

    for i in range(0, r1):
        deltaC.append(cmath.log(maps[i](a)) - cmath.log(K(a).norm()) / n)

    for i in range(r1, r1 + r2):
        deltaC.append(2 * (cmath.log(maps[i](a)) - cmath.log(K(a).norm()) / n))

    return deltaC


# Specify the number field by the minimal polynomial P
# of an integral primitive element alpha
Qx = QQ['x']
#P = Qx([105, 0, 1])  # [2,2,2]
K = NumberField(P, 'a')
(a) = K.gens()
n = K.degree()

# The matrix of relations algorithm
# Step 1: Compute the signature (r1, r2)
signature = K.signature()
r1 = signature[0]
r2 = signature[1]
ru = r1 + r2

# Step 2: Compute D
D = K.discriminant()

# Step 3: Compute the Minkowski bound
Mk = ((4 / np.pi) ** r2) * (math.factorial(n) / (n ** n)) * math.sqrt(abs(D))
# or if assuming GRH, take the Bach bound
# Mk = 12*(np.log(abs(D)))**2

print("D: ", D)
print("r1: ", r1, ", r2: ", r2, sep='')
print("basis for ring of integers: ", K.integral_basis())
print("M_k: ", Mk)

# Step 4:
u = 1
S = []

# Step 5: Compute the small factor base S
p = 2
while u <= Mk and p <= Mk:
    print(p, u)
    if sympy.isprime(p) and (D % p != 0):
        F = np.array(K.ideal(p).factor())
        prime_factors = F[:, 0]
        exponents = F[:, 1]

        for i in range(0, len(prime_factors)):
            prime_norm = prime_factors[i].norm()
            if prime_norm <= Mk:
                S.append(prime_factors[i])
                u = u * prime_norm

    p += 1

s = len(S)

print("s: ", s)

# Step 6: Compute FB and the Euler product z
FB = []
z = 1

p = 2
while p <= Mk:
    if sympy.isprime(p):
        F = np.array(K.ideal(p).factor())
        prime_factors = F[:, 0]
        exponents = F[:, 1]

        # Add non-inert prime ideals to FB
        if len(exponents) > 1 or exponents[0] != 1:
            for i in range(0, len(exponents)):
                prime_norm = prime_factors[i].norm()

                # Skip those already in S - we'll add those to FB after
                if prime_norm <= Mk and not (prime_factors[i] in S):
                    FB.append(prime_factors[i])

        # Update the Euler product for this prime p
        denom = 1

        for i in range(0, len(prime_factors)):
            denom = denom * (1 - 1 / prime_factors[i].norm())

        z = z * (1 - 1 / p) / denom

    p += 1

# Add in the s elements of S - we want these at the start of FB
FB = S + FB
k = len(FB)

print("k = |FB| = ", k)
print("z: ", z)

# Step 7: Find trivial relations
k2 = k + ru + 10
# We will need to take the transpose of Mt and MCt to get M and MC
Mt = []
MCt = []
m = 0

p = 2
while p <= Mk:
    if sympy.isprime(p):
        F = np.array(K.ideal(p).factor())
        prime_factors = F[:, 0]
        exponents = F[:, 1]

        v = [0 for i in range(0, k)]
        for i in range(0, len(exponents)):
            if prime_factors[i] in FB:
                index = FB.index(prime_factors[i])
                v[index] = exponents[i]

            else:
                break

            # if we reached the last prime factor and it was in FB, then:
            if i == (len(exponents) - 1):
                prime_norm = prime_factors[i].norm()
                Mt.append(v)
                MCt.append(deltaC(p))

                m += 1
                print("m = ", m)

    p += 1

print("m: ", m)
print("Mt: \n", Mt)
print("MCt: \n", matrix(MCt).str(rep_mapping=lambda x: str(x.n(digits=3))))

# Step 8 is contained in the class group algorithm
# We loop Step 8 until we have eenough relations to compute Cl(K)


# The class group algorithm
# Step 2: Compute the order of the group of roots of unity
w = K.number_of_roots_of_unity()

# Step 3: Update the Euler product
z = (2 ** (-r1)) * ((2 * np.pi) ** (-r2)) * w * math.sqrt(abs(D)) * z
print("z: ", z)

while True:
    while m <= k2:
        # Generate the random powers of elements of S
        w = []
        for i in range(0, s):
            w.append(random.randint(0, 20))  # or maybe 20?
        for i in range(s, k):
            w.append(0)

        # Avoid the case where all the a_i are zero
        for i in range(0, s):
            if w[i] != 0:
                break
            else:
                w[0] = 1

        A = K.ideal(1)
        for i in range(0, s):
            A = A * (S[i] ** w[i])

        # Generate a random element a in A
        for j in range(0, 10):
            a = A.random_element(-15, 15)
            if a.norm() == 0:
                continue

            # Compute the ideal B = (a)A^{-1}
            B = (K.ideal(a)) / A

            if B == K.ideal(1): continue

            # Check if B factors over FB
            F = np.array(B.factor())
            prime_factors = F[:, 0]
            exponents = F[:, 1]
            b = [0 for i in range(0, k)]
            v = [0 for i in range(0, k)]

            for i in range(0, len(exponents)):
                if prime_factors[i] in FB:
                    index = FB.index(prime_factors[i])
                    b[index] = exponents[i]

                else:
                    break

                # B factors over FB, so add a relation
                if i == (len(exponents) - 1):
                    prime_norm = prime_factors[i].norm()
                    v = [w[i] + b[i] for i in range(0, k)]
                    Mt.append(v)
                    MCt.append(deltaC(a))

                    m += 1
                    print("m = ", m)



    M = matrix(Mt).transpose()
    H = M
    MC = matrix(MCt).transpose()

    # Step 4: Hermite reduction of M and MC
    H, U = M.transpose().hermite_form(transformation=True)  # .antitranspose()

    # Step 5
    MCp = U * (MC.transpose())

    H = H.antitranspose()
    MCp = MCp.antitranspose()

    # Step 6
    A = H.right_kernel_matrix(basis='LLL').transpose()

    # Step 7
    C = MCp * A

    # Step 8: Compute R and F
    R, F = regulator_and_F(C)
    print("R: ", R)
    print("F: \n", F)

    # Step 9: Check that C and H are full-rank
    if H.rank() != H.nrows(): continue
    if C.rank() != C.nrows(): continue

    # Step 10: Compute the matrix W
    i = 0
    while i < H.ncols():
        if matrix(H.column(i)) == matrix(1, H.nrows(), 0):
            H = H.delete_columns([i])
        else:
            i += 1

    i = 0
    while i < H.ncols():
        if H[i][i] == 1:
            H = H.delete_columns([i])
            H = H.delete_rows([i])
        else:
            i += 1

    W = H

    # Step 11: Compute the class number h
    h = W.determinant()
    print("W: \n", W, sep='')
    print("h: ", h)

    # Step 12: Check whether enough relations found
    if h * R >= z * math.sqrt(2):
        print("Not enough relations! Continuing search.")
        k2 += 10
        continue

    # Step 13: Compute the Smith form of W
    else:
        W = W.smith_form()[0]

        diagonal = []
        for d in W.diagonal():
            if d > 1:
                diagonal.append(d)

        classgroup = ' x '.join(['Z' + str(d) for d in diagonal])

        if diagonal == []:
            classgroup = "trivial"

        # Step 14: Output h, R and Cl(K)
        print("Class number: h=", h, sep='')
        print("Regulator: R=", R, sep='')
        print("Class group: ", classgroup)
        break