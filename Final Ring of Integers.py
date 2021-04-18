#!/usr/bin/env sage -python
import sys
from sage.all import *


# Determine whether v is in the Q-span of the basis
def is_in_span(basis, v):
    try:
        mat = matrix(QQ, basis)
        mat = mat.transpose()
        matrix(mat).solve_right(vector(v))
        return True
    except ValueError:
        return False


# Raise P to the power pow, mod p
def polynomial_power_mod_f(a, pow, P):
    g = S(a)
    h = Qx(list(g**pow))
    return h


# Define Qx to be the polynomial ring over the rationals
Qx = QQ['x']
P = Qx([1791, 585, 24, 0, 1]) # P(x) = x^4 + 24x^2 + 585x + 1791
S = Qx.quotient(P, 'y')
n = P.degree()

# Step 1: Initialise the basis of O
std_basis = [Qx(x**i) for i in range(0, n)]
basis = std_basis
old_HNF = matrix.identity(n)

# Step 2: Compute the discriminant of P
D = P.discriminant()

# Step 3
L = [a[0] for a in list(factor(D)) if a[1] >= 2]

k = 0
while k < len(L):

    # Step 4
    p = L[k]
    j = 1
    while p ** j < n: j += 1

    basis_matrix = matrix(QQ, [a.padded_list(n) for a in basis]).transpose()

    # The matrix of the transformation x -> x^(p^j) is given by
    A = basis_matrix.inverse() * matrix(QQ,
            [polynomial_power_mod_f(a, p**j, P).padded_list(n)
                for a in basis]).transpose()
    A = matrix(FiniteField(p), A)

    # Step 5: Compute a basis of I_p/pO
    A_kernel = list(A.right_kernel().basis())

    # Step 6: Compute a basis of I_p/pI_p
    I_pI_basis = list(A_kernel)

    for i in range(0, len(basis)):
        e_i = (Qx(x**i)).padded_list(n)

        if is_in_span(A_kernel, vector(QQ, e_i)) == False:
            I_pI_basis.append([(p * b) for b in e_i])
            A_kernel.append([(p * b) for b in e_i])

    I_pI_basis = matrix(QQ, I_pI_basis)
    I_pI_basis_polynomials = list(vector((I_pI_basis)
                                * matrix(basis).transpose()))
    I_pI_cob_matrix = matrix(QQ, [a.padded_list(n)
                                    for a in I_pI_basis_polynomials]).transpose()

    # Step 7: Compute the matrix of the map
    # Ker(O/pO -> End(I_p/pI_p), w -> (y -> wy))
    C = []

    for i in range(0, n):
        C.append((I_pI_cob_matrix.inverse()
                  * matrix(QQ, [(((basis[i] * y)) % P).padded_list(n)
                                    for y in I_pI_basis_polynomials])
                                        .transpose()).list())

    C = matrix(FiniteField(p), C).transpose()

    # Step 8: Compute a basis for the kernel of C
    C_kernel = C.right_kernel()

    # Step 9: Compute the matrix M
    new_basis = list(basis)

    if not C_kernel.dimension() == 0:
        for a in C_kernel.basis():
            new_basis.append(vector(basis).dot_product(vector(QQ, a) / p))

    M = basis_matrix.inverse() * matrix(QQ, [a.padded_list(n)
                                             for a in new_basis]).transpose()

    # Step 10: Compute the HNF of M
    new_HNF = matrix(ZZ, (p * M) % p**3).transpose()\
                        .hermite_form(include_zero_rows=False).transpose()
    new_HNF = matrix(QQ, new_HNF * (1 / p))

    new_basis = list(new_HNF.transpose())

    # Step 11: Check if O = Op
    if new_HNF == old_HNF:
        k += 1
        old_HNF = new_HNF
    else:
        basis = (matrix(basis) * new_HNF).list()

print("Final basis: ", basis, sep='')
