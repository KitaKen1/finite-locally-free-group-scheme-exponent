"""Verify a rank-nine group scheme with a point of order 27. Requires SymPy.

R = (Z/9)[a,b,s,t] / ((s,t)^2, (a,b)^6, s*a^3-3, t*b^3-3, s*b^3, t*a^3).
The coordinates x,y satisfy x^3=-s*W(x,y), y^3=-t*W(x,y). Their nine
monomials of individual degrees below three form an R-basis: after a cubic
substitution any further cubic substitution gives zero by (s,t)^2=0.
A monomial divisible by both cubics reduces to zero in either order.

The law is v*w = v + (1+a*v[0]+b*v[1])*w. Its multiplier is multiplicative,
so it is associative, with identity (0,0). The two-point check below shows it
descends to the cubic quotient. Iteration on the universal point verifies the
27th power is the identity (hence the 26th power supplies inverses), while
the ninth power has a coefficient detected by an explicit additive functional.
"""

from collections import defaultdict
from functools import lru_cache

from sympy import ZZ
from sympy.polys.rings import ring


polynomials, a, b, s, t, x, y, u, v = ring("a,b,s,t,x,y,u,v", ZZ)


def multiplier(x_coord, y_coord):
    return 1 + a * x_coord + b * y_coord


def correction(x_coord, y_coord):
    c = a * x_coord + b * y_coord
    return c + c**2 + a**2 * b * x_coord**2 * y_coord + a * b**2 * x_coord * y_coord**2


@lru_cache(None)
def reduce_monomial(powers):
    """Return (monomial, integer coefficient) pairs before coefficient reduction."""
    a_deg, b_deg, s_deg, t_deg, *coords = powers
    if a_deg + b_deg >= 6 or s_deg + t_deg >= 2:
        return ()
    if (s_deg and b_deg >= 3) or (t_deg and a_deg >= 3):
        return ()
    if s_deg and a_deg >= 3:
        if max(coords) >= 3:  # another cubic substitution is killed by 3s=3t=0
            return ()
        return (((a_deg - 3, b_deg, 0, 0, *coords), 3),)
    if t_deg and b_deg >= 3:
        if max(coords) >= 3:
            return ()
        return (((a_deg, b_deg - 3, 0, 0, *coords), 3),)

    for pair_index, pair in enumerate(((x, y), (u, v))):
        for coord_index, coefficient in enumerate((s, t)):
            index = 2 * pair_index + coord_index
            if coords[index] < 3:
                continue
            coords[index] -= 3
            residual = (a_deg, b_deg, s_deg, t_deg, *coords)
            output = defaultdict(int)
            for monomial, value in (-coefficient * correction(*pair)).items():
                shifted = tuple(i + j for i, j in zip(residual, monomial))
                for reduced, factor in reduce_monomial(shifted):
                    output[reduced] += int(value) * factor
            return tuple(output.items())
    return ((powers, 1),)


def normal_form(polynomial):
    output = defaultdict(int)
    for monomial, coefficient in polynomial.items():
        for reduced, factor in reduce_monomial(monomial):
            output[reduced] += int(coefficient) * factor
    terms = {}
    for monomial, value in output.items():
        a_deg, b_deg, s_deg, t_deg = monomial[:4]
        # 3 kills s,t and base monomials of degree >=3, by the relations of R.
        modulus = 3 if s_deg + t_deg or a_deg + b_deg >= 3 else 9
        if value % modulus:
            terms[monomial] = value % modulus
    return polynomials.from_dict(terms)


def witness(polynomial):
    """Z/9-linear functional on the base: b^2 -> 1, s*a^3*b^2 and t*b^5 -> 3."""
    return sum(int(polynomial.get((*powers, 0, 0, 0, 0), 0)) * weight
               for powers, weight in [((0, 2, 0, 0), 1), ((3, 2, 1, 0), 3),
                                      ((0, 5, 0, 1), 3)]) % 9


def verify():
    relations = [s**2, s*t, t**2, s*a**3 - 3, t*b**3 - 3, s*b**3, t*a**3]
    relations.extend(a**i * b**(6-i) for i in range(7))
    # All other monomial multiples have degree beyond the functional's support.
    for i in range(6):
        for j in range(6-i):
            for extra in (1, s, t):
                for relation in relations:
                    assert witness(a**i * b**j * extra * relation) == 0
    assert witness(3 * b**2) == 3

    lam = multiplier(x, y)
    left, right = x + lam*u, y + lam*v
    assert multiplier(left, right) == lam * multiplier(u, v)
    assert not normal_form(left**3 + s * correction(left, right))
    assert not normal_form(right**3 + t * correction(left, right))

    x_power = y_power = polynomials.zero
    for exponent in range(1, 28):
        scale = multiplier(x_power, y_power)
        x_power = normal_form(x_power + scale*x)
        y_power = normal_form(y_power + scale*y)
        if exponent == 9:
            assert x_power == 6*a*b*x**2*y + 3*b**2*x*y**2
            assert y_power == 3*a**2*x**2*y + 6*a*b*x*y**2
            print("[9]x =", x_power)
            print("[9]y =", y_power)
    assert not x_power and not y_power
    print("[27](x,y) = (0,0). The universal point has order 27.")


if __name__ == "__main__":
    verify()
