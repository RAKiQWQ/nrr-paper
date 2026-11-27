"""Exact finite checks for the winding construction and the layer moment formulas."""

from collections import Counter
from fractions import Fraction as F
from itertools import product
from math import comb, gcd


EXAMPLES = {
    6: (-1, -1, 1),
    10: (-1, -1, -2, -1, 2),
    12: (-1, -1, -1, -1, 1, 0),
    15: (-1, 1, -1, 1, -2, 1, 0),
}


def prime_power_base(n):
    """Return the base prime of a prime power and 1 for a mixed prime factorization."""
    prime = next(divisor for divisor in range(2, n + 1) if n % divisor == 0)
    remainder = n
    while remainder % prime == 0:
        remainder //= prime
    return prime if remainder == 1 else 1


def mark(j, n):
    return 1 - F(2 * j, n)


def append_turns(path, center, radius, turns):
    """From the top vertex, go around a diamond; positive turns go counterclockwise."""
    left = (center - radius, 0)
    bottom = (center, -radius)
    right = (center + radius, 0)
    top = (center, radius)
    assert path[-1] == top
    vertices = [left, bottom, right, top] if turns >= 0 else [right, bottom, left, top]
    path.extend(vertices * abs(turns))


def winding_polygon(n, coefficients):
    radius = F(1, 4 * n)
    top = (0, radius)
    half = [top]
    for j in range(1, (n + 1) // 2):
        center = mark(j, n)
        half.append((center, radius))
        append_turns(half, center, radius, coefficients[j - 1] - 1)
        half.append(top)
    central_turns = coefficients[-1] if n % 2 == 0 else 0
    append_turns(half, 0, radius, central_turns)
    half.extend([(radius, 0), (0, -radius)])
    edges = len(half) - 1
    vertical_step = max(abs(q[1] - p[1]) for p, q in zip(half, half[1:]))
    epsilon = 1 / (1 + edges * vertical_step)
    assert epsilon * edges * vertical_step / 2 < F(1, 2)
    half = [(s, b * epsilon) for s, b in half]
    assert all(abs(s) < 1 for s, _ in half)
    closed = half + [(-s, -b) for s, b in half[1:]]
    assert closed[-1] == closed[0]
    return closed


def index_at(vertices, center):
    """Count signed crossings of a ray from (center, 0), including vertex hits once."""
    index = 0
    for (sx, sy), (tx, ty) in zip(vertices, vertices[1:]):
        orient = (tx - sx) * (-sy) - (ty - sy) * (center - sx)
        if orient == 0 and min(sx, tx) <= center <= max(sx, tx) and min(sy, ty) <= 0 <= max(sy, ty):
            raise AssertionError("The polygon meets a puncture")
        if sy <= 0 < ty and orient > 0:
            index += 1
        if ty <= 0 < sy and orient < 0:
            index -= 1
    return index


def check_degrees():
    for n in range(2, 201):
        divisor = gcd(*(comb(n, j) for j in range(1, n)))
        assert divisor == prime_power_base(n)
    print("Internal binomial gcd agrees with factorization for n = 2..200.")
    for n, coefficients in EXAMPLES.items():
        assert len(coefficients) == n // 2
        curve = winding_polygon(n, coefficients)
        degrees = [1, *(1 + index_at(curve, mark(j, n)) for j in range(1, n)), 1]
        for j, value in enumerate(coefficients, start=1):
            expected = 2 * value if 2 * j == n else value
            assert degrees[j] == expected == degrees[n - j]
        # Fix the first of the n-1 root signs to be positive, then count actual ends.
        ends = Counter()
        for other_signs in product((0, 1), repeat=n - 2):
            j = 1 + sum(other_signs)
            ends[degrees[j] + degrees[j + 1]] += 1
        total = sum(degree * count for degree, count in ends.items())
        binomial_sum = sum(comb(n, j) * degree for j, degree in enumerate(degrees))
        assert sum(ends.values()) == 2 ** (n - 2)
        assert binomial_sum == 2 * total == 0
        if n == 6:
            assert ends == {-2: 5, 0: 1, 1: 10}
        print(f"n={n}: {sum(ends.values())} ends, total winding {total}, "
              f"winding counts {dict(sorted(ends.items()))}.")


BASE_RULE = ((-1, F(1, 6)), (0, F(2, 3)), (1, F(1, 6)))


def cube_moments(mass_height, upper_height, lower_parameter, increment):
    """Direct vertical integration and exact Simpson average on the square."""
    px, py = lower_parameter
    wx, wy = increment
    moments = [F(0) for _ in range(4)]
    for (x, x_weight), (y, y_weight) in product(BASE_RULE, repeat=2):
        lower = upper_height - mass_height + 3 * mass_height * (px * x + py * y)
        upper = upper_height + 3 * mass_height * ((px + wx) * x + (py + wy) * y)
        length = upper - lower
        z_integral = (upper**2 - lower**2) / 2
        values = (x * length, y * length, (1 + x) * z_integral, y * z_integral)
        for j, value in enumerate(values):
            moments[j] += x_weight * y_weight * value / mass_height
    return moments


def check_moments():
    grid = (F(-1, 100), F(0), F(1, 100))
    checks = 0
    for m, t in product((F(1, 3), F(2, 15)), (F(-1, 5), F(3, 7))):
        center = t - m / 2
        for px, py, wx, wy in product(grid, repeat=4):
            mx, my, vx, vy = cube_moments(m, t, (px, py), (wx, wy))
            norm_squared = wx**2 + wy**2
            mean_z = center + 3 * m * (px * wx + py * wy + norm_squared / 2)
            assert (mx, my) == (wx, wy)
            assert vx == m * px + t * wx + mean_z
            assert vy == m * py + t * wy
            recovered_y = (vy - t * wy) / m
            recovered_x = (vx - t * wx - center - 3 * m * recovered_y * wy
                           - 3 * m * norm_squared / 2) / (m * (1 + 3 * wx))
            assert (recovered_x, recovered_y) == (px, py)
            checks += 1
    # After the vertical integral is divided by m, it is affine separately in
    # m and t, and at most quadratic in each slope coordinate. The grid fixes
    # all polynomial coefficients in (5). Recovery follows by multiplication.
    print(f"Four cube moments and slope recovery: {checks} exact interpolation nodes.")


def check_ball_cap():
    # Area at height x is pi*(1-x*x). The antiderivative below omits pi.
    def primitive(x):
        return x - x**3 / 3

    height = F(7, 10)
    assert height**2 < F(1, 2)
    fraction = (primitive(F(1)) - primitive(height)) / (primitive(F(1)) - primitive(F(-1)))
    assert fraction == F(243, 4000) < F(1, 6)
    print("3D cap at 1/sqrt(2) is smaller than 243/4000, the volume fraction at 7/10.")


def check_asymmetric_body():
    # Pyramid with apex (0,0,1) and base [-1,2] x [-1,1] at height -1.
    # A slice at z scales both horizontal coordinates by (1-z)/2.
    # Its area is quadratic in z and its horizontal first moments are cubic.
    mass = F(0)
    moment_x = F(0)
    moment_y = F(0)
    for (s, sw), (v, vw), (z, zw) in product(BASE_RULE, repeat=3):
        scale = F(1 - z, 2)
        x = scale * (1 + 3 * s) / 2
        y = scale * v
        weight = 12 * sw * vw * zw * scale**2
        mass += weight
        moment_x += x * weight
        moment_y += y * weight
    assert (mass, moment_x, moment_y) == (4, F(3, 2), 0)

    # A centered small cube also gives isotropic second moments. Use a
    # bound R on its horizontal radius in the positive weight correction.
    side = F(1, 2)
    radius_bound = F(1, 2)
    kappa = side**5 / 12
    corrected_x, corrected_y = moment_x, moment_y
    for (s, sw), (v, vw), (t, tw) in product(BASE_RULE, repeat=3):
        x, y, z = side * s / 2, side * v / 2, side * t / 2
        scale = (1 - z) / 2
        assert -scale <= x <= 2 * scale and abs(y) <= scale
        assert x**2 + y**2 <= radius_bound**2
        added_weight = (radius_bound * moment_x - moment_x * x) / kappa
        assert added_weight >= 0
        weighted_volume = added_weight * side**3 * sw * vw * tw
        corrected_x += x * weighted_volume
        corrected_y += y * weighted_volume
    assert (corrected_x, corrected_y) == (0, 0)
    print("Asymmetric pyramid: horizontal first moment (3/2, 0) becomes (0, 0) exactly.")


if __name__ == "__main__":
    check_degrees()
    check_moments()
    check_ball_cap()
    check_asymmetric_body()
