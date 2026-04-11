"""
Comprehensive tests for all builtins in every supported mode.
Tests both solver1 and solver2.
"""

from arsenal.assertions import assert_throws

from dyna import Program, InstFault
from dyna.execute.solver import Solver as Solver1
from dyna.execute.solver2 import Solver as Solver2


# ─── Solver2 tests (primary) ──────────────────────────────────────────────────

def test_unification():
    """= builtin: variable binding and ground matching."""

    # bind variable
    Solver2(Program("f(X) += X = 5."))().assert_equal("f(5) += 1.")

    # ground match success
    Solver2(Program("f += 5 = 5."))().assert_equal("f += 1.")

    # ground match failure (no results)
    Solver2(Program("f += 3 = 4."))().assert_equal("")


def test_direct_comparisons():
    """Comparisons used directly as subgoals (not inside `is`)."""

    Solver2(Program("""
    gt  += 3 > 2.
    lt  += 2 < 3.
    gte += 3 >= 3.
    gte2 += 3 >= 2.
    lte += 2 <= 3.
    lte2 += 3 <= 3.
    neq += 3 != 4.
    """))().assert_equal("""
    gt += 1.
    lt += 1.
    gte += 1.
    gte2 += 1.
    lte += 1.
    lte2 += 1.
    neq += 1.
    """)

    # failures: none of these should produce results
    Solver2(Program("""
    a += 2 > 3.
    b += 3 < 2.
    c += 2 >= 3.
    d += 3 <= 2.
    e += 3 != 3.
    """))().assert_equal("")


def test_unary_negation():
    """Unary - via `is`: forward and inverse modes."""

    # forward with variable: Y=3, X is -Y → X=-3
    Solver2(Program("f(X) += Y=3, X is -Y."))().assert_equal("f(-3) += 1.")

    # inverse: Y=3, Y is -X → X=-3
    Solver2(Program("f(X) += Y=3, Y is -X."))().assert_equal("f(-3) += 1.")

    # literal folded by parser: X is -3 should error (use X = -3 instead)
    with assert_throws(InstFault):
        Solver2(Program("f(X) += X is -3."))()


def test_unary_plus():
    """Unary + via `is`: forward mode."""

    Solver2(Program("f(X) += Y=3, X is +Y."))().assert_equal("f(3) += 1.")


def test_abs():
    """abs via `is`: forward and inverse modes."""

    # forward: X is abs(-3)
    Solver2(Program("f(X) += X is abs(-3)."))().assert_equal("f(3) += 1.")

    # forward: X is abs(3) (already positive)
    Solver2(Program("f(X) += X is abs(3)."))().assert_equal("f(3) += 1.")

    # inverse: 3 is abs(X) → X in {3, -3}
    p = Program("f(X) += 3 is abs(X).")
    d = Solver2(p)()
    d.user_query('f(3)').assert_equal("f(3) += 1.")
    d.user_query('f(-3)').assert_equal("f(-3) += 1.")


def test_str_type_check():
    """str type check via `is`."""

    Solver2(Program("""
    a(X) += X is str("hello").
    b(X) += X is str(5).
    """))().assert_equal("""
    a(true) += 1.
    b(false) += 1.
    """)


def test_int_type_check():
    """int type check via `is`."""

    Solver2(Program("""
    a(X) += X is int(5).
    b(X) += X is int("hello").
    """))().assert_equal("""
    a(true) += 1.
    b(false) += 1.
    """)


def test_bool_negation():
    """! (boolean negation) via `is`: forward and inverse modes."""

    # forward: X is !true → X=false
    Solver2(Program("f(X) += X is !true."))().assert_equal("f(false) += 1.")

    # forward: X is !false → X=true
    Solver2(Program("f(X) += X is !false."))().assert_equal("f(true) += 1.")

    # inverse: false is !X → X=true
    Solver2(Program("f(X) += false is !X."))().assert_equal("f(true) += 1.")


def test_addition_forward():
    """Binary + (addition): forward mode."""

    Solver2(Program("f(X) += X is 3 + 4."))().assert_equal("f(7) += 1.")


def test_addition_inverse():
    """Binary + (addition): inverse modes solving for each operand."""

    # solve for first operand: 7 is X + 4
    Solver2(Program("f(X) += 7 is X + 4."))().assert_equal("f(3) += 1.")

    # solve for second operand: 7 is 3 + X
    Solver2(Program("f(X) += 7 is 3 + X."))().assert_equal("f(4) += 1.")


def test_addition_identity():
    """Binary + identity elements."""

    # 0 + Y
    Solver2(Program("f(X) += X is 0 + 5."))().assert_equal("f(5) += 1.")

    # Y + 0
    Solver2(Program("f(X) += X is 5 + 0."))().assert_equal("f(5) += 1.")


def test_string_concat():
    """Binary + with strings: concatenation and splitting."""

    # forward concat
    Solver2(Program('f(X) += X is "ab" + "cd".'))().assert_equal('f("abcd") += 1.')

    # string split: "ab" is X + Y → all splits
    p = Program('f(X, Y) += "ab" is X + Y.')
    d = Solver2(p)()
    d.user_query('f("", "ab")').assert_equal('f("", "ab") += 1.')
    d.user_query('f("a", "b")').assert_equal('f("a", "b") += 1.')
    d.user_query('f("ab", "")').assert_equal('f("ab", "") += 1.')


def test_subtraction():
    """Binary - (subtraction): rewrites to + inverse."""

    # X is 7 - 3 → X=4
    Solver2(Program("f(X) += X is 7 - 3."))().assert_equal("f(4) += 1.")

    # inverse: 4 is X - 3 → X=7
    Solver2(Program("f(X) += 4 is X - 3."))().assert_equal("f(7) += 1.")

    # inverse: 4 is 7 - X → X=3
    Solver2(Program("f(X) += 4 is 7 - X."))().assert_equal("f(3) += 1.")


def test_multiplication_forward():
    """Binary * (multiplication): forward mode."""

    Solver2(Program("f(X) += X is 3 * 4."))().assert_equal("f(12) += 1.")


def test_multiplication_inverse():
    """Binary * (multiplication): inverse modes."""

    # solve for first: 12 is X * 4
    Solver2(Program("f(X) += 12 is X * 4."))().assert_equal("f(3.0) += 1.")

    # solve for second: 12 is 3 * X
    Solver2(Program("f(X) += 12 is 3 * X."))().assert_equal("f(4.0) += 1.")


def test_multiplication_identity():
    """Binary * identity elements."""

    # 1 * Y
    Solver2(Program("f(X) += X is 1 * 5."))().assert_equal("f(5) += 1.")

    # Y * 1
    Solver2(Program("f(X) += X is 5 * 1."))().assert_equal("f(5) += 1.")


def test_string_repetition():
    """Binary * with string and int."""

    Solver2(Program('f(X) += X is "ab" * 3.'))().assert_equal('f("ababab") += 1.')


def test_division():
    """Binary / (division): rewrites to * inverse."""

    Solver2(Program("f(X) += X is 12 / 4."))().assert_equal("f(3.0) += 1.")


def test_comparisons_via_is():
    """Comparison operators inside `is` return booleans."""

    Solver2(Program("""
    gt_t(X) += X is 3 > 2.
    gt_f(X) += X is 2 > 3.
    lt_t(X) += X is 2 < 3.
    lt_f(X) += X is 3 < 2.
    gte_t(X) += X is 3 >= 3.
    gte_f(X) += X is 2 >= 3.
    lte_t(X) += X is 3 <= 3.
    lte_f(X) += X is 3 <= 2.
    eq_t(X) += X is 3 == 3.
    eq_f(X) += X is 3 == 4.
    ne_t(X) += X is 3 != 4.
    ne_f(X) += X is 3 != 3.
    """))().assert_equal("""
    gt_t(true) += 1.
    gt_f(false) += 1.
    lt_t(true) += 1.
    lt_f(false) += 1.
    gte_t(true) += 1.
    gte_f(false) += 1.
    lte_t(true) += 1.
    lte_f(false) += 1.
    eq_t(true) += 1.
    eq_f(false) += 1.
    ne_t(true) += 1.
    ne_f(false) += 1.
    """)


def test_min_max():
    """min and max builtins."""

    Solver2(Program("""
    a(X) += X is min(3, 5).
    b(X) += X is max(3, 5).
    c(X) += X is min(5, 3).
    d(X) += X is max(5, 3).
    e(X) += X is min(3, 3).
    f(X) += X is max(3, 3).
    """))().assert_equal("""
    a(3) += 1.
    b(5) += 1.
    c(3) += 1.
    d(5) += 1.
    e(3) += 1.
    f(3) += 1.
    """)


def test_range():
    """range(X, A, B) enumerates integers from A to B-1."""

    Solver2(Program("""
    f(X) += true is range(X, 0, 5).
    """))().assert_equal("""
    f(0) += 1.
    f(1) += 1.
    f(2) += 1.
    f(3) += 1.
    f(4) += 1.
    """)

    # empty range
    Solver2(Program("f(X) += true is range(X, 5, 5)."))().assert_equal("")

    # single element
    Solver2(Program("f(X) += true is range(X, 3, 4)."))().assert_equal("f(3) += 1.")


def test_not_matches():
    """$not_matches builtin."""

    # doesn't match → succeeds
    Solver2(Program('b += $not_matches("f(X)", g(1)).'))().assert_equal("b += 1.")

    # matches ground → fails
    Solver2(Program('a += $not_matches("f(X)", f(1)).'))().assert_equal("")

    # variable pattern → InstFault
    with assert_throws(InstFault):
        Solver2(Program('e += $not_matches("f(1)", f(X)).'))()


def test_chained_builtins():
    """Multiple builtins chained together in one rule."""

    # classic iteration pattern
    Solver2(Program("""
    f(0).
    f(Z) += f(X), Y is X + 1, Y < 5, Y = Z.
    """))().assert_equal("""
    f(0) += 1.
    f(1) += 1.
    f(2) += 1.
    f(3) += 1.
    f(4) += 1.
    """)

    # range + arithmetic + comparison
    Solver2(Program("""
    f(Y) += true is range(X, 1, 6), Y is X * X, Y < 20.
    """))().assert_equal("""
    f(1) += 1.
    f(4) += 1.
    f(9) += 1.
    f(16) += 1.
    """)


def test_inst_fault_on_insufficient_binding():
    """Builtins raise InstFault when arguments are insufficiently bound."""

    # + with nothing bound
    with assert_throws(InstFault):
        Solver2(Program("f(X) += X is Y + Z."))()

    # comparison with unbound arg
    with assert_throws(InstFault):
        Solver2(Program("f += X > 3."))()

    # min with unbound arg
    with assert_throws(InstFault):
        Solver2(Program("f(X) += X is min(Y, 3)."))()


# ─── Solver1 tests (parallel coverage) ────────────────────────────────────────

def test_solver1_unification():
    Solver1(Program("f(X) += X = 5."))().assert_equal("f(5) += 1.")
    Solver1(Program("f += 5 = 5."))().assert_equal("f += 1.")
    Solver1(Program("f += 3 = 4."))().assert_equal("")


def test_solver1_comparisons():
    Solver1(Program("""
    gt  += 3 > 2.
    lt  += 2 < 3.
    gte += 3 >= 3.
    lte += 3 <= 3.
    neq += 3 != 4.
    """))().assert_equal("""
    gt += 1.
    lt += 1.
    gte += 1.
    lte += 1.
    neq += 1.
    """)

    Solver1(Program("a += 2 > 3."))().assert_equal("")


def test_solver1_arithmetic():
    Solver1(Program("""
    a(X) += X is 3 + 4.
    b(X) += X is 3 * 4.
    c(X) += Y=3, X is -Y.
    d(X) += X is abs(-3).
    e(X) += X is min(3, 5).
    f(X) += X is max(3, 5).
    """))().assert_equal("""
    a(7) += 1.
    b(12) += 1.
    c(-3) += 1.
    d(3) += 1.
    e(3) += 1.
    f(5) += 1.
    """)


def test_solver1_range():
    Solver1(Program("f(X) += true is range(X, 0, 3)."))().assert_equal("""
    f(0) += 1.
    f(1) += 1.
    f(2) += 1.
    """)


def test_solver1_not_matches():
    Solver1(Program('b += $not_matches("f(X)", g(1)).'))().assert_equal("b += 1.")
    Solver1(Program('a += $not_matches("f(X)", f(1)).'))().assert_equal("")
    with assert_throws(InstFault):
        Solver1(Program('e += $not_matches("f(1)", f(X)).'))()


def test_solver1_chained():
    Solver1(Program("""
    f(0).
    f(Z) += f(X), Y is X + 1, Y < 5, Y = Z.
    """))().assert_equal("""
    f(0) += 1.
    f(1) += 1.
    f(2) += 1.
    f(3) += 1.
    f(4) += 1.
    """)


if __name__ == '__main__':
    from arsenal.testing_framework import testing_framework
    testing_framework(globals())
