# OEIS A000051: 2^n + 1 as a permanent

**Source:** [OEIS A000051](https://oeis.org/A000051), conjecture by Peter Luschny
**Type:** known result formalized
**Status:** ✅ fully Lean-checked (`lean/Math/OEIS/A000051.lean`); statement in review

## Statement

> For any integer n >= 0, a(n) is the permanent of the (n+1) X (n+1) matrix with
> M(j, k) = -floor((j - k - 2)/(n + 1)).

where a(n) = 2^n + 1. The OEIS entry also says that "the corrected Luschny's conjecture is true"
(Sela Fried), so this is probably a known result rather than an open problem.

## What is done

- Lean statement written and accepted by the Left To Solve checker, using Mathlib's
  `Matrix.permanent` and the true floor of a rational.
- Computational check (`check.py`): the permanent equals 2^n + 1 for n = 0..7.
- Lean proof complete: `permanent_luschnyMatrix` in `lean/Math/OEIS/A000051.lean` (axioms: propext, Classical.choice, Quot.sound only).

## Links

- Left To Solve page: <https://lefttosolve.com/p/oeis-a000051>
- Pull request: <https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/3911>
