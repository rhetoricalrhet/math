# OEIS A000330: sums of three generalized square pyramidal numbers

**Source:** [OEIS A000330](https://oeis.org/A000330), conjecture by Altug Alkan
**Type:** Lean statement only (open conjecture)
**Status:** 📝 statement in review

## Statement

> Conjecture: Every integer can be represented as a sum of three generalized square pyramidal
> numbers. ... In here "generalized" means negative indices are included.

With P(k) = k(k+1)(2k+1)/6 for every integer k: every integer n is P(a) + P(b) + P(c).

## What is done

- Lean statement written and accepted by the Left To Solve checker
  (`statements/oeis-a000330.lean` in the pull request).
- Computational checks (`check.py`): most |n| ≤ 300 have small representations; some need huge
  cancelling terms (73 = -8905830115 + 53515184 + 8852315004); none found for 128 or 262 with
  |index| ≤ 3000.

## Links

- Left To Solve page: <https://lefttosolve.com/p/oeis-a000330>
- Pull request: <https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/3886>
