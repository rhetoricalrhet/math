# OEIS A000225: a characterization of 2^n - 1

**Source:** [OEIS A000225](https://oeis.org/A000225), conjecture by Chai Wah Wu
**Type:** Lean statement only (open conjecture)
**Status:** 📝 statement in review

## Statement

> Conjecture: except for a(2)=3, numbers m such that 2^(m+1) - 2^j - 2^k - 1 is composite for all
> 0 <= j < k <= m.

So: apart from 3, the numbers 2^n - 1 are exactly the m for which every such number is not prime.
"Composite" is read as "not prime": for m = 1 one of the numbers is 0, and the strict reading
would make the conjecture false as written.

## What is done

- Lean statement written and accepted by the Left To Solve checker.
- Computational check (`check.py`): the m in 0..80 with the property are 0, 1, 7, 15, 31, 63.

## Links

- Left To Solve page: <https://lefttosolve.com/p/oeis-a000225>
- Pull request: <https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/3956>
