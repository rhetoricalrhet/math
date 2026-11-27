# math

I liked math as a boy, but the culture around me didn't value it.

Formal statements, proofs and experiments on open conjectures in number theory, combinatorics
and beyond. Lean 4 formalizations alongside reproducible search and verification scripts.

Curated by [rhetoricalrhet](https://github.com/rhetoricalrhet). Results contributed elsewhere
are credited per result in the table.

## Status

| Problem | Type | Status | Links |
|---|---|---|---|
| [OEIS A000330](problems/oeis-a000330/): every integer is a sum of three generalized square pyramidal numbers | Lean statement only | 📝 statement in review | [PR #3886](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/3886) · [page](https://lefttosolve.com/p/oeis-a000330) |
| [OEIS A000051](problems/oeis-a000051/): 2^n + 1 is the permanent of a Toeplitz matrix | Known result formalized | ✅ fully Lean-checked · statement in review | [PR #3911](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/3911) · [page](https://lefttosolve.com/p/oeis-a000051) |
| [OEIS A000225](problems/oeis-a000225/): a compositeness characterization of 2^n - 1 | Open conjecture | 🟡 partly in Lean (one direction proved) · statement in review | [PR #3956](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/3956) · [page](https://lefttosolve.com/p/oeis-a000225) |
| [OEIS A008676](problems/oeis-a008676/): partitions into 3s and 5s; three conjectured comments | Open conjecture (open on OEIS; follows from known results) | ✍️ written proof · one comment corrected | [OEIS](https://oeis.org/A008676) |

**Status:** 💡 idea · 🔍 exploring · 📝 statement in review · ✍️ written proof · 🟡 partly in Lean ·
✅ fully Lean-checked · ❌ disproved/counterexample

**Type:** open conjecture · known result formalized · Lean statement only · reduction/partial

A Lean statement is the problem written precisely in Lean, with no proof. Formalizing a known
result is not the same as solving an open problem, and the table says which is which.

## Layout

```
problems/<id>/        one folder per problem: README.md, NOTES.md, optional check.py
templates/problem/    copy this to start a new problem
lean/                 Lean 4 + Mathlib project; only complete proofs (CI fails on sorry)
TODO.md               what is outstanding and what is done
```

The layout is meant to grow: new kinds of work (papers, write-ups, other tools, other
languages) get their own top-level folder next to these, and new problems only need a copy of
`templates/problem/`. `check.py` scripts are computational evidence (small cases, searches),
not proofs.

## Lean

`lean/` uses Lean `v4.33.1` and Mathlib `v4.33.1`, the same versions as Left To Solve
(google-deepmind/formal-conjectures at `9097e2f`), so proofs here also check there.

```
cd lean && lake exe cache get && lake build
```

## License

Code and Lean: [MIT](LICENSE). Written mathematics (Markdown): [CC BY 4.0](LICENSE-TEXT.md).
Quoted problem statements are credited to their sources.
