# TODO

What is outstanding and what is done. Update this file at the end of every piece of work.

## Waiting on others

- [ ] [PR #3886](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/3886): A000330 statement, in review at Left To Solve
- [ ] [PR #3911](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/3911): A000051 statement, in review at Left To Solve
- [ ] [PR #3956](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/3956): A000225 statement, in review at Left To Solve

## Next actions

- [ ] **When #3911 is merged:** submit the A000051 proof to Left To Solve. Claim
      `oeis-a000051` from the desk, write `proofs/oeis-a000051.lean` in the fork as
      `theorem OMA.solution : type_of% @OMA.S_oeis_a000051.main` using the lemmas in
      `lean/Math/OEIS/A000051.lean`, run `tools/check.sh`, open the PR, release the claim.
- [ ] **When any PR is merged or rejected:** update its row in the README table and the problem's
      README; tick it off above.
- [ ] Add the `Model:` line on PR #3886 (and #3911, #3956 if not already done), by editing the
      PR description on GitHub.
- [ ] **A008676 OEIS edit:** read `problems/oeis-a008676/OEIS-EDIT.md`, understand the proofs, and
      submit the edit in your own words (OEIS AI policy forbids AI-written comment text).
- [ ] Add repo topics on GitHub: `lean4`, `mathematics`, `formal-verification`, `conjectures`.
- [ ] Profile README (`rhetoricalrhet/rhetoricalrhet`): needs a one-line intro from me first.
- [ ] Optional: save the Lean/Mathlib install as the cloud environment's setup script, so new
      sessions set themselves up automatically.

## Ideas (not started)

- A000225 "only if" direction (open): look for a covering with period > 160, or a reason none
  can exist; see `problems/oeis-a000225/NOTES.md`.
- Prove A000330 (open; research-level).
- Formalize more OEIS conjectures (`lefttosolve.com/api/problems?kind=unformalized`).
- Check whether A000330's conjecture has a published proof or counterexample (128 and 262 had no
  representation with |index| ≤ 3000).

## Done

- 2026-11-27: Forked `open-math-agents`; set commits to the GitHub noreply email.
- 2026-11-27: Formalized and submitted A000330 (PR #3886), A000051 (PR #3911), A000225 (PR #3956).
- 2026-11-27: Created this repo: README, status table, templates, Lean project, CI.
- 2026-11-27: A000051 fully proved in Lean (`lean/Math/OEIS/A000051.lean`), CI green.
- 2026-11-27: A000225 "if" direction proved in Lean (`lean/Math/OEIS/A000225.lean`); partial
  result: Fermat-style coverings only work for powers of 2; no covering with period ≤ 160.
- 2026-11-27: A008676: proved Layman's formula and multiset comment, corrected Wiseman's comment
  (positive triples give a(n-8)); all in Lean (`lean/Math/OEIS/A008676.lean`); OEIS edit drafted.

## Resuming in a new session

- Cloud environment `open-math` allows the hosts needed (Lean releases, Mathlib cache,
  lefttosolve.com, GitHub).
- Setup: install elan, clone `google-deepmind/formal-conjectures` at the commit in the fork's
  `data/catalog.json` (`9097e2f`), run `lake exe cache get` there (about 7 GB).
- `gh` is not signed in on cloud sessions: open PRs with a prefilled
  `github.com/.../compare/...?expand=1` link and create them from the browser.
- Draft branches `oma/oeis-*` on the fork can be deleted once their PRs are merged.
