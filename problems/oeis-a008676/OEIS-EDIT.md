# Proposed OEIS edit for A008676

Draft only, not submitted. To submit: sign in at oeis.org, open A008676, click **edit**, change the
lines below, fill in the reason, and submit for review. Signed as Rhet Porter (OEIS requires
contributors to sign with their real name).

Date format used by OEIS: `Nov 27 2026`.

**OEIS AI policy** ([Use of AI for OEIS Submissions](https://oeis.org/wiki/Use_of_AI_for_OEIS_Submissions)):
the human submitter is responsible for correctness and must be able to explain the result; it
prohibits "using AI to generate the full text of comments", pasting AI-generated text into the
editors' Pink Box discussions, and listing an AI tool as an author or co-author. So treat the text
below as notes: understand each proof, then write the comments in your own words before
submitting, and answer any editor questions yourself.

---

## Easiest way: replace two whole boxes

1. Open **https://oeis.org/edit?seq=A008676** and choose **Sign in with GitHub** (no password to type
   if you are signed in to GitHub). You land on the edit page for A008676.
2. Find the **Comments** box. Select everything in it and replace it with the block below.
   (This keeps Baxter's and Perry's comments unchanged, removes Layman's "Conjecture" line, and
   updates Layman's multiset comment and Wiseman's comment.)
3. Find the **Formula** box. Select everything in it and replace it with the block below.
   (This keeps the three existing formulas and adds Layman's formula with its proof.)
4. Paste the reason for change, then submit.

If the page looks different from this (for example one box per line instead of one box per
field), use the line-by-line sections further down instead.

**Comments box (replace all):**

```
a(n) gives the number of partitions of n using only the parts 3 and 5.  e.g. a(25)=2: 5+5+5+5+5 and 5+5+3+3+3+3+3+3. - _Andrew Baxter_, Jun 20 2011
a(n) gives the number of partitions of n+8 involving both a 3 and a 5. e.g. a(25)=2 and we may write 33 as 5+5+5+5+5+5+3 and 5+5+5+3+3+3+3+3+3. 11*3 doesn't count as no 5 is involved. - _Jon Perry_, Jul 03 2004
For n >= 1, a(n) is also the number of distinct multisets of n-1 integers, each of which is -2, +3, or +4, such that the sum of the members of each multiset is 2. E.g., for n=5, the multiset {-2,-2,3,3}, and no others, of n-1=4 members, sums to 2, so a(5)=1. - _John W. Layman_, Sep 23 2009 [Proof: if the multiset has p copies of -2, q of +3 and r of +4, then p + q + r = n - 1 and -2p + 3q + 4r = 2 give 5q + 6r = 2n, so q = 2s with 3r + 5s = n; conversely each such (r, s) gives a valid multiset. - _Rhet Porter_, Nov 27 2026]
a(n-8) is the number of ordered triples of positive integers summing to n such that 2x = 3y + 4z, ranked by A357489 (if zero entries are allowed, the number of such triples summing to n is a(n)). An unordered version appears to be A357849, ranked by A358102. - _Gus Wiseman_, Nov 04 2022 [Corrected and proved: x + y + z = n and 2x = 3y + 4z force y = 2u, x = 3u + 2z and n = 5u + 3z; with u, z >= 1 this is a partition n - 8 = 5(u-1) + 3(z-1). For example, the smallest such triple is (5, 2, 1), summing to 8, matching a(0) = 1. - _Rhet Porter_, Nov 27 2026]
```

**Formula box (replace all):**

```
G.f.: 1/( (1-x^3) * (1-x^5) ).
a(n) = a(n-3) + a(n-5) - a(n-8), a(0)=a(3)=a(5)=a(6)=1, a(1)=a(2)=a(4) =a(6)=a(7)=0.
a(n) = floor((2*n+5)/5) - floor((n+2)/3). - _Tani Akinari_, Aug 07 2013
a(n) = floor(2*(n + 3)/3) - floor(3*(n + 3)/5) (conjectured by _John W. Layman_, Sep 23 2009). Proof: both sides increase by 1 when n is replaced by n + 15. For the left side, the solutions of 3i + 5j = n + 15 with i >= 5 correspond to those of 3i + 5j = n via i -> i - 5, and exactly one solution has i <= 4, since 3i runs over all residues mod 5. For the right side, the two floors increase by 10 and 9. Both sides agree for n = 0..14. The same argument proves the formula of Tani Akinari in this entry. Both formulas also follow from Popoviciu's theorem on the number of solutions of ax + by = n. - _Rhet Porter_, Nov 27 2026
```

**Reason for change:**

```
Proved Layman's conjecture (2009) and his multiset comment; corrected Wiseman's comment, whose
triples (compositions, positive parts, as in A357489) are counted by a(n-8), not a(n).
Proofs are short and included (the floor formula also follows from Popoviciu's theorem); also
checked numerically and formalized in Lean 4.
```

---

## Line by line (same changes)

### 1. Layman's conjecture (move from %C to %F, with proof)

**Remove this %C line:**

```
Conjecture: a(n) = Floor(2*(n + 3)/3) - Floor(3*(n + 3)/5). - _John W. Layman_, Sep 23 2009
```

**Add this %F line:**

```
a(n) = floor(2*(n + 3)/3) - floor(3*(n + 3)/5) (conjectured by _John W. Layman_, Sep 23 2009). Proof: both sides increase by 1 when n is replaced by n + 15. For the left side, the solutions of 3i + 5j = n + 15 with i >= 5 correspond to those of 3i + 5j = n via i -> i - 5, and exactly one solution has i <= 4, since 3i runs over all residues mod 5. For the right side, the two floors increase by 10 and 9. Both sides agree for n = 0..14. The same argument proves the formula of Tani Akinari in this entry. Both formulas also follow from Popoviciu's theorem on the number of solutions of ax + by = n. - _Rhet Porter_, Nov 27 2026
```

### 2. Layman's multiset comment (state as fact, with proof)

**Replace this %C line:**

```
Also, it appears that a(n) gives the number of distinct multisets of n-1 integers, each of which is -2, +3, or +4, such that the sum of the members of each multiset is 2. E.g., for n=5, the multiset {-2,-2,3,3}, and no others, of n-1=4 members, sums to 2, so a(5)=1. - _John W. Layman_, Sep 23 2009
```

**with:**

```
For n >= 1, a(n) is also the number of distinct multisets of n-1 integers, each of which is -2, +3, or +4, such that the sum of the members of each multiset is 2. E.g., for n=5, the multiset {-2,-2,3,3}, and no others, of n-1=4 members, sums to 2, so a(5)=1. - _John W. Layman_, Sep 23 2009 [Proof: if the multiset has p copies of -2, q of +3 and r of +4, then p + q + r = n - 1 and -2p + 3q + 4r = 2 give 5q + 6r = 2n, so q = 2s with 3r + 5s = n; conversely each such (r, s) gives a valid multiset. - _Rhet Porter_, Nov 27 2026]
```

### 3. Wiseman's comment (correct the index)

**Replace this %C line:**

```
Appears to be the number of ordered triples summing to n such that 2x = 3y + 4z, ranked by A357489. An unordered version appears to be A357849, ranked by A358102. - _Gus Wiseman_, Nov 04 2022
```

**with:**

```
a(n-8) is the number of ordered triples of positive integers summing to n such that 2x = 3y + 4z, ranked by A357489 (if zero entries are allowed, the number of such triples summing to n is a(n)). An unordered version appears to be A357849, ranked by A358102. - _Gus Wiseman_, Nov 04 2022 [Corrected and proved: x + y + z = n and 2x = 3y + 4z force y = 2u, x = 3u + 2z and n = 5u + 3z; with u, z >= 1 this is a partition n - 8 = 5(u-1) + 3(z-1). For example, the smallest such triple is (5, 2, 1), summing to 8, matching a(0) = 1. - _Rhet Porter_, Nov 27 2026]
```

## Reason for change (edit form)

```
Proved Layman's conjecture (2009) and his multiset comment; corrected Wiseman's comment, whose
triples (compositions, positive parts, as in A357489) are counted by a(n-8), not a(n).
Proofs are short and included (the floor formula also follows from Popoviciu's theorem); also
checked numerically and formalized in Lean 4.
```

## Optional link (%H), once the Lean proofs are pushed

```
Rhet Porter, <a href="https://github.com/rhetoricalrhet/math/tree/main/problems/oeis-a008676">Proofs of the comments, with Lean 4 formalization</a>
```
