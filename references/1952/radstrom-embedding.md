# An embedding theorem for spaces of convex sets

```bibtex
@article{radstrom1952embedding,
  author = {Rådström, H.},
  title = {An embedding theorem for spaces of convex sets},
  journal = {Proceedings of the American Mathematical Society},
  year = {1952}
}
```

**Source:** https://web.archive.org/web/20170824215421id_/http://www.ams.org/journals/proc/1952-003-01/S0002-9939-1952-0045938-2/S0002-9939-1952-0045938-2.pdf (the AMS's own copy, archived; ams.org itself answers scripts with a bot challenge)  
**Inventory:** confirmed

The cancellation law: `X + E ⊆ Y + E` gives `X ⊆ Y` when `Y` is convex and
closed and `E` is bounded and nonempty. Mathlib does not have it, so
`Global/Radstrom.lean` proves it, and it is what turns an outer approximation
with a known error into an inner one, which is where every inner approximation
here starts. The paper proves it on the way to its real subject, embedding a
cone of convex sets isometrically in a normed space, which CORALean has no use
for.

## Results

| Result | What it says | In CORALean | Class |
|---|---|---|---|
| `Thm. 1` | A: a commutative semigroup with cancellation embeds in a group, minimally. B: a multiplication by non-negative scalars satisfying 4-7 extends to real scalars and makes that group a vector space. C: a translation-invariant, homogeneous metric with continuous operations extends to a norm on it. | n/a — the construction of a group, vector space and norm from a cancellative semigroup: the embedding, which CORALean does not do | `not-covered` |
| `Lemma 1` | In a real normed linear space, with `B` closed and convex and `X` bounded, `A + X ⊆ B + X` implies `A ⊆ B`. | [`Radstrom.lean`](../../src/CORALean/Global/Radstrom.lean) — `radstrom_cancel`, with `X` also nonempty, which the lemma needs and does not print: see `## Findings` | `underspecified` — fails only at `X = ∅`, which the paper's setting (nonempty sets) excludes; `X` nonempty is supplied |
| `Lemma 2` | In a real normed linear space, with `A` and `B` closed and convex and `X` bounded, `A + X = B + X` implies `A = B`. | [`RadstromEq.lean`](../../src/CORALean/Global/RadstromEq.lean) — `radstrom_cancel_eq`, with `X` nonempty as for `Lemma 1` | `underspecified` — fails only at `X = ∅`, which the paper's setting (nonempty sets) excludes; `X` nonempty is supplied |
| `Lemma 3` | In a real normed linear space, with `A` and `B` convex, `A + λS` and `B + λS` closed for all `λ ≥ 0` (`S` the unit ball) and `X` bounded, `d(A, B) = d(A + X, B + X)` for the Hausdorff distance `d`. | [`RadstromHausdorff.lean`](../../src/CORALean/Global/RadstromHausdorff.lean) — `hausdorffEDist_add_eq`, at `Metric.hausdorffEDist` so that an infinite distance between unbounded convex sets is not read as `0`, and with `X` nonempty as for `Lemma 1` | `underspecified` — fails only at `X = ∅`, which the paper's setting (nonempty sets) excludes; `X` nonempty is supplied |
| `Thm. 2` | A family `M` of closed bounded convex sets in a real normed space, closed under sum and non-negative scaling, with `A + S` closed for each member and metrized by the Hausdorff distance, embeds as a convex cone in a real normed space, isometrically and preserving both operations, and minimally. Compact convex sets, finite-dimensional ones and, in a reflexive space, closed bounded convex ones are examples. | n/a — the embedding itself, which CORALean does not do; the two facts it rests on that are about sets, `Lemma 2` and `Lemma 3`, are above | `not-covered` |

## Findings

**`Lemma 1`, `Lemma 2` and `Lemma 3` need `X` nonempty, and do not say so.** At
`X = ∅`, `A + X = B + X = ∅` whatever `A` and `B` are, so `Lemma 1` would put
every set inside every closed convex one, and `Lemma 3` would make every
distance `0`. The proof of `Lemma 1` opens with "given any `x₁ ∈ X`", which is
where the hypothesis is used. `Lemma 2` is `Lemma 1` twice, and `Lemma 3` uses
`Lemma 1` to cancel `X`, so both inherit it. Nothing in the paper goes wrong
because of this: `Thm. 2` applies the lemmas to members of `M`, which are never
empty in any of its examples. But the lemmas as printed are false, and all three
here carry the hypothesis.
