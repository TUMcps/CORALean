import CORALean.ContSet.PolyZonotope.Float.Operations.GirardSplit
import CORALean.ContSet.PolyZonotope.Float.Operations.ReduceBy

/-!
# `PolyZonotope.reduceGirard`

Split out of `Reduce.lean` (issue #62): each `reduce`-family rule now earns its
own file, as CORA gives each a file too.

The two blocks are ranked as one, which is what bounds the result:
`Theorems/ReduceOrder.lean` reads `n·o` off the two clamped budgets and never
off the ranking. `aux_girardKeptDep` is the joint accounting as one number.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   06-September-2026
-- Last revision: ---

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}

-- file-local: only `reduceGirard` below needs these
/-- CORA's `[G, GI]`: the two blocks as one matrix, which is what it ranks.
Generators carry the second index here, so concatenating them appends along a
row. -/
def PolyZonotope.aux_concatGens (PZ : PolyZonotope 𝕋 n) : Mat 𝕋 n (PZ.h + PZ.q) :=
  fun i => Fin.append (PZ.G i) (PZ.GI i)

/-- How many of the `K` best-ranked generators overall are dependent: CORA's
joint accounting as one number, `rank` bound by a `let` so the sort runs once
over generators nothing memoizes. The cap at `K` never binds. -/
def PolyZonotope.aux_girardKeptDep (PZ : PolyZonotope 𝕋 n) (K : ℕ) : ℕ :=
  let metric := PolyZonotope.girardMetric PZ.aux_concatGens
  let rank := (sortPerm fun l₁ l₂ => le (metric l₂) (metric l₁)).symm
  min K (Finset.univ.filter fun l : Fin PZ.h =>
    (rank (Fin.castAdd PZ.q l) : ℕ) < K).card

/-- CORA's `reduce(pZ, 'girard', o)`: past `n·o` generators in the two blocks
together, keep the `(o-1)·n` Girard ranks first and box the rest, bringing the
total back to `n·o`. At that order or below, nothing happens. -/
def PolyZonotope.reduceGirard (PZ : PolyZonotope 𝕋 n) (o : ℕ) : PolyZonotope 𝕋 n :=
  if o * n < PZ.h + PZ.q then
    let K := (o - 1) * n
    let d := PZ.aux_girardKeptDep K
    PZ.reduceBy (PolyZonotope.girardSplit (PolyZonotope.girardMetric PZ.G) d)
      (PolyZonotope.girardSplit (PolyZonotope.girardMetric PZ.GI) (K - d))
  else PZ

end CORALean.Float
