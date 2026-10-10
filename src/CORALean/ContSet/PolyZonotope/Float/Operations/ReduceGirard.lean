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


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

-- file-local: only `reduceGirard` below needs these
/-- CORA's `[G, GI]`: the two blocks as one matrix, which is what it ranks.
Generators carry the second index here, so concatenating them appends along a
row. -/
def PolyZonotope.aux_concatGens (pZ : PolyZonotope 𝕋 n) : Mat 𝕋 n (pZ.h + pZ.q) :=
  fun i => Fin.append (fun l => pZ.G l i) (fun j => pZ.GI j i)

/-- How many of the `K` best-ranked generators overall are dependent: CORA's
joint accounting as one number, `rank` bound by a `let` so the sort runs once
over generators nothing memoizes. The cap at `K` never binds. -/
def PolyZonotope.aux_girardKeptDep (pZ : PolyZonotope 𝕋 n) (K : ℕ) : ℕ :=
  let metric := PolyZonotope.girardMetric pZ.aux_concatGens
  let rank := (sortPerm fun l₁ l₂ => le (metric l₂) (metric l₁)).symm
  min K (Finset.univ.filter fun l : Fin pZ.h =>
    (rank (Fin.castAdd pZ.q l) : ℕ) < K).card


-- =====================================  MAIN DEFINITION  ====================================== --

/-- CORA's `reduce(pZ, 'girard', o)`: past `n·o` generators in the two blocks
together, keep the `(o-1)·n` Girard ranks first and box the rest, bringing the
total back to `n·o`. At that order or below, nothing happens. -/
def PolyZonotope.reduceGirard (pZ : PolyZonotope 𝕋 n) (o : ℕ) : PolyZonotope 𝕋 n :=
  if o * n < pZ.h + pZ.q then
    let K := (o - 1) * n
    let d := pZ.aux_girardKeptDep K
    pZ.reduceBy (PolyZonotope.girardSplit (PolyZonotope.girardMetric fun i l => pZ.G l i) d)
      (PolyZonotope.girardSplit (PolyZonotope.girardMetric fun i j => pZ.GI j i) (K - d))
  else pZ

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
