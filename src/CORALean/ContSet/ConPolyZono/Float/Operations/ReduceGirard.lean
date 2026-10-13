module

public import CORALean.ContSet.ConPolyZono.Float.Operations.ReduceBy
public import CORALean.Global.Sort

@[expose] public section

/-!
# `ConPolyZono.reduceGirard`, over a floating-point scalar

Split out of `Reduce.lean` (issue #62): read again by `Theorems/
ReduceGirardOrderLe.lean` and `Theorems/ReduceGirardOuter.lean`, both outside
this file.
-/

-- Authors:       Claude Opus 5
-- Written:       06-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

-- file-local: only `reduceGirard` below needs these
/-- Girard's metric on one generator, `‖g‖₁ - ‖g‖∞`, in `𝕋`, over a bare family
so that either block and their concatenation are ranked by this one line. Zero
on the axis-aligned generators, which a box reproduces for free. -/
def ConPolyZono.aux_girardMetric {m : ℕ} (G : Fin m → Vec 𝕋 n) (l : Fin m) : 𝕋 :=
  subDown (sumUp fun i => absolute (G l i)) (maximumOver fun i => absolute (G l i))

/-- CORA's `[G, GI]`: the two blocks as one family, which is what it ranks. -/
def ConPolyZono.aux_concatGens (cPZ : ConPolyZono 𝕋 (Vec 𝕋 n)) : Fin (cPZ.h + cPZ.q) → Vec 𝕋 n :=
  Fin.append cPZ.G cPZ.GI

/-- The `k` generators a metric ranks first, against the rest. Clamped to the
block, so the split is total and no order hypothesis travels with it; the
comparator ranks the larger metric first, CORA's descending sort. -/
def ConPolyZono.aux_girardSplit {m : ℕ} (metric : Fin m → 𝕋) (k : ℕ) :
    Split (Fin m) into (Fin (min k m)) ⊕ (Fin (m - min k m)) :=
  (Partition.split (min k m) (m - min k m)).reindex
    ((sortPerm fun l₁ l₂ => le (metric l₂) (metric l₁)).symm.trans
      (finCongr (Nat.add_sub_cancel' (min_le_right k m)).symm))

/-- How many of the `K` best-ranked generators overall are dependent: CORA's
joint accounting as one number, `rank` bound by a `let` so the sort runs once
over generators nothing memoizes. The cap at `K` never binds. -/
def ConPolyZono.aux_girardKeptDep (cPZ : ConPolyZono 𝕋 (Vec 𝕋 n)) (K : ℕ) : ℕ :=
  let metric := ConPolyZono.aux_girardMetric cPZ.aux_concatGens
  let rank := (sortPerm fun l₁ l₂ => le (metric l₂) (metric l₁)).symm
  min K (Finset.univ.filter fun l : Fin cPZ.h =>
    (rank (Fin.castAdd cPZ.q l) : ℕ) < K).card


-- =====================================  MAIN DEFINITION  ====================================== --

/-- CORA's `reduce(cPZ, 'girard', o)`: past `n·o` generators in the two blocks
together, keep the `(o-1)·n` Girard ranks first and box the rest, bringing the
total back to `n·o`. At that order or below, nothing happens. -/
def ConPolyZono.reduceGirard (cPZ : ConPolyZono 𝕋 (Vec 𝕋 n)) (o : ℕ) : ConPolyZono 𝕋 (Vec 𝕋 n) :=
  if o * n < cPZ.h + cPZ.q then
    let K := (o - 1) * n
    let d := cPZ.aux_girardKeptDep K
    cPZ.reduceBy (ConPolyZono.aux_girardSplit (ConPolyZono.aux_girardMetric cPZ.G) d)
      (ConPolyZono.aux_girardSplit (ConPolyZono.aux_girardMetric cPZ.GI) (K - d))
  else cPZ

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
