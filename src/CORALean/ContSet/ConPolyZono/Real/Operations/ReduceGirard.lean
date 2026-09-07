import CORALean.ContSet.ConPolyZono.Real.Operations.ReduceBy
import CORALean.Global.Sort

/-!
# `ConPolyZono.reduceGirard`

Girard's metric, `‖g‖₁ - ‖g‖∞`, ranks both blocks as one: the `(o-1)·n` best
survive and the rest boxes into `n` fresh independent generators, bringing the
total back to `n·o`.
-/

-- Authors:       Tobias Ladner
-- Written:       05-September-2026
-- Last update:   05-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- Girard's metric on one generator, `‖g‖₁ - ‖g‖∞`, over a bare family so that
either block and their concatenation are ranked by this one line. Zero on the
axis-aligned generators; the max folds from `0`, which no `|G l i|` undercuts. -/
noncomputable def ConPolyZono.aux_girardMetric {m : ℕ} (G : Fin m → Vec ℝ n) (l : Fin m) : ℝ :=
  (∑ i, |G l i|) - Finset.univ.fold max 0 fun i => |G l i|

/-- The `k` generators a metric ranks first, against the rest. Clamped to the
block, so the split is total and no order hypothesis travels with it; sorting is
ascending, so the metric enters negated and the dearest to box rank first. -/
noncomputable def ConPolyZono.aux_girardSplit {m : ℕ} (metric : Fin m → ℝ) (k : ℕ) :
    Split (Fin m) into (Fin (min k m)) ⊕ (Fin (m - min k m)) :=
  (Partition.split (min k m) (m - min k m)).reindex
    ((Tuple.sort fun l => -metric l).symm.trans
      (finCongr (Nat.add_sub_cancel' (min_le_right k m)).symm))

/-- How many of the `K` best-ranked generators overall are dependent: CORA's
joint accounting as one number, `rank` bound by a `let` so the sort runs once.
The cap at `K` never binds and is there to keep the order bound arithmetic. -/
noncomputable def ConPolyZono.aux_girardKeptDep (C : ConPolyZono (Vec ℝ n)) (K : ℕ) : ℕ :=
  let rank := (Tuple.sort fun l =>
    -ConPolyZono.aux_girardMetric (Fin.append C.G C.GI) l).symm
  min K (Finset.univ.filter fun l : Fin C.h =>
    (rank (Fin.castAdd C.q l) : ℕ) < K).card


-- =====================================  MAIN DEFINITION  ====================================== --

/-- CORA's `reduce(cPZ, 'girard', o)`: past `n·o` generators in the two blocks
together, keep the `(o-1)·n` Girard ranks first and box the rest, bringing the
total back to `n·o`. Noncomputable, as ordering reals is. -/
noncomputable def ConPolyZono.reduceGirard (C : ConPolyZono (Vec ℝ n)) (o : ℕ) :
    ConPolyZono (Vec ℝ n) :=
  if o * n < C.h + C.q then
    let K := (o - 1) * n
    let d := C.aux_girardKeptDep K
    C.reduceBy (ConPolyZono.aux_girardSplit (ConPolyZono.aux_girardMetric C.G) d)
      (ConPolyZono.aux_girardSplit (ConPolyZono.aux_girardMetric C.GI) (K - d))
  else C

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
