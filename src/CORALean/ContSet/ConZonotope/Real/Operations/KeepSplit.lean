module

public import CORALean.ContSet.ConZonotope.Real.ConZonotope
public import CORALean.ContSet.HPolytope.Real.Operations.Basic
public import CORALean.ContSet.ConZonotope.Real.Operations.KeepMetric
public import CORALean.Global.Partition
public import CORALean.Global.Sort
public import Mathlib.Data.Fin.Tuple.Sort

@[expose] public section

/-!
# `ConZonotope.keepSplit`

Which generators `reduceKeep` keeps: first the ones the constraints use most (the
constraint's own `HPolytope.colWeight` at the generator's unit vector, largest first), so that
unconstrained generators, whose removal loses nothing but the usual box, are boxed before any
constrained one; ties are broken by Girard's metric, dearest to box first, as `girardSplit` does.
The ranking is by lexicographic key, sorted ascending, hence both entries negated.
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   19-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `(o - 1) * n` generators kept, the rest boxed, ranked by constraint involvement
and then Girard's metric. -/
noncomputable def ConZonotope.keepSplit (cZ : ConZonotope (Vec ℝ n)) (o : ℕ)
    (hlt : o * n < cZ.h) :
    Split (Fin cZ.h) into (Fin ((o - 1) * n)) ⊕ (Fin (cZ.h - (o - 1) * n)) :=
  have hle : (o - 1) * n ≤ cZ.h :=
    le_of_lt (lt_of_le_of_lt (Nat.mul_le_mul (Nat.sub_le o 1) (le_refl n)) hlt)
  (Partition.split ((o - 1) * n) (cZ.h - (o - 1) * n)).reindex
    ((Tuple.sort fun j =>
        toLex (-cZ.P.colWeight (Pi.single j (1 : ℝ) : Vec ℝ cZ.h), -cZ.keepMetric j)).symm.trans
      (finCongr (Nat.add_sub_cancel' hle).symm))

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
