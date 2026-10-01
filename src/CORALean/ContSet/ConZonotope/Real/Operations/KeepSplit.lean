import CORALean.ContSet.ConZonotope.Real.Operations.KeepInvolvement
import CORALean.ContSet.ConZonotope.Real.Operations.KeepMetric
import CORALean.Global.Partition
import CORALean.Global.Sort

/-!
# `ConZonotope.keepSplit`

Which generators `reduceKeep` keeps: first the ones the constraints use most
(`keepInvolvement`, largest first), so that unconstrained generators, whose removal
loses nothing but the usual box, are boxed before any constrained one; ties are
broken by Girard's metric, dearest to box first, as `girardSplit` does. The
ranking is by lexicographic key, sorted ascending, hence both entries negated.
-/

-- Authors:       Tobias Ladner
-- Written:       01-October-2026
-- Last update:   ---
-- Last revision: ---


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
    ((Tuple.sort fun j => toLex (-cZ.keepInvolvement j, -cZ.keepMetric j)).symm.trans
      (finCongr (Nat.add_sub_cancel' hle).symm))

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
