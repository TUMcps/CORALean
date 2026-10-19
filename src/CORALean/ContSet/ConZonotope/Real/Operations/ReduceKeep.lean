module

public import CORALean.ContSet.ConZonotope.Real.ConZonotope
public import CORALean.ContSet.ConZonotope.Real.Operations.ReduceKeepBy
public import CORALean.ContSet.HPolytope.Real.Operations.Basic
public import CORALean.Global.Partition
public import CORALean.Global.Sort
public import Mathlib.Data.Fin.Tuple.Sort

@[expose] public section

/-!
# `ConZonotope.reduceKeep`

A reduction that keeps the constraints. Above the requested order, `aux_keepSplit` ranks
the generators, `reduceKeepBy` boxes the lowest ranked and projects the constraints
onto what is kept; at or below it nothing happens.

Beside `ConZonotope.reduce`, not in place of it: that one drops `P` and reduces by
Girard's metric alone, this one ranks constrained generators first, so neither set
contains the other in general. What this one buys is that every constraint on a
kept coefficient survives, up to the slack `keepSlack` charges for a dropped one.
No linear program runs in either.
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- `‖g‖₁ - ‖g‖∞` of generator `j`; the max folds from `0`, which no `|G j i|` undercuts. -/
noncomputable def ConZonotope.aux_keepMetric (cZ : ConZonotope (Vec ℝ n)) (j : Fin cZ.h) : ℝ :=
  (∑ i, |cZ.G j i|) - Finset.univ.fold max 0 fun i => |cZ.G j i|

/-- `(o - 1) * n` generators kept, the rest boxed, ranked by constraint involvement
and then Girard's metric. -/
noncomputable def ConZonotope.aux_keepSplit (cZ : ConZonotope (Vec ℝ n)) (o : ℕ)
    (hlt : o * n < cZ.h) :
    Split (Fin cZ.h) into (Fin ((o - 1) * n)) ⊕ (Fin (cZ.h - (o - 1) * n)) :=
  have hle : (o - 1) * n ≤ cZ.h :=
    le_of_lt (lt_of_le_of_lt (Nat.mul_le_mul (Nat.sub_le o 1) (le_refl n)) hlt)
  (Partition.split ((o - 1) * n) (cZ.h - (o - 1) * n)).reindex
    ((Tuple.sort fun j =>
        toLex (-cZ.P.colWeight (Pi.single j (1 : ℝ) : Vec ℝ cZ.h), -cZ.aux_keepMetric j)).symm.trans
      (finCongr (Nat.add_sub_cancel' hle).symm))


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Above order `o`, box all but `(o - 1) * n` generators and keep the constraints on
the rest; at or below it, the identity. -/
noncomputable def ConZonotope.reduceKeep (cZ : ConZonotope (Vec ℝ n)) (o : ℕ) :
    ConZonotope (Vec ℝ n) :=
  if hlt : o * n < cZ.h then cZ.reduceKeepBy (cZ.aux_keepSplit o hlt) else cZ

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
