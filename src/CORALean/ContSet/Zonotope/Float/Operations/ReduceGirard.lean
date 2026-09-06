import CORALean.ContSet.Zonotope.Float.Operations.ReduceBy
import CORALean.Global.Sort

/-!
# `Zonotope.reduceGirard`

The ranking is where the two layers part company. `Tuple.sort` wants a
`LinearOrder`, which no float type has — distinct representations of one value
compare equal each way, so antisymmetry fails — hence `sortPerm`, which asks
its comparator for nothing. It can afford to, since `reduceBy_outer` holds at
every partition: a misranking costs precision alone.
-/

-- Authors:       Tobias Ladner
-- Written:       18-August-2026
-- Last update:   05-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- Girard's metric on one generator, `‖g‖₁ - ‖g‖∞`, in `𝕋`. Zero exactly on the
axis-aligned generators, which a box reproduces for free. -/
def Zonotope.aux_girardMetric (Z : Zonotope 𝕋 n) (j : Fin Z.h) : 𝕋 :=
  subDown (sumUp fun i => absolute (Z.G i j)) (maximumOver fun i => absolute (Z.G i j))

/-- The generators Girard's rule keeps at order `o`, against the rest: `(o-1)*n`
of them, leaving room for the box of `n`. The comparator ranks the larger metric
first, so the generators dearest to box survive — CORA's descending sort. -/
def Zonotope.aux_girardSplit (Z : Zonotope 𝕋 n) (o : ℕ) (hlt : o * n < Z.h) :
    Split (Fin Z.h) into (Fin ((o - 1) * n)) and (Fin (Z.h - (o - 1) * n)) :=
  have hle : (o - 1) * n ≤ Z.h :=
    le_of_lt (lt_of_le_of_lt (Nat.mul_le_mul (Nat.sub_le o 1) (le_refl n)) hlt)
  (Partition.split ((o - 1) * n) (Z.h - (o - 1) * n)).reindex
    ((sortPerm fun j₁ j₂ => le (Z.aux_girardMetric j₂) (Z.aux_girardMetric j₁)).symm.trans
      (finCongr (Nat.add_sub_cancel' hle).symm))


-- =====================================  MAIN DEFINITION  ====================================== --

/-- CORA's `reduce(Z, 'girard', o)`: keep the `(o - 1) * n` generators Girard
ranks first and box the rest, which brings the count to `o * n`. Already at that
order or below, nothing happens. -/
def Zonotope.reduceGirard (Z : Zonotope 𝕋 n) (o : ℕ) : Zonotope 𝕋 n :=
  if hlt : o * n < Z.h then Z.reduceBy (Z.aux_girardSplit o hlt) else Z

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
