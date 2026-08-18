import CORALean.Arithmetic.Float.ContSet.Zonotope.Zonotope

/-!
# `Zonotope.reduce`

The exact layer's `reduce`, rounded: `reduceBy` keeps the generators a partition
names and boxes the rest, `aux_girardMetric` ranks them by what boxing would
cost, and `aux_girardSplit` turns that ranking into the partition.

The ranking is where the two layers must part company. `Tuple.sort` wants a
`LinearOrder`, which no float type has — distinct representations of one value
compare equal each way, so antisymmetry fails — hence `sortPerm`, which asks its
comparator for nothing. It can afford to: `reduceBy_outer` holds at every
partition, so `le` needs no axiom and the metric no rounding argument. A
misranking costs precision alone.
-/

-- Authors:       Tobias Ladner
-- Written:       18-August-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Arithmetic.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n q r : ℕ}

/-- CORA's reduction at a given partition, unchanged in shape and sound for
every one of them.

Nothing is charged to the box: the centre and the kept generators are copied
exactly, and the diagonal block rounds *up*, which only enlarges a result that
was already an over-approximation. -/
def Zonotope.reduceBy (Z : Zonotope 𝕋 n) (part : Split (Fin Z.h) into (Fin q) and (Fin r)) :
    Zonotope 𝕋 n where
  h := q + n
  c := Z.c
  G := fun i => Fin.append (fun l => Z.G i (part.left l))
                  (diagonalBlock (radius fun i l => Z.G i (part.right l)) i)
  E := Z.E

/-- Girard's metric on one generator, `‖g‖₁ - ‖g‖∞`, in `𝕋`. Zero exactly on the
axis-aligned generators, which a box reproduces for free. -/
def Zonotope.aux_girardMetric (Z : Zonotope 𝕋 n) (j : Fin Z.h) : 𝕋 :=
  subDown (sumUp fun i => absolute (Z.G i j)) (maximumOver fun i => absolute (Z.G i j))

/-- The generators Girard's rule keeps at order `o`, against the rest: `(o-1)*n`
of them, which is what leaves room for the box of `n` that replaces the others.

The comparator ranks the larger metric first, so the generators dearest to box
survive — CORA's descending sort. -/
def Zonotope.aux_girardSplit (Z : Zonotope 𝕋 n) (o : ℕ) (hlt : o * n < Z.h) :
    Split (Fin Z.h) into (Fin ((o - 1) * n)) and (Fin (Z.h - (o - 1) * n)) :=
  have hle : (o - 1) * n ≤ Z.h :=
    le_of_lt (lt_of_le_of_lt (Nat.mul_le_mul (Nat.sub_le o 1) (le_refl n)) hlt)
  (Partition.split ((o - 1) * n) (Z.h - (o - 1) * n)).reindex
    ((sortPerm fun j₁ j₂ => le (Z.aux_girardMetric j₂) (Z.aux_girardMetric j₁)).symm.trans
      (finCongr (Nat.add_sub_cancel' hle).symm))

/-- CORA's `reduce(Z, 'girard', o)`: keep the `(o - 1) * n` generators Girard
ranks first and box the rest, which brings the count to `o * n`. Already at that
order or below, nothing happens. -/
def Zonotope.reduceGirard (Z : Zonotope 𝕋 n) (o : ℕ) : Zonotope 𝕋 n :=
  if hlt : o * n < Z.h then Z.reduceBy (Z.aux_girardSplit o hlt) else Z

/-- CORA's `reduce`: to a maximum order, by whichever rule the representation
sees fit. Girard's is the one here, as over ℝ, and which it is goes no further —
a caller names an order and gets an over-approximation. -/
def Zonotope.reduce (Z : Zonotope 𝕋 n) (o : ℕ) : Zonotope 𝕋 n :=
  Z.reduceGirard o

end CORALean.Arithmetic.Float
