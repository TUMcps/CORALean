import CORALean.ContSet.PolyZonotope.Float.Operations.Compact
import CORALean.Global.Partition
import CORALean.Global.Sort

/-!
# `PolyZonotope.reduce`

The exact layer's `reduce`, rounded — and the one operation here that the float
layer *runs* where the exact layer only specifies. `PolyZonotope.reduceGirard`
is noncomputable over ℝ because `Tuple.sort` needs a `LinearOrder` on the
metric; `sortPerm` asks its comparator for nothing, so `le` on a machine scalar
suffices. It can afford to: `reduceBy_outer` holds at every partition, so a
misranking costs precision and never soundness.

`reduceBy` charges nothing to the error box. The centre, the kept generators and
their exponent columns are copied exactly, and the diagonal block rounds *up*,
which only enlarges a result that was already an over-approximation. `compact`,
which `reduce` runs first as over ℝ, does charge one: merging two columns adds
their entries.

Running it is what makes the order bound mean what it means over ℝ — a count of
distinct monomials rather than of stored columns, which `plus` and `quadMap`
inflate while the set stands still.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n d r : ℕ}

/-- CORA's reduction at a given partition, unchanged in shape and sound for
every one of them: the kept dependent generators keep their exponent columns,
and the rest become a diagonal block of *independent* generators — independent
because nothing ties a box to the factors any more. -/
def PolyZonotope.reduceBy (PZ : PolyZonotope 𝕋 n)
    (part : Split (Fin PZ.h) into (Fin d) and (Fin r)) : PolyZonotope 𝕋 n where
  p := PZ.p
  h := d
  q := PZ.q + n
  c := PZ.c
  G := fun i l => PZ.G i (part.left l)
  E := fun k l => PZ.E k (part.left l)
  GI := fun i => Fin.append (PZ.GI i)
    (diagonalBlock (radius fun i l => PZ.G i (part.right l)) i)
  err := PZ.err

/-- Girard's metric on one generator, `‖g‖₁ - ‖g‖∞`, in `𝕋`. Zero exactly on the
axis-aligned generators, which a box reproduces for free. -/
def PolyZonotope.aux_girardMetric (PZ : PolyZonotope 𝕋 n) (l : Fin PZ.h) : 𝕋 :=
  subDown (sumUp fun i => absolute (PZ.G i l)) (maximumOver fun i => absolute (PZ.G i l))

/-- The dependent generators Girard's rule keeps at order `o`, against the rest:
`(o-1)*n` of them, which is what leaves room for the box of `n` that replaces
the others.

The comparator ranks the larger metric first, so the generators dearest to box
survive — CORA's descending sort. -/
def PolyZonotope.aux_girardSplit (PZ : PolyZonotope 𝕋 n) (o : ℕ) (hlt : o * n < PZ.h) :
    Split (Fin PZ.h) into (Fin ((o - 1) * n)) and (Fin (PZ.h - (o - 1) * n)) :=
  have hle : (o - 1) * n ≤ PZ.h :=
    le_of_lt (lt_of_le_of_lt (Nat.mul_le_mul (Nat.sub_le o 1) (le_refl n)) hlt)
  (Partition.split ((o - 1) * n) (PZ.h - (o - 1) * n)).reindex
    ((sortPerm fun l₁ l₂ => le (PZ.aux_girardMetric l₂) (PZ.aux_girardMetric l₁)).symm.trans
      (finCongr (Nat.add_sub_cancel' hle).symm))

/-- CORA's `reduce(pZ, 'girard', o)` on the dependent block: keep the `(o-1)*n`
generators Girard ranks first and box the rest. Already at that order or below,
nothing happens. -/
def PolyZonotope.reduceGirard (PZ : PolyZonotope 𝕋 n) (o : ℕ) : PolyZonotope 𝕋 n :=
  if hlt : o * n < PZ.h then PZ.reduceBy (PZ.aux_girardSplit o hlt) else PZ

/-- CORA's `reduce`: to a maximum order, by whichever rule the representation
sees fit. Girard's is the one here, as over ℝ, and which it is goes no further —
a caller names an order and gets an over-approximation. -/
def PolyZonotope.reduce (PZ : PolyZonotope 𝕋 n) (o : ℕ) : PolyZonotope 𝕋 n :=
  PZ.compact.reduceGirard o

end CORALean.Float
