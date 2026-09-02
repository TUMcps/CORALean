import CORALean.ContSet.PolyZonotope.Real.Operations.Compact
import CORALean.Global.Partition
import CORALean.Global.Sort

/-!
# `PolyZonotope.reduce`

CORA's `@polyZonotope/reduce`: bring the dependent generator count down to a
maximum order. `reduceBy` keeps the dependent generators a partition names and
boxes the rest into *independent* generators; Girard's is the rule that chooses
the partition, ranking by what boxing a generator would cost and keeping the
dearest — the same metric `Zonotope.reduce` uses, since what a box costs does
not depend on which coefficient scales the generator.

The box is what makes this a polynomial zonotope's operation rather than a
zonotope's. A monomial never leaves `[-1,1]`, so the dropped generators reach no
further than `∑ |G|` per coordinate; the enclosure is that diagonal block, and
it is independent because nothing ties it to the factors any more. CORA is
tighter on a column whose exponents are all even, where the monomial stays in
`[0,1]` and half the box moves into the centre. That is a precision knob and not
the guarantee, so it is left out.

`reduce` compacts first, which is the whole reason `compact` exists: the count
being reduced has to be a count of monomials the set actually has, or the order
bounds noise.

The order counts the *dependent* block, and the independent one is untouched
apart from the `n` generators the box adds. Reducing that block too is
`Zonotope.reduce`'s shape over a second partition, and is not here: a caller
that also needs the independent count bounded still has to say so. Any partition
over-approximates, so a rule is free to be a heuristic and owes no proof.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Real

open Matrix

variable {n d r : ℕ}

/-- Partitions the dependent generators rather than choosing them: `part.left`
is kept with its exponent columns, `part.right` absorbed into a diagonal block
of independent generators. CORA's selection rules are this definition with a
different partition. -/
def PolyZonotope.reduceBy (PZ : PolyZonotope (Vec ℝ n))
    (part : Split (Fin PZ.h) into (Fin d) and (Fin r)) : PolyZonotope (Vec ℝ n) where
  p := PZ.p
  h := d
  q := PZ.q + n
  c := PZ.c
  G := fun l => PZ.G (part.left l)
  E := fun k l => PZ.E k (part.left l)
  GI := Fin.append PZ.GI (Matrix.diagonal fun i => ∑ l, |PZ.G (part.right l) i|)

/-- Girard's metric on one generator, `‖g‖₁ - ‖g‖∞`. It is zero exactly on the
axis-aligned generators, which a box reproduces for free, and grows with what
boxing the generator would cost. The max folds from `0`, which no `|G i j|`
undercuts. -/
noncomputable def PolyZonotope.aux_girardMetric (PZ : PolyZonotope (Vec ℝ n))
    (j : Fin PZ.h) : ℝ :=
  (∑ i, |PZ.G j i|) - Finset.univ.fold max 0 fun i => |PZ.G j i|

/-- The dependent generators Girard's rule keeps at order `o`, against the rest:
`(o-1)*n` of them, which is what leaves room for the box of `n` that replaces
the others.

Sorting is ascending, so the metric enters negated and CORA's descending order
comes out: the generators dearest to box rank first and survive. -/
noncomputable def PolyZonotope.aux_girardSplit (PZ : PolyZonotope (Vec ℝ n)) (o : ℕ)
    (hlt : o * n < PZ.h) :
    Split (Fin PZ.h) into (Fin ((o - 1) * n)) and (Fin (PZ.h - (o - 1) * n)) :=
  have hle : (o - 1) * n ≤ PZ.h :=
    le_of_lt (lt_of_le_of_lt (Nat.mul_le_mul (Nat.sub_le o 1) (le_refl n)) hlt)
  (Partition.split ((o - 1) * n) (PZ.h - (o - 1) * n)).reindex
    ((Tuple.sort fun j => -PZ.aux_girardMetric j).symm.trans
      (finCongr (Nat.add_sub_cancel' hle).symm))

/-- CORA's `reduce(pZ, 'girard', o)` on the dependent block: keep the `(o-1)*n`
generators Girard ranks first and box the rest, which brings the dependent count
to `(o-1)*n`. Already at that order or below, nothing happens.

Noncomputable, as ordering reals is. A rule that runs needs a decidable order,
which is the float layer's to give. -/
noncomputable def PolyZonotope.reduceGirard (PZ : PolyZonotope (Vec ℝ n)) (o : ℕ) :
    PolyZonotope (Vec ℝ n) :=
  if hlt : o * n < PZ.h then PZ.reduceBy (PZ.aux_girardSplit o hlt) else PZ

/-- CORA's `reduce`: compact, then rank. Compacting first is not an
optimization — a repeated exponent column is one monomial, and ranking before
merging would spend the budget twice on it. -/
noncomputable def PolyZonotope.reduce (PZ : PolyZonotope (Vec ℝ n)) (o : ℕ) :
    PolyZonotope (Vec ℝ n) :=
  PZ.compact.reduceGirard o

end CORALean.Real
