import CORALean.ContSet.Zonotope.Real.Zonotope

/-!
# `Zonotope.reduce`

CORA's `@zonotope/reduce`: bring the generator count down to a maximum order.
`reduceBy` keeps the generators a partition names and boxes the rest, which is
that reduction whatever rule chose the partition. Girard's is the rule
implemented: rank by what boxing a generator would cost, keep the dearest.

Any partition gives an over-approximation, so a rule owes no proof of its own
and is free to be a heuristic. A second one would be another `aux_girardSplit`
and nothing else — which is why `reduce` takes an order and not a choice of rule.
-/

-- Authors:       Tobias Ladner
-- Written:       18-August-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Real

open Matrix

variable {n q r : ℕ}

/-- Partitions the generator indices rather than choosing them: `part.left` is
kept, `part.right` absorbed into a diagonal block. CORA's twenty-odd selection
rules are this definition with a different partition. -/
def Zonotope.reduceBy (Z : Zonotope (Vec ℝ n))
    (part : Split (Fin Z.h) into (Fin q) and (Fin r)) : Zonotope (Vec ℝ n) where
  h := q + n
  c := Z.c
  G := Fin.append (fun l => Z.G (part.left l))
        (Matrix.diagonal fun i => ∑ l, |Z.G (part.right l) i|)

/-- Girard's metric on one generator, `‖g‖₁ - ‖g‖∞`. It is zero exactly on the
axis-aligned generators, which a box reproduces for free, and grows with what
boxing the generator would cost. The max folds from `0`, which no `|G i j|`
undercuts. -/
noncomputable def Zonotope.aux_girardMetric (Z : Zonotope (Vec ℝ n)) (j : Fin Z.h) : ℝ :=
  (∑ i, |Z.G j i|) - Finset.univ.fold max 0 fun i => |Z.G j i|

/-- The generators Girard's rule keeps at order `o`, against the rest: `(o-1)*n`
of them, which is what leaves room for the box of `n` that replaces the others.

Sorting is ascending, so the metric enters negated and CORA's descending order
comes out: the generators dearest to box rank first and survive. -/
noncomputable def Zonotope.aux_girardSplit (Z : Zonotope (Vec ℝ n)) (o : ℕ)
    (hlt : o * n < Z.h) :
    Split (Fin Z.h) into (Fin ((o - 1) * n)) and (Fin (Z.h - (o - 1) * n)) :=
  have hle : (o - 1) * n ≤ Z.h :=
    le_of_lt (lt_of_le_of_lt (Nat.mul_le_mul (Nat.sub_le o 1) (le_refl n)) hlt)
  (Partition.split ((o - 1) * n) (Z.h - (o - 1) * n)).reindex
    ((Tuple.sort fun j => -Z.aux_girardMetric j).symm.trans
      (finCongr (Nat.add_sub_cancel' hle).symm))

/-- CORA's `reduce(Z, 'girard', o)`: keep the `(o - 1) * n` generators Girard
ranks first and box the rest, which brings the count to `o * n`. Already at that
order or below, nothing happens.

Noncomputable, as ordering reals is. A rule that runs needs a decidable order,
which is the float layer's to give. -/
noncomputable def Zonotope.reduceGirard (Z : Zonotope (Vec ℝ n)) (o : ℕ) :
    Zonotope (Vec ℝ n) :=
  if hlt : o * n < Z.h then Z.reduceBy (Z.aux_girardSplit o hlt) else Z

/-- CORA's `reduce`: to a maximum order, by whichever rule the representation
sees fit. Girard's is the one here, and which it is goes no further — a caller
names an order and gets an over-approximation. -/
noncomputable def Zonotope.reduce (Z : Zonotope (Vec ℝ n)) (o : ℕ) : Zonotope (Vec ℝ n) :=
  Z.reduceGirard o

end CORALean.Real
