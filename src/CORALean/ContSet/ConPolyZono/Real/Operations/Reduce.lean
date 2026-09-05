import CORALean.ContSet.ConPolyZono.Real.Operations.Compact
import CORALean.Global.Partition
import CORALean.Global.Sort

/-!
# `ConPolyZono.reduce`

CORA's `@conPolyZono/reduce` at Girard's rule: bring the generator count down to
a maximum order. `reduceBy` keeps the dependent and the independent generators
two partitions name and boxes the rest into `n` new *independent* generators;
Girard's metric chooses both partitions, ranking by what boxing a generator
would cost, as `PolyZonotope.reduce` does.

The constraint block is copied unchanged — `p`, `A`, `b` and `EC` all — so a
factor vector admitted before is admitted after and the ranking never reads a
constraint. Only `E`'s kept columns travel, and a dropped column reaches no
further than an independent coefficient, a monomial never leaving `[-1,1]`.

The two blocks are ranked as one, which is what bounds the result: `(o-1)·n` of
the concatenation are kept, so the `n` the box adds brings the total back to
`n·o`. `reduce` compacts first, so the count counts distinct monomials, and
compaction is also the only stage that moves `s`.
-/

-- Authors:       Tobias Ladner
-- Written:       05-September-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Real

open Matrix

variable {n d r dI rI : ℕ}

/-- How far the dropped generators of both blocks reach in each coordinate. A
monomial and an independent coefficient obey the same bound, so one box covers
the two blocks together. -/
def ConPolyZono.dropRadius (C : ConPolyZono (Vec ℝ n))
    (partD : Split (Fin C.h) into (Fin d) and (Fin r))
    (partI : Split (Fin C.q) into (Fin dI) and (Fin rI)) : Vec ℝ n :=
  fun i => (∑ l, |C.G (partD.right l) i|) + ∑ j, |C.GI (partI.right j) i|

/-- Partitions both generator blocks: what `partD.left` and `partI.left` name is
kept, with the former's exponent columns, and the rest is absorbed into a
diagonal block of `n` independent generators. The constraints stand. -/
def ConPolyZono.reduceBy (C : ConPolyZono (Vec ℝ n))
    (partD : Split (Fin C.h) into (Fin d) and (Fin r))
    (partI : Split (Fin C.q) into (Fin dI) and (Fin rI)) : ConPolyZono (Vec ℝ n) where
  p := C.p
  h := d
  q := dI + n
  m := C.m
  s := C.s
  c := C.c
  G := fun l => C.G (partD.left l)
  E := fun k l => C.E k (partD.left l)
  GI := Fin.append (fun j => C.GI (partI.left j))
          (Matrix.diagonal (C.dropRadius partD partI))
  A := C.A
  b := C.b
  EC := C.EC

/-- Girard's metric on one generator, `‖g‖₁ - ‖g‖∞`, over a bare family so that
either block and their concatenation are ranked by this one line. Zero on the
axis-aligned generators; the max folds from `0`, which no `|G l i|` undercuts. -/
noncomputable def ConPolyZono.aux_girardMetric {m : ℕ} (G : Fin m → Vec ℝ n) (l : Fin m) : ℝ :=
  (∑ i, |G l i|) - Finset.univ.fold max 0 fun i => |G l i|

/-- The `k` generators a metric ranks first, against the rest. Clamped to the
block, so the split is total and no order hypothesis travels with it; sorting is
ascending, so the metric enters negated and the dearest to box rank first. -/
noncomputable def ConPolyZono.aux_girardSplit {m : ℕ} (metric : Fin m → ℝ) (k : ℕ) :
    Split (Fin m) into (Fin (min k m)) and (Fin (m - min k m)) :=
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

/-- CORA's `reduce`: compact, then rank. Compacting first is not an
optimization — a repeated exponent column is one monomial, and ranking before
merging would spend the budget twice on it. -/
noncomputable def ConPolyZono.reduce (C : ConPolyZono (Vec ℝ n)) (o : ℕ) :
    ConPolyZono (Vec ℝ n) :=
  C.compact.reduceGirard o

end CORALean.Real
