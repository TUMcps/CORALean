import CORALean.ContSet.PolyZonotope.Real.Operations.Compact
import CORALean.Global.Partition
import CORALean.Global.Sort

/-!
# `PolyZonotope.reduce`

CORA's `@polyZonotope/reduce`: bring the generator count down to a maximum
order. `reduceBy` keeps the dependent and the independent generators that two
partitions name and boxes the rest into `n` new *independent* generators;
Girard's metric chooses both partitions, ranking by what boxing a generator
would cost, as `Zonotope.reduce` does.

The two blocks are ranked as one, which is what bounds the result: `(o-1)·n` of
the concatenation are kept, so the `n` the box adds brings the total back to
`n·o`, where ranking the dependent block alone leaves `q` free to grow. The
joint ranking enters as one number, `aux_girardKeptDep`, and each block is cut
at its share of the budget by the same metric, selecting what the joint cut
selects. `reduce` compacts first, so the count reduced counts real monomials.

One box covers both blocks because a monomial never leaves `[-1,1]`, so a
dropped dependent generator reaches no further than an independent coefficient.
CORA is tighter on an all-even column and ranks by `sum(G.^2)`, not Girard's.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   03-September-2026
-- Last revision: ---

namespace CORALean.Real

open Matrix

variable {n d r dI rI : ℕ}

/-- How far the dropped generators of both blocks reach in each coordinate. A
monomial and an independent coefficient obey the same bound, so one box covers
the two blocks together. -/
def PolyZonotope.dropRadius (PZ : PolyZonotope (Vec ℝ n))
    (partD : Split (Fin PZ.h) into (Fin d) and (Fin r))
    (partI : Split (Fin PZ.q) into (Fin dI) and (Fin rI)) : Vec ℝ n :=
  fun i => (∑ l, |PZ.G (partD.right l) i|) + ∑ j, |PZ.GI (partI.right j) i|

/-- Partitions both generator blocks rather than choosing either: what
`partD.left` and `partI.left` name is kept, with the former's exponent columns,
and the rest is absorbed into a diagonal block of `n` independent generators. -/
def PolyZonotope.reduceBy (PZ : PolyZonotope (Vec ℝ n))
    (partD : Split (Fin PZ.h) into (Fin d) and (Fin r))
    (partI : Split (Fin PZ.q) into (Fin dI) and (Fin rI)) : PolyZonotope (Vec ℝ n) where
  p := PZ.p
  h := d
  q := dI + n
  c := PZ.c
  G := fun l => PZ.G (partD.left l)
  E := fun k l => PZ.E k (partD.left l)
  GI := Fin.append (fun j => PZ.GI (partI.left j))
          (Matrix.diagonal (PZ.dropRadius partD partI))

/-- Girard's metric on one generator, `‖g‖₁ - ‖g‖∞`, over a bare family so that
either block and their concatenation are ranked by this one line. Zero on the
axis-aligned generators; the max folds from `0`, which no `|G i j|` undercuts. -/
noncomputable def PolyZonotope.aux_girardMetric {m : ℕ} (G : Fin m → Vec ℝ n) (l : Fin m) : ℝ :=
  (∑ i, |G l i|) - Finset.univ.fold max 0 fun i => |G l i|

/-- The `k` generators a metric ranks first, against the rest. Clamped to the
block, so the split is total and no order hypothesis travels with it; sorting is
ascending, so the metric enters negated and the dearest to box rank first. -/
noncomputable def PolyZonotope.aux_girardSplit {m : ℕ} (metric : Fin m → ℝ) (k : ℕ) :
    Split (Fin m) into (Fin (min k m)) and (Fin (m - min k m)) :=
  (Partition.split (min k m) (m - min k m)).reindex
    ((Tuple.sort fun l => -metric l).symm.trans
      (finCongr (Nat.add_sub_cancel' (min_le_right k m)).symm))

/-- Nothing dropped: what a rule hands `reduceBy` for a block it leaves
alone. -/
noncomputable def PolyZonotope.aux_keepAll (m : ℕ) : Split (Fin m) into (Fin m) and (Fin 0) :=
  (Partition.split m 0).reindex (finCongr (Nat.add_zero m).symm)

/-- How many of the `K` best-ranked generators overall are dependent: CORA's
joint accounting as one number, `rank` bound by a `let` so the sort runs once.
The cap at `K` never binds and is there to keep the order bound arithmetic. -/
noncomputable def PolyZonotope.aux_girardKeptDep (PZ : PolyZonotope (Vec ℝ n)) (K : ℕ) : ℕ :=
  let rank := (Tuple.sort fun l =>
    -PolyZonotope.aux_girardMetric (Fin.append PZ.G PZ.GI) l).symm
  min K (Finset.univ.filter fun l : Fin PZ.h =>
    (rank (Fin.castAdd PZ.q l) : ℕ) < K).card

/-- CORA's `reduce(pZ, 'girard', o)`: past `n·o` generators in the two blocks
together, keep the `(o-1)·n` Girard ranks first and box the rest, bringing the
total back to `n·o`. Noncomputable, as ordering reals is. -/
noncomputable def PolyZonotope.reduceGirard (PZ : PolyZonotope (Vec ℝ n)) (o : ℕ) :
    PolyZonotope (Vec ℝ n) :=
  if o * n < PZ.h + PZ.q then
    let K := (o - 1) * n
    let d := PZ.aux_girardKeptDep K
    PZ.reduceBy (PolyZonotope.aux_girardSplit (PolyZonotope.aux_girardMetric PZ.G) d)
      (PolyZonotope.aux_girardSplit (PolyZonotope.aux_girardMetric PZ.GI) (K - d))
  else PZ

/-- CORA's `reduce`: compact, then rank. Compacting first is not an
optimization — a repeated exponent column is one monomial, and ranking before
merging would spend the budget twice on it. -/
noncomputable def PolyZonotope.reduce (PZ : PolyZonotope (Vec ℝ n)) (o : ℕ) :
    PolyZonotope (Vec ℝ n) :=
  PZ.compact.reduceGirard o

/-- The same rule with the independent block left out: cut the dependent
generators alone against `n·o` and keep every independent one. Tighter per step
and bounding nothing — the box adds `n` independent generators at every call. -/
noncomputable def PolyZonotope.reduceGirardDependent (PZ : PolyZonotope (Vec ℝ n)) (o : ℕ) :
    PolyZonotope (Vec ℝ n) :=
  if o * n < PZ.h then
    PZ.reduceBy
      (PolyZonotope.aux_girardSplit (PolyZonotope.aux_girardMetric PZ.G) ((o - 1) * n))
      (PolyZonotope.aux_keepAll PZ.q)
  else PZ

/-- `reduce`'s shape at the dependent-only rule: compact, then rank. -/
noncomputable def PolyZonotope.reduceDependent (PZ : PolyZonotope (Vec ℝ n)) (o : ℕ) :
    PolyZonotope (Vec ℝ n) :=
  PZ.compact.reduceGirardDependent o

end CORALean.Real
