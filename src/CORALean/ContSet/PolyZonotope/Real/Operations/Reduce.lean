import CORALean.ContSet.PolyZonotope.Real.Operations.Compact
import CORALean.Global.Partition
import CORALean.Global.Sort

/-!
# `PolyZonotope.reduce`

CORA's `@polyZonotope/reduce`: bring the generator count down to a maximum
order. `reduceBy` keeps the dependent and the independent generators that two
partitions name and boxes the rest into `n` new *independent* generators;
Girard's is the rule that chooses both partitions, ranking by what boxing a
generator would cost and keeping the dearest — the same metric `Zonotope.reduce`
uses, since what a box costs does not depend on which coefficient scales the
generator.

The two blocks are ranked as one, and that is what bounds the result. CORA
reduces when `h + q > n·o` and keeps `(o-1)·n` of the concatenation `[G, GI]`,
so the `n` the box adds brings the total back to `n·o`; ranking the dependent
block alone leaves `q` free to grow by a box per step without limit.
`Theorems/ReduceOrder` states the bound.

The joint ranking enters as a single number, `aux_girardKeptDep`: how many of
the best `(o-1)·n` generators are dependent. Each block is then cut at its share
of the budget by the same metric, which selects what the joint cut selects,
since restricting a total order to a subset keeps its prefixes. Carrying the
joint partition itself would make the two block sizes cardinalities of a
filtered set rather than plain counts, and select exactly the same generators.

The box is what makes this a polynomial zonotope's operation rather than a
zonotope's. A monomial never leaves `[-1,1]`, so the dropped dependent
generators reach no further than `∑ |G|` per coordinate — the same bound an
independent coefficient obeys, which is why one box covers both blocks. CORA is
tighter on a column whose exponents are all even, where the monomial stays in
`[0,1]` and half the box moves into the centre. That is a precision knob and not
the guarantee, so it is left out.

`reduce` compacts first, which is the whole reason `compact` exists: the count
being reduced has to be a count of monomials the set actually has, or the order
bounds noise.

Two departures from CORA remain, both deliberate. It ranks by `sum(G.^2)`,
where Girard's `‖g‖₁ - ‖g‖∞` is precisely what boxing a generator costs and is
zero on an axis-aligned one, which a squared length is not — and CORA's own
`zonotope/reduce('girard')` ranks by Girard's. And it boxes the dropped
generators through a zonotope reduced to order one, which under `'girard'` is
this diagonal block exactly: order 1 keeps `(1-1)·n = 0` generators and boxes
the rest into the row sums of `|G|`. The two differ only by the even-exponent
halving above, and — for a method such as `'pca'` — by the box sitting in a
rotated basis.
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
`partD.left` and `partI.left` name is kept, with the exponent columns of the
former, and the rest is absorbed into a diagonal block of `n` independent
generators. CORA's selection rules are this definition at different
partitions. -/
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

/-- Girard's metric on one generator, `‖g‖₁ - ‖g‖∞`. It is zero exactly on the
axis-aligned generators, which a box reproduces for free, and grows with what
boxing the generator would cost. Over a bare family of generators, so that the
dependent block, the independent one and their concatenation are all ranked by
this one line. The max folds from `0`, which no `|G i j|` undercuts. -/
noncomputable def PolyZonotope.aux_girardMetric {m : ℕ} (G : Fin m → Vec ℝ n) (l : Fin m) : ℝ :=
  (∑ i, |G l i|) - Finset.univ.fold max 0 fun i => |G l i|

/-- The `k` generators a metric ranks first, against the rest. Clamped to the
block, which is what makes the split total: a budget larger than the block asks
for all of it, and no order hypothesis has to travel with the split.

Sorting is ascending, so the metric enters negated and CORA's descending order
comes out: the generators dearest to box rank first and survive. -/
noncomputable def PolyZonotope.aux_girardSplit {m : ℕ} (metric : Fin m → ℝ) (k : ℕ) :
    Split (Fin m) into (Fin (min k m)) and (Fin (m - min k m)) :=
  (Partition.split (min k m) (m - min k m)).reindex
    ((Tuple.sort fun l => -metric l).symm.trans
      (finCongr (Nat.add_sub_cancel' (min_le_right k m)).symm))

/-- How many of the `K` best-ranked generators overall are dependent ones: the
whole of CORA's joint accounting, as one number. `rank` is CORA's
`sort(len,'descend')` on the concatenation `[G, GI]`, read as a rank rather than
as an order, and bound by a `let` so that the sort is run once rather than once
per generator. The independent block gets what is left of `K`, and each block is
cut by the metric that ranked the two together, so the two cuts fall where the
joint cut does.

Capped at `K`, and the cap never binds: `reduceGirard` calls this only where
`K < h + q`, so exactly `K` generators rank below it and the two blocks take
`K` between them. The cap is there to make the order bound arithmetic rather
than a fact about the ranking, which owes no proof. -/
noncomputable def PolyZonotope.aux_girardKeptDep (PZ : PolyZonotope (Vec ℝ n)) (K : ℕ) : ℕ :=
  let rank := (Tuple.sort fun l =>
    -PolyZonotope.aux_girardMetric (Fin.append PZ.G PZ.GI) l).symm
  min K (Finset.univ.filter fun l : Fin PZ.h =>
    (rank (Fin.castAdd PZ.q l) : ℕ) < K).card

/-- CORA's `reduce(pZ, 'girard', o)`: with more than `n·o` generators in the two
blocks together, keep the `(o-1)·n` that Girard ranks first and box the rest,
which brings the total back to `n·o`. At that order or below, nothing happens.

Noncomputable, as ordering reals is. A rule that runs needs a decidable order,
which is the float layer's to give. -/
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

end CORALean.Real
