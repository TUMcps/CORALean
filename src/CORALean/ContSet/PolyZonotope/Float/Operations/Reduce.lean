import CORALean.ContSet.PolyZonotope.Float.Operations.Compact
import CORALean.Global.Partition
import CORALean.Global.Sort

/-!
# `PolyZonotope.reduce`

The exact layer's `reduce`, rounded — and the one operation here that the float
layer *runs* where the exact layer only specifies. `PolyZonotope.reduceGirard`
is noncomputable over ℝ because `Tuple.sort` needs a `LinearOrder` on the
metric; `sortPerm` asks its comparator for nothing, so `le` on a machine scalar
suffices. It can afford to: `reduceBy_outer` holds at every pair of partitions,
so a misranking costs precision and never soundness.

The dependent and the independent block are ranked as one, as over ℝ and as in
CORA, which is what bounds the result: `Theorems/ReduceOrder` reads `n·o` off
the two clamped budgets and never off the ranking.

`reduceBy` charges nothing to the error box. The centre, the kept generators of
either block and their exponent columns are copied exactly, and the diagonal
block rounds *up* — twice, once per block radius and once for their sum — which
only enlarges a result that was already an over-approximation. `compact`, which
`reduce` runs first as over ℝ, does charge one: merging two columns adds their
entries.

Running it is what makes the order bound mean what it means over ℝ — a count of
distinct monomials rather than of stored columns, which `plus` and `quadMap`
inflate while the set stands still.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   03-September-2026
-- Last revision: ---

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n d r dI rI : ℕ}

/-- How far the dropped generators of both blocks reach in each coordinate: the
two row sums, added upward. A monomial and an independent coefficient obey the
same bound, so one box covers the two blocks together. -/
def PolyZonotope.dropRadius (PZ : PolyZonotope 𝕋 n)
    (partD : Split (Fin PZ.h) into (Fin d) and (Fin r))
    (partI : Split (Fin PZ.q) into (Fin dI) and (Fin rI)) : Vec 𝕋 n :=
  fun i₀ => addUp (radius (fun i l => PZ.G i (partD.right l)) i₀)
    (radius (fun i j => PZ.GI i (partI.right j)) i₀)

/-- CORA's reduction at a given pair of partitions, unchanged in shape and sound
for every one of them: the kept dependent generators keep their exponent
columns, the kept independent ones are copied, and the rest of both blocks
becomes a diagonal block of *independent* generators — independent because
nothing ties a box to the factors any more. -/
def PolyZonotope.reduceBy (PZ : PolyZonotope 𝕋 n)
    (partD : Split (Fin PZ.h) into (Fin d) and (Fin r))
    (partI : Split (Fin PZ.q) into (Fin dI) and (Fin rI)) : PolyZonotope 𝕋 n where
  p := PZ.p
  h := d
  q := dI + n
  c := PZ.c
  G := fun i l => PZ.G i (partD.left l)
  E := fun k l => PZ.E k (partD.left l)
  GI := fun i => Fin.append (fun j => PZ.GI i (partI.left j))
    (diagonalBlock (PZ.dropRadius partD partI) i)
  err := PZ.err

/-- Girard's metric on one generator, `‖g‖₁ - ‖g‖∞`, in `𝕋`. Zero exactly on the
axis-aligned generators, which a box reproduces for free. Over a bare matrix, so
that the dependent block, the independent one and their concatenation are all
ranked by this one line. -/
def PolyZonotope.aux_girardMetric {m : ℕ} (G : Mat 𝕋 n m) (l : Fin m) : 𝕋 :=
  subDown (sumUp fun i => absolute (G i l)) (maximumOver fun i => absolute (G i l))

/-- CORA's `[G, GI]`: the two blocks as one matrix, which is what it ranks.
Generators carry the second index here, so concatenating them appends along a
row. -/
def PolyZonotope.aux_concatGens (PZ : PolyZonotope 𝕋 n) : Mat 𝕋 n (PZ.h + PZ.q) :=
  fun i => Fin.append (PZ.G i) (PZ.GI i)

/-- The `k` generators a metric ranks first, against the rest. Clamped to the
block, which is what makes the split total: a budget larger than the block asks
for all of it, and no order hypothesis has to travel with the split.

The comparator ranks the larger metric first, so the generators dearest to box
survive — CORA's descending sort. -/
def PolyZonotope.aux_girardSplit {m : ℕ} (metric : Fin m → 𝕋) (k : ℕ) :
    Split (Fin m) into (Fin (min k m)) and (Fin (m - min k m)) :=
  (Partition.split (min k m) (m - min k m)).reindex
    ((sortPerm fun l₁ l₂ => le (metric l₂) (metric l₁)).symm.trans
      (finCongr (Nat.add_sub_cancel' (min_le_right k m)).symm))

/-- How many of the `K` best-ranked generators overall are dependent ones: the
whole of CORA's joint accounting, as one number. `rank` is CORA's
`sort(len,'descend')` on `[G, GI]`, read as a rank rather than as an order, and
bound by a `let` so that the sort runs once rather than once per generator —
which matters here, where every metric it compares reads a generator of a set
`compact` has just merged and nothing memoizes. The independent block gets what
is left of `K`, and each block is cut by the metric that ranked the two
together, so the two cuts fall where the joint cut does.

That the two cuts agree with the joint one needs the comparator to be a
preorder. `le` on a machine scalar is one, and nothing here depends on it:
disagreeing costs precision, never soundness.

Capped at `K`, and the cap never binds: `reduceGirard` calls this only where
`K < h + q`, so exactly `K` generators rank below it and the two blocks take
`K` between them. The cap is there to make the order bound arithmetic rather
than a fact about the ranking. -/
def PolyZonotope.aux_girardKeptDep (PZ : PolyZonotope 𝕋 n) (K : ℕ) : ℕ :=
  let metric := PolyZonotope.aux_girardMetric PZ.aux_concatGens
  let rank := (sortPerm fun l₁ l₂ => le (metric l₂) (metric l₁)).symm
  min K (Finset.univ.filter fun l : Fin PZ.h =>
    (rank (Fin.castAdd PZ.q l) : ℕ) < K).card

/-- CORA's `reduce(pZ, 'girard', o)`: with more than `n·o` generators in the two
blocks together, keep the `(o-1)·n` that Girard ranks first and box the rest,
which brings the total back to `n·o`. At that order or below, nothing
happens. -/
def PolyZonotope.reduceGirard (PZ : PolyZonotope 𝕋 n) (o : ℕ) : PolyZonotope 𝕋 n :=
  if o * n < PZ.h + PZ.q then
    let K := (o - 1) * n
    let d := PZ.aux_girardKeptDep K
    PZ.reduceBy (PolyZonotope.aux_girardSplit (PolyZonotope.aux_girardMetric PZ.G) d)
      (PolyZonotope.aux_girardSplit (PolyZonotope.aux_girardMetric PZ.GI) (K - d))
  else PZ

/-- CORA's `reduce`: to a maximum order, by whichever rule the representation
sees fit. Girard's is the one here, as over ℝ, and which it is goes no further —
a caller names an order and gets an over-approximation of bounded size. -/
def PolyZonotope.reduce (PZ : PolyZonotope 𝕋 n) (o : ℕ) : PolyZonotope 𝕋 n :=
  PZ.compact.reduceGirard o

end CORALean.Float
