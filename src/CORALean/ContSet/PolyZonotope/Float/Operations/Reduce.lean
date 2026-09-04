import CORALean.ContSet.PolyZonotope.Float.Operations.Compact
import CORALean.Global.Partition
import CORALean.Global.Sort

/-!
# `PolyZonotope.reduce`

The exact layer's `reduce`, rounded — and the one operation the float layer
*runs* where the exact layer only specifies: `reduceGirard` is noncomputable
over ℝ because `Tuple.sort` needs a `LinearOrder`, while `sortPerm` asks its
comparator for nothing. It can afford to, `reduceBy_outer` holding at every pair
of partitions, so a misranking costs precision and never soundness.

The two blocks are ranked as one, as over ℝ, which is what bounds the result:
`Theorems/ReduceOrder` reads `n·o` off the two clamped budgets and never off the
ranking.

`reduceBy` charges nothing to the error box. The centre, the kept generators and
their exponent columns are copied exactly, and the diagonal block rounds *up* —
twice, once per block radius and once for their sum — which only enlarges an
over-approximation. `compact`, which `reduce` runs first, does charge one:
merging two columns adds their entries, and running it is what makes the order
bound count distinct monomials rather than stored columns.
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

/-- CORA's reduction at a given pair of partitions, sound for every one of them:
kept dependent generators keep their exponent columns, kept independent ones are
copied, and the rest becomes a box no longer tied to the factors. -/
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

/-- Girard's metric on one generator, `‖g‖₁ - ‖g‖∞`, in `𝕋`, over a bare matrix
so that either block and their concatenation are ranked by this one line. Zero
on the axis-aligned generators, which a box reproduces for free. -/
def PolyZonotope.aux_girardMetric {m : ℕ} (G : Mat 𝕋 n m) (l : Fin m) : 𝕋 :=
  subDown (sumUp fun i => absolute (G i l)) (maximumOver fun i => absolute (G i l))

/-- CORA's `[G, GI]`: the two blocks as one matrix, which is what it ranks.
Generators carry the second index here, so concatenating them appends along a
row. -/
def PolyZonotope.aux_concatGens (PZ : PolyZonotope 𝕋 n) : Mat 𝕋 n (PZ.h + PZ.q) :=
  fun i => Fin.append (PZ.G i) (PZ.GI i)

/-- The `k` generators a metric ranks first, against the rest. Clamped to the
block, so the split is total and no order hypothesis travels with it; the
comparator ranks the larger metric first, CORA's descending sort. -/
def PolyZonotope.aux_girardSplit {m : ℕ} (metric : Fin m → 𝕋) (k : ℕ) :
    Split (Fin m) into (Fin (min k m)) and (Fin (m - min k m)) :=
  (Partition.split (min k m) (m - min k m)).reindex
    ((sortPerm fun l₁ l₂ => le (metric l₂) (metric l₁)).symm.trans
      (finCongr (Nat.add_sub_cancel' (min_le_right k m)).symm))

/-- Nothing dropped: what a rule hands `reduceBy` for a block it leaves
alone. -/
def PolyZonotope.aux_keepAll (m : ℕ) : Split (Fin m) into (Fin m) and (Fin 0) :=
  (Partition.split m 0).reindex (finCongr (Nat.add_zero m).symm)

/-- How many of the `K` best-ranked generators overall are dependent: CORA's
joint accounting as one number, `rank` bound by a `let` so the sort runs once
over generators nothing memoizes. The cap at `K` never binds. -/
def PolyZonotope.aux_girardKeptDep (PZ : PolyZonotope 𝕋 n) (K : ℕ) : ℕ :=
  let metric := PolyZonotope.aux_girardMetric PZ.aux_concatGens
  let rank := (sortPerm fun l₁ l₂ => le (metric l₂) (metric l₁)).symm
  min K (Finset.univ.filter fun l : Fin PZ.h =>
    (rank (Fin.castAdd PZ.q l) : ℕ) < K).card

/-- CORA's `reduce(pZ, 'girard', o)`: past `n·o` generators in the two blocks
together, keep the `(o-1)·n` Girard ranks first and box the rest, bringing the
total back to `n·o`. At that order or below, nothing happens. -/
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

/-- The same rule with the independent block left out: cut the dependent
generators alone against `n·o` and keep every independent one. Tighter per step
and bounding nothing — the box adds `n` independent generators at every call. -/
def PolyZonotope.reduceGirardDependent (PZ : PolyZonotope 𝕋 n) (o : ℕ) : PolyZonotope 𝕋 n :=
  if o * n < PZ.h then
    PZ.reduceBy
      (PolyZonotope.aux_girardSplit (PolyZonotope.aux_girardMetric PZ.G) ((o - 1) * n))
      (PolyZonotope.aux_keepAll PZ.q)
  else PZ

/-- `reduce`'s shape at the dependent-only rule: compact, then rank. -/
def PolyZonotope.reduceDependent (PZ : PolyZonotope 𝕋 n) (o : ℕ) : PolyZonotope 𝕋 n :=
  PZ.compact.reduceGirardDependent o

end CORALean.Float
