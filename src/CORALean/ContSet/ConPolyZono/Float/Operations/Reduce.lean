import CORALean.ContSet.ConPolyZono.Float.Operations.Compact
import CORALean.ContSet.ConPolyZono.Real.Operations.Reduce
import CORALean.Global.Partition
import CORALean.Global.Sort

/-!
# `ConPolyZono.reduce`

The exact layer's `reduce`, rounded — and the one operation the float layer
*runs* where the exact layer only specifies: `reduceGirard` is noncomputable
over ℝ because `Tuple.sort` needs a `LinearOrder`, while `sortPerm` asks its
comparator for nothing. It can afford to, `reduceBy_outer` holding at every pair
of partitions, so a misranking costs precision and never soundness.

`reduceBy` charges nothing to either place a rounding can go. The centre, the
kept generators and their exponent columns are copied exactly, the whole
constraint block with them — so `b` does not move and the ranking never reads a
constraint — and the diagonal block rounds *up*, twice, which only enlarges an
over-approximation. `compact`, which `reduce` runs first, is where the rounding
of this operation is: it pays into the error box and into `b` both, and running
it is what makes the order bound count distinct monomials.
-/

-- Authors:       Tobias Ladner
-- Written:       05-September-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n d r dI rI : ℕ}

/-- How far the dropped generators of both blocks reach in each coordinate: the
two row sums, added upward. A monomial and an independent coefficient obey the
same bound, so one box covers the two blocks together. -/
def ConPolyZono.dropRadius (C : ConPolyZono 𝕋 n)
    (partD : Split (Fin C.h) into (Fin d) and (Fin r))
    (partI : Split (Fin C.q) into (Fin dI) and (Fin rI)) : Vec 𝕋 n :=
  fun i₀ => addUp (radius (fun i l => C.G i (partD.right l)) i₀)
    (radius (fun i j => C.GI i (partI.right j)) i₀)

/-- CORA's reduction at a given pair of partitions, sound for every one of them:
kept dependent generators keep their exponent columns, kept independent ones are
copied, and the rest becomes a box no longer tied to the factors. -/
def ConPolyZono.reduceBy (C : ConPolyZono 𝕋 n)
    (partD : Split (Fin C.h) into (Fin d) and (Fin r))
    (partI : Split (Fin C.q) into (Fin dI) and (Fin rI)) : ConPolyZono 𝕋 n where
  p := C.p
  h := d
  q := dI + n
  m := C.m
  s := C.s
  c := C.c
  G := fun i l => C.G i (partD.left l)
  E := fun k l => C.E k (partD.left l)
  GI := fun i => Fin.append (fun j => C.GI i (partI.left j))
    (diagonalBlock (C.dropRadius partD partI) i)
  A := C.A
  b := C.b
  EC := C.EC
  err := C.err

/-- Girard's metric on one generator, `‖g‖₁ - ‖g‖∞`, in `𝕋`, over a bare matrix
so that either block and their concatenation are ranked by this one line. Zero
on the axis-aligned generators, which a box reproduces for free. -/
def ConPolyZono.aux_girardMetric {m : ℕ} (G : Mat 𝕋 n m) (l : Fin m) : 𝕋 :=
  subDown (sumUp fun i => absolute (G i l)) (maximumOver fun i => absolute (G i l))

/-- CORA's `[G, GI]`: the two blocks as one matrix, which is what it ranks.
Generators carry the second index here, so concatenating them appends along a
row. -/
def ConPolyZono.aux_concatGens (C : ConPolyZono 𝕋 n) : Mat 𝕋 n (C.h + C.q) :=
  fun i => Fin.append (C.G i) (C.GI i)

/-- The `k` generators a metric ranks first, against the rest. Clamped to the
block, so the split is total and no order hypothesis travels with it; the
comparator ranks the larger metric first, CORA's descending sort. -/
def ConPolyZono.aux_girardSplit {m : ℕ} (metric : Fin m → 𝕋) (k : ℕ) :
    Split (Fin m) into (Fin (min k m)) and (Fin (m - min k m)) :=
  (Partition.split (min k m) (m - min k m)).reindex
    ((sortPerm fun l₁ l₂ => le (metric l₂) (metric l₁)).symm.trans
      (finCongr (Nat.add_sub_cancel' (min_le_right k m)).symm))

/-- How many of the `K` best-ranked generators overall are dependent: CORA's
joint accounting as one number, `rank` bound by a `let` so the sort runs once
over generators nothing memoizes. The cap at `K` never binds. -/
def ConPolyZono.aux_girardKeptDep (C : ConPolyZono 𝕋 n) (K : ℕ) : ℕ :=
  let metric := ConPolyZono.aux_girardMetric C.aux_concatGens
  let rank := (sortPerm fun l₁ l₂ => le (metric l₂) (metric l₁)).symm
  min K (Finset.univ.filter fun l : Fin C.h =>
    (rank (Fin.castAdd C.q l) : ℕ) < K).card

/-- CORA's `reduce(cPZ, 'girard', o)`: past `n·o` generators in the two blocks
together, keep the `(o-1)·n` Girard ranks first and box the rest, bringing the
total back to `n·o`. At that order or below, nothing happens. -/
def ConPolyZono.reduceGirard (C : ConPolyZono 𝕋 n) (o : ℕ) : ConPolyZono 𝕋 n :=
  if o * n < C.h + C.q then
    let K := (o - 1) * n
    let d := C.aux_girardKeptDep K
    C.reduceBy (ConPolyZono.aux_girardSplit (ConPolyZono.aux_girardMetric C.G) d)
      (ConPolyZono.aux_girardSplit (ConPolyZono.aux_girardMetric C.GI) (K - d))
  else C

/-- CORA's `reduce`: compact, then rank. A caller names an order and gets an
over-approximation of bounded size; which rule ranked it goes no further. -/
def ConPolyZono.reduce (C : ConPolyZono 𝕋 n) (o : ℕ) : ConPolyZono 𝕋 n :=
  C.compact.reduceGirard o

end CORALean.Float
