module

public import CORALean.ContSet.ConPolyZono.Float.Operations.Compact
public import CORALean.ContSet.ConPolyZono.Float.Operations.ReduceGirard
public import CORALean.ContSet.ConPolyZono.Real.Operations.Reduce

@[expose] public section

/-!
# `ConPolyZono.reduce`

The exact layer's `reduce`, rounded — and the one operation the float layer
*runs* where the exact layer only specifies: `reduceGirard` is noncomputable
over ℝ because `Tuple.sort` needs a `LinearOrder`, while `sortPerm` asks its
comparator for nothing. It can afford to, `reduceBy_outer` holding at every pair
of partitions, so a misranking costs precision and never soundness.

`reduceBy` charges nothing to either place a rounding can go. The center, the
kept generators and their exponent columns are copied exactly, the whole
constraint block with them — so `b` does not move and the ranking never reads a
constraint — and the diagonal block rounds *up*, twice, which only enlarges an
over-approximation. `compact`, which `reduce` runs first, is where the rounding
of this operation is: it pays into the error box and into `b` both, and running
it is what makes the order bound count distinct monomials.
-/

-- Authors:       Claude Opus 5
-- Written:       05-September-2026
-- Last update:   06-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- CORA's `reduce`: compact, then rank. A caller names an order and gets an
over-approximation of bounded size; which rule ranked it goes no further. -/
def ConPolyZono.reduce (cPZ : ConPolyZono 𝕋 (Vec 𝕋 n)) (o : ℕ) : ConPolyZono 𝕋 (Vec 𝕋 n) :=
  cPZ.compact.reduceGirard o

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
