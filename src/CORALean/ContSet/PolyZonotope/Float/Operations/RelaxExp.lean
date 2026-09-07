import CORALean.ContSet.Interval.Float.Operations.Plus
import CORALean.ContSet.PolyZonotope.Float.Operations.GeneratorError
import CORALean.ContSet.PolyZonotope.Float.Operations.MergedGen
import CORALean.ContSet.PolyZonotope.Float.Operations.RelaxGap
import CORALean.ContSet.PolyZonotope.Float.Operations.RelaxGen

/-!
# `PolyZonotope.relaxExp`

The exact layer's `relaxExp`, rounded. Two things it computes are sums of stored
floats — the merged dependent column and the `ξ_E` copies of the relaxed one —
and each is stored downward with the gap to its upward rounding paid into the
box, as `compact` pays for merging columns.

`ξ_E` itself rounds nothing: `eDiff` is over ℕ in both layers and the exponent
matrix is copied, so the two layers relax by the same width. At `ξ_E ≤ 1` that
column folds against `zero` alone, which no format moves and only the axioms
leave open; the paper's graph selects exactly those pairs.

The centre is untouched, `ξ_c` being zero at `ξ_G = ξ_E`, so this operation adds
nothing to the box beyond the two gaps.
-/

-- Authors:       Tobias Ladner
-- Written:       05-September-2026
-- Last update:   06-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] {n d : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The two generators `part.right` names merged into one, at the exponent
column of the second, the first scaled by `ξ_E` becoming independent. -/
def PolyZonotope.relaxExp (PZ : PolyZonotope 𝕋 n)
    (part : Split (Fin PZ.h) into (Fin d) ⊕ (Fin 2)) (k₀ : Fin PZ.p) : PolyZonotope 𝕋 n where
  p := PZ.p
  h := d + 1
  q := PZ.q + 1
  c := PZ.c
  G := fun i => Fin.append (fun l => PZ.G i (part.left l)) (fun _ => PZ.mergedGen part i)
  E := fun k => Fin.append (fun l => PZ.E k (part.left l)) (fun _ => PZ.E k (part.right 1))
  GI := fun i => Fin.append (PZ.GI i) (fun _ => PZ.relaxGen part k₀ i)
  err := PZ.err.plus (PolyZonotope.generatorError (PZ.relaxGap part k₀))

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
