module

public import CORALean.ContSet.Interval.Float.Operations.Basic
public import CORALean.ContSet.PolyZonotope.Float.Operations.GeneratorError
public import CORALean.ContSet.PolyZonotope.Float.Operations.MergedGen
public import CORALean.ContSet.PolyZonotope.Float.Operations.RelaxGap
public import CORALean.ContSet.PolyZonotope.Float.Operations.RelaxGen

@[expose] public section

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

-- Authors:       Claude Opus 5
-- Written:       05-September-2026
-- Last update:   06-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] {n d : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The two generators `part.right` names merged into one, at the exponent
column of the second, the first scaled by `ξ_E` becoming independent. -/
def PolyZonotope.relaxExp (pZ : PolyZonotope (Vec 𝕋 n))
    (part : Split (Fin pZ.h) into (Fin d) ⊕ (Fin 2)) (k₀ : Fin pZ.p) : PolyZonotope (Vec 𝕋 n) where
  p := pZ.p
  h := d + 1
  q := pZ.q + 1
  c := pZ.c
  G := Fin.append (fun l => pZ.G (part.left l)) (fun _ => pZ.mergedGen part)
  E := fun k => Fin.append (fun l => pZ.E k (part.left l)) (fun _ => pZ.E k (part.right 1))
  GI := Fin.append pZ.GI (fun _ => pZ.relaxGen part k₀)
  err := pZ.err.plus (PolyZonotope.generatorError (pZ.relaxGap part k₀))

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
