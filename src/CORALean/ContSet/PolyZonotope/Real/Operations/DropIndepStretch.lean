import CORALean.ContSet.PolyZonotope.Real.Operations.DropIndepMat
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# `PolyZonotope.dropIndepStretch`

[1, Prop. 2] (Overapproximative Generator Removal): one independent generator,
named by `partI.right 0`, is dropped, and the `n` picked dependent generators
`partD.left` are stretched to compensate — by `1 + |γⱼ|` rather than [1]'s own
`1 + γⱼ`, `γ := P⁻¹ g^{(i)}` — a safe bound either way (`|1 + γⱼ| ≤ 1 + |γⱼ|`)
and one that does not depend on which sign convention the source's own
generators happen to use. Every other dependent generator, and the whole
exponent matrix `E`, is untouched — the compensation lives entirely in the
`n` picked columns of `G`, never in a fresh independent block the way
`reduceBy` would spend it.

`partD.index.symm` tells `G` which side of the partition an index came from,
the same bookkeeping `reduceBy`'s own `dropRadius`/`reduceBy` pair reads.

## References

* [1] M. Althoff. "Reachability Analysis of Nonlinear Systems using Conservative
      Polynomialization and Non-Convex Sets". HSCC 2013.
-/

-- Authors:       Claude Opus 5
-- Written:       21-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

noncomputable def PolyZonotope.dropIndepStretch (pZ : PolyZonotope (Vec ℝ n)) {r dI : ℕ}
    (partD : Split (Fin pZ.h) into (Fin n) ⊕ (Fin r))
    (partI : Split (Fin pZ.q) into (Fin dI) ⊕ (Fin 1)) : PolyZonotope (Vec ℝ n) :=
  let γ : Fin n → ℝ := (pZ.dropIndepMat partD)⁻¹ *ᵥ pZ.GI (partI.right 0)
  { p := pZ.p
    h := pZ.h
    q := dI
    c := pZ.c
    G := fun l => match partD.index.symm l with
      | ⟨true, j⟩ => (1 + |γ j|) • pZ.G l
      | ⟨false, _⟩ => pZ.G l
    E := pZ.E
    GI := fun l => pZ.GI (partI.left l) }

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
