module

public import CORALean.ContSet.PolyZonotope.Float.Theorems.BilinRefines
public import CORALean.ContSet.PolyZonotope.Real.Theorems.BilinExact

@[expose] public section

/-!
# `PolyZonotope.bilin` over-approximates the exact pairing

The exact layer proves the hard half — the pairing of two polynomial zonotopes over shared
factors *is* a polynomial zonotope (`bilin_exact`) — and `bilin_refines` puts the exact pairing of
the nominal parts inside the float one. This reads it at the points `bilin_exact` names: at every
factor vector in the cube, the exact pairing of the two nominal points is a point of the float
pairing. Outer only.

## Inputs
* `Q` – family of bilinear form matrices
* `pZ₁` – first polynomial zonotope
* `pZ₂` – second polynomial zonotope

## Hypotheses
* `hp` – both have the same factor count

## Conclusion
* the bilinear image of shared factor values lies in the result
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       08-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Pointwise Matrix FloatOps SoundFloatArithmetic InflatedContSet

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n m : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- At every factor vector in the cube, the exact pairing of the two nominal points is a point of
the float pairing. -/
theorem PolyZonotope.bilin_outer (Q : Fin m → Mat 𝕋 n n) (pZ₁ pZ₂ : PolyZonotope (Vec 𝕋 n))
    (hp : pZ₁.p = pZ₂.p) : -- --- CONCL ---
    (fun a : Fin pZ₁.p → ℝ =>
        Real.PolyZonotope.quadBilin (fun k => toRealMat (Q k))
          ((nominal pZ₁).point a) ((nominal pZ₂).point fun k => a (Fin.cast hp.symm k)))
        '' {a | ∀ k, |a k| ≤ 1}
      ⊆ (PolyZonotope.bilin Q pZ₁ pZ₂ hp).construct :=
  (Real.PolyZonotope.bilin_exact (Real.PolyZonotope.quadBilin fun k => toRealMat (Q k))
    (nominal pZ₁) (nominal pZ₂) hp).subset.trans (PolyZonotope.bilin_refines Q pZ₁ pZ₂ hp)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
