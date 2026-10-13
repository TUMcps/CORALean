import CORALean.Global.Float.SoundFloatArithmetic
import CORALean.NN.Layers.Definitions.EvalPoly

/-!
# What a polynomial activation has to supply

CORA's `computeApproxPoly` together with the error `computeApproxError` [1, Alg. 1] leaves: per
box, the coefficients of a degree-`m` polynomial and the error to allow for, stored in the scalar.
`Sound` is that it encloses `σ` on every box the stored values describe, measured against the
coefficients *stored*: a rounded fit is a different fit and not a wrong one, and only the
error pays. `Relaxation` is the order-1 case.

A layer's abstraction is one relaxation per neuron, all at one degree, which is what an order
pattern [1, Eq. 23] makes of a nonlinear layer; a family is one per refinement level, the order
free to grow with it, and sound when every level is.

## References

* [1] T. Ladner and M. Althoff. "Automatic Abstraction Refinement in Neural
      Network Verification using Sensitivity Analysis". HSCC 2023.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-September-2026
-- Last update:   23-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Float.SoundFloatArithmetic

variable {𝕋 : Type} [Float.FloatOps 𝕋] [Float.SoundFloatArithmetic 𝕋] {m : ℕ}


-- ========================================  MAIN TYPE  ========================================= --

/-- A degree-`m` fit per box, stored in the scalar and nothing else. -/
structure PolyRelaxation (𝕋 : Type) [Float.FloatOps 𝕋] [Float.SoundFloatArithmetic 𝕋] (m : ℕ) where
  coeffs : 𝕋 → 𝕋 → Fin (m + 1) → 𝕋
  error : 𝕋 → 𝕋 → 𝕋

/-- That it encloses `σ` on every box the stored values describe. -/
structure PolyRelaxation.Sound (P : PolyRelaxation 𝕋 m) (σ : ℝ → ℝ) : Prop where
  sound {l u : 𝕋} {t : ℝ} (hl : toReal l ≤ t) (hu : t ≤ toReal u) :
    |σ t - Real.evalPoly (fun k => toReal (P.coeffs l u k)) t| ≤ toReal (P.error l u)

/-- A layer's abstraction: one relaxation per neuron, all at one degree. -/
abbrev LayerRelaxation (𝕋 : Type) [Float.FloatOps 𝕋] [Float.SoundFloatArithmetic 𝕋] (n m : ℕ) :=
  Fin n → PolyRelaxation 𝕋 m

/-- A polynomial relaxation per refinement level, the order free to grow. -/
structure PolyRelaxationFamily (𝕋 : Type) [Float.FloatOps 𝕋] [Float.SoundFloatArithmetic 𝕋] where
  deg : ℕ → ℕ
  rel : (o : ℕ) → PolyRelaxation 𝕋 (deg o)

/-- That every level of it encloses `σ`, which is where `σ` arrives. -/
structure PolyRelaxationFamily.Sound (F : PolyRelaxationFamily 𝕋) (σ : ℝ → ℝ) : Prop where
  rel_sound (o : ℕ) : (F.rel o).Sound σ

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
