import CORALean.ContDynamics.LinearSys.Operations.TimePointStepInnerErrorFloat
import CORALean.ContSet.Zonotope.Float.Operations.MinkDiffRep

/-!
# A step's inner approximation, over a floating-point scalar

`timePointStepInnerRep` computed in `𝕋`: the float step
`timePointStepInputFloat` minus its budget `timePointStepInnerErrorFloat`, by
the float `Zonotope.minkDiffRep`. The real operation takes the exact step's
error box off the exact step; this one takes off what the *float* step owes,
which also covers the float step's excess over the exact one, measured against
the held input rather than against the exact step.

`minkDiffRep` is inward-rounded and certified by a float containment check, at a
representation `M`, a margin factor `ρ` and a right inverse `H` the caller
offers. Any of them wrong gives `none`, costing precision and never soundness;
`timePointStepInnerRepFloat_inner` is the guarantee on `some`.
-/

-- Authors:       Tobias Ladner
-- Written:       09-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The float step from `X₀` minus its budget, at the caller's representation `M`, margin `ρ`
and right inverse `H`: `none` where the certificate does not go through. -/
def LinearSys.timePointStepInnerRepFloat (sys : LinearSys 𝕋 n) (r : 𝕋) (η : ℕ)
    (X₀ U : Zonotope (Vec 𝕋 n))
    (M : Fin (sys.timePointStepInputFloat r η X₀ U).h →
      Fin (sys.timePointStepInnerErrorFloat r η X₀ U).h → 𝕋) (ρ : 𝕋)
    (H : Mat 𝕋 (sys.timePointStepInputFloat r η X₀ U).h n) : Option (Zonotope (Vec 𝕋 n)) :=
  let S := sys.timePointStepInputFloat r η X₀ U                             -- the float step
  let B := sys.timePointStepInnerErrorFloat r η X₀ U                        -- what it owes
  S.minkDiffRep B M ρ H                                                     -- S ⊖ B, certified

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
