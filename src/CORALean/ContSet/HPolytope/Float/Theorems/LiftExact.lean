module

public import CORALean.ContSet.HPolytope.Float.Theorems.MemConstruct
public import CORALean.ContSet.HPolytope.Float.Operations.Lift
public import CORALean.ContSet.HPolytope.Float.Operations.MemLiftNominalIff
public import CORALean.ContSet.HPolytope.Float.Theorems.LiftErrorBox
public import CORALean.ContSet.HPolytope.Float.Theorems.PreimageAddImage
public import Mathlib.LinearAlgebra.Pi

@[expose] public section

/-!
# `HPolytope.lift_` is exact

The lifted polytope is the set of points whose selected coordinates lie in the original, as the
exact layer's `lift_exact` states it: nothing rounds, the stored right-hand sides are unchanged,
and the error box is lifted with zeros in the free coordinates (`lift_errorBox`), so the lifted
box plus the lifted rows is the lifted sum.

## Inputs
* `P` – H-polytope
* `dims` – indices indexed by `Fin n`

## Hypotheses
* `hdims` – `dims` is injective

## Conclusion
* the lift is the set of points whose selected coordinates lie in `P`
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       02-October-2026
-- Last update:   15-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Pointwise FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n N : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem HPolytope.lift_exact (P : HPolytope 𝕋 (Vec 𝕋 n)) {dims : Fin n → Fin N}
    (hdims : Function.Injective dims) :
    (P.lift_ dims).construct =
      {x : Vec ℝ N | (fun k => x (dims k)) ∈ P.construct} := by -- --- PROOF ---
  ext x
  show x ∈ (P.lift_ dims).nominal.construct + (P.lift_ dims).I_error.construct ↔
    (fun k => x (dims k)) ∈ P.nominal.construct + P.I_error.construct
  have hN : (P.lift_ dims).nominal.construct
      = ⇑(LinearMap.funLeft ℝ ℝ dims).toAddMonoidHom ⁻¹' P.nominal.construct := by
    ext y
    exact HPolytope.mem_lift_nominal_iff P hdims
  have key := HPolytope.preimage_inter_add_image
    (LinearMap.funLeft ℝ ℝ dims).toAddMonoidHom (Function.ExtendByZero.hom ℝ dims)
    (fun e => funext fun k => hdims.extend_apply _ _ k) P.nominal.construct
    P.I_error.construct Set.univ (fun _ _ => by simp)
  simp only [Set.inter_univ] at key
  rw [hN, HPolytope.lift_errorBox P hdims]
  exact (Set.ext_iff.mp key x).trans Iff.rfl

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
