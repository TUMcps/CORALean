module

public import CORALean.ContDynamics.LinearSys.Definitions.ReachSetExact
public import CORALean.ContDynamics.LinearSys.Operations.TimePointStepInnerRepFloat
public import CORALean.ContDynamics.LinearSys.Theorems.DiscretizeReachSetExactSubsetInputReach
public import CORALean.ContDynamics.LinearSys.Theorems.ReachSetExactSuperset
public import CORALean.ContDynamics.LinearSys.Theorems.TimePointStepInputFloatSubsetAddInnerErrorFloat
public import CORALean.ContDynamics.LinearSys.Theorems.ZeroMemTimePointStepInputFloatError
public import CORALean.ContDynamics.LinearSysDT.Theorems.ReachSetExactInnerOfOuter
public import CORALean.ContSet.Zonotope.Float.Theorems.CenterMemConstruct
public import CORALean.ContSet.Zonotope.Float.Theorems.IsCompact
public import CORALean.ContSet.Zonotope.Float.Theorems.MinkDiffRepInner
public import CORALean.ContSet.Zonotope.Real.Theorems.CenterMemConstruct
public import CORALean.ContSet.Zonotope.Real.Theorems.Convex
public import CORALean.ContSet.Zonotope.Real.Theorems.IsBounded
public import CORALean.ContSet.Zonotope.Real.Theorems.IsCompact
public import CORALean.ContSet.Zonotope.Real.Theorems.MtimesExact

@[expose] public section

/-!
# `timePointStepInnerRepFloat` is an inner approximation

`timePointStepInnerRep_inner` at the float layer, by three steps, each in the direction an inner
approximation needs. (1) `minkDiffRep_inner`: what the float `minkDiffRep` returns lies inside the
float step minus its budget (`D ⊆ S ⊖ B`). (2) `timePointStepInputFloat_subset_add_innerErrorFloat`
puts the float step inside the exact held-input step plus the budget (`S ⊆ Y + B`), so Rådström
cancellation (`reachSetExact_inner_of_outer`, `Y` convex and compact) gives `S ⊖ B ⊆ Y`. (3) `Y`,
the held-input step from the nominal zonotopes, lies in the states the system reaches at `t = r`
(`discretize_reachSetExact_subset_inputReach`, then
`mulVecLin_image_add_inputReach_subset_reachSetExact`).

## Inputs
* `sys` – linear system
* `r` – float step length
* `η` – Taylor order
* `X₀` – initial float zonotope
* `U` – input float zonotope
* `M` – generator representation
* `ρ` – margin factor
* `H` – right inverse

## Hypotheses
* `hr` – step length positive
* `hη` – order admissible
* `hX₀` – initial error box contains zero
* `hU` – input error box contains zero

## Conclusion
* every returned zonotope lies in the exact reach set at the step end
-/

-- Authors:       Claude Opus 5.5
-- Written:       09-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float FloatOps SoundFloatArithmetic InflatedContSet Matrix NormedSpace
open scoped Pointwise
open scoped CORALean.Real

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- Whatever `timePointStepInnerRepFloat` returns is *contained in* the states the system
reaches at `t = r` from the nominal zonotopes of `X₀` and `U`, at `r > 0` and an admissible
order, given both error boxes bracket `0`. -/
theorem LinearSys.timePointStepInnerRepFloat_inner (sys : LinearSys 𝕋 n) {r : 𝕋} (hr : 0 < toReal r)
    {η : ℕ} (hη : sys.IsOrderAdmissibleFloat r r η) {X₀ U : Zonotope (Vec 𝕋 n)}
    (hX₀ : (0 : Vec ℝ n) ∈ X₀.I_error.construct) (hU : (0 : Vec ℝ n) ∈ U.I_error.construct)
    (M : Fin (sys.timePointStepInputFloat r η X₀ U).h →
      Fin (sys.timePointStepInnerErrorFloat r η X₀ U).h → 𝕋) (ρ : 𝕋)
    (H : Mat 𝕋 (sys.timePointStepInputFloat r η X₀ U).h n) : -- --- CONCL ---
    ∀ D ∈ sys.timePointStepInnerRepFloat r η X₀ U M ρ H,
      D.construct ⊆ sys.reachSetExact (S := 𝒵)
        (Set.Icc 0 (toReal r)) (nominal X₀) (nominal U) (toReal r) := by -- --- PROOF ---
  intro D (hD : sys.timePointStepInnerRepFloat r η X₀ U M ρ H = some D)
  set S := sys.timePointStepInputFloat r η X₀ U
  set B := sys.timePointStepInnerErrorFloat r η X₀ U
  set Q := Real.Zonotope.mtimes (Real.MatExp.expIntegral (Scalar.toRealMat sys.A) (toReal r))
    (nominal U)
  have hout := sys.timePointStepInputFloat_subset_add_innerErrorFloat hr hη hX₀ hU
  -- the budget is nonempty: the float step holds its center, and lies in `Y + B`
  have hS0 : (0 : Vec ℝ n) ∈ S.I_error.construct :=
    sys.zero_mem_timePointStepInputFloat_error hr.le hη hX₀ hU
  obtain ⟨_, -, b, hb, -⟩ := hout (Zonotope.center_mem_construct S hS0)
  have hinner := (sys.discretize (toReal r)).reachSetExact_inner_of_outer
    (S := 𝒵)
    (Real.Zonotope.convex_construct (nominal X₀)) (Real.Zonotope.isCompact_construct (nominal X₀))
    (Real.Zonotope.convex_construct Q) (Real.Zonotope.isCompact_construct Q) 1
    ⟨b, hb⟩ (Zonotope.isCompact_construct B).isBounded hout
  -- each step's held input is `stepInputConst` at a point of `U`
  have hstep : ContSet.construct Q
      ⊆ (fun c => sys.stepInputConst c (toReal r)) '' ContSet.construct (nominal U) := by
    intro v hv
    have hv' : v ∈ Q.construct := hv
    rw [← Real.Zonotope.mtimes_exact] at hv'
    obtain ⟨c, hc, rfl⟩ := hv'
    exact ⟨c, hc, rfl⟩
  have hzoh := sys.discretize_reachSetExact_subset_inputReach (S := 𝒵)
    hr (nominal X₀) (nominal U) Q (Real.Zonotope.isBounded_construct _)
    ⟨_, Real.Zonotope.center_mem_construct _⟩ hstep 1
  have hint := sys.mulVecLin_image_add_inputReach_subset_reachSetExact
    (S := 𝒵) (nominal X₀) (nominal U)
    (t := ((1 : ℕ) : ℝ) * toReal r) (by positivity) (Real.Zonotope.isBounded_construct _)
  rw [Nat.cast_one, one_mul] at hzoh hint
  exact (Zonotope.minkDiffRep_inner _ hD).trans (hinner.trans (hzoh.trans hint))

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
