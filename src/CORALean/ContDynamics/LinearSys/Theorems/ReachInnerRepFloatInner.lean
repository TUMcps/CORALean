module

public import CORALean.ContDynamics.LinearSys.Definitions.ReachSet
public import CORALean.ContDynamics.LinearSys.Operations.ReachInnerRepFloat
public import CORALean.ContDynamics.LinearSys.Theorems.DiscretizeEnclosureFloatReachSubsetAddErrorFloat
public import CORALean.ContDynamics.LinearSys.Theorems.DiscretizeReachSetSubsetInputReach
public import CORALean.ContDynamics.LinearSys.Theorems.ReachSetSuperset
public import CORALean.ContDynamics.LinearSysDT.Theorems.ReachSetInnerOfOuter
public import CORALean.ContSet.Zonotope.Float.Theorems.CentreMemConstruct
public import CORALean.ContSet.Zonotope.Float.Theorems.IsCompact
public import CORALean.ContSet.Zonotope.Float.Theorems.MinkDiffRepInner
public import CORALean.ContSet.Zonotope.Real.Theorems.CentreMemConstruct
public import CORALean.ContSet.Zonotope.Real.Theorems.Convex
public import CORALean.ContSet.Zonotope.Real.Theorems.IsBounded
public import CORALean.ContSet.Zonotope.Real.Theorems.IsCompact
public import CORALean.ContSet.Zonotope.Real.Theorems.MtimesExact

@[expose] public section

/-!
# `reachInnerRepFloat` is an inner approximation

`reachInnerRep_inner` at the float layer, by the chain `reachInner_inner` uses,
each step in the direction an inner approximation needs:

1. `minkDiffRep_inner`: what the float `minkDiffRep` returns lies inside the
   float run minus its budget (`D ⊆ R ⊖ B`).
2. `discretizeEnclosureFloat_reach_subset_add_errorFloat` puts the float run
   inside the exact held-input sampled set plus the budget (`R ⊆ Y + B`), so
   Rådström cancellation (`reachSet_inner_of_outer`, `Y` convex and compact)
   gives `R ⊖ B ⊆ Y`.
3. `Y` lies in the states the system reaches at `t = kΔt`
   (`discretize_reachSet_subset_inputReach`, then
   `mulVecLin_image_add_inputReach_subset_reachSet`).

The exact reachable set is read from the nominal zonotopes of `R₀` and `U`; the
float sets' error boxes are paid inside the budget. The budget is nonempty
because the float run is (its error box brackets `0`).
-/

-- Authors:       Claude Opus 5.5
-- Written:       09-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float FloatOps SoundFloatArithmetic InflatedContSet Matrix NormedSpace
open scoped Pointwise

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- Whatever `reachInnerRepFloat` returns is *contained in* the states the system reaches at
`t = kΔt` from the nominal zonotopes of `R₀` and `U`, at `Δt > 0` and an admissible order,
given both error boxes bracket `0`. -/
theorem LinearSys.reachInnerRepFloat_inner (sys : LinearSys 𝕋 n) {Δt : 𝕋} (hΔt : 0 < toReal Δt)
    {η : ℕ} (hη : sys.OrderAdmissibleFloat Δt Δt η) {o : ℕ} (ho : 0 < o) {R₀ U : Zonotope (Vec 𝕋 n)}
    (hR₀ : (0 : Vec ℝ n) ∈ R₀.E.construct) (hU : (0 : Vec ℝ n) ∈ U.E.construct) (k : ℕ)
    (M : Fin ((sys.discretizeEnclosureFloat Δt η).reach (S := fun k => Zonotope (Vec 𝕋 k))
        ⟨R₀, sys.inputSolutionFloat Δt η U, 0, k⟩ ⟨o, ho⟩).h →
      Fin (sys.reachErrorFloat Δt η o ho R₀ U k).h → 𝕋) (ρ : 𝕋)
    (H : Mat 𝕋 ((sys.discretizeEnclosureFloat Δt η).reach (S := fun k => Zonotope (Vec 𝕋 k))
        ⟨R₀, sys.inputSolutionFloat Δt η U, 0, k⟩ ⟨o, ho⟩).h n) {D : Zonotope (Vec 𝕋 n)}
    (hD : sys.reachInnerRepFloat Δt η o ho R₀ U k M ρ H = some D) :
    D.construct ⊆ sys.reachSet (S := fun k => Real.Zonotope (Vec ℝ k))
      (Set.Icc 0 ((k : ℝ) * toReal Δt)) (nominal R₀) (nominal U)
      ((k : ℝ) * toReal Δt) := by -- --- PROOF ---
  set R := (sys.discretizeEnclosureFloat Δt η).reach (S := fun k => Zonotope (Vec 𝕋 k))
    ⟨R₀, sys.inputSolutionFloat Δt η U, 0, k⟩ ⟨o, ho⟩
  set B := sys.reachErrorFloat Δt η o ho R₀ U k
  set Q := Real.Zonotope.mtimes (Real.MatExp.expIntegral (Scalar.toRealMat sys.A) (toReal Δt))
    (nominal U)
  have hout := sys.discretizeEnclosureFloat_reach_subset_add_errorFloat hΔt hη ho hR₀ hU k
  -- the budget is nonempty: the float run holds its centre, and lies in `Y + B`
  have hR0 : (0 : Vec ℝ n) ∈ R.E.construct :=
    sys.zero_mem_discretizeEnclosureFloat_reach_error hΔt.le hη ho hR₀ hU k
  obtain ⟨_, -, b, hb, -⟩ := hout (Zonotope.centre_mem_construct R hR0)
  have hinner := (sys.discretize (toReal Δt)).reachSet_inner_of_outer
    (S := fun k => Real.Zonotope (Vec ℝ k))
    (Real.Zonotope.convex_construct (nominal R₀)) (Real.Zonotope.isCompact_construct (nominal R₀))
    (Real.Zonotope.convex_construct Q) (Real.Zonotope.isCompact_construct Q) k
    ⟨b, hb⟩ (Zonotope.isCompact_construct B).isBounded hout
  -- each step's held input is `stepInputConst` at a point of `U`
  have hstep : ContSet.construct Q
      ⊆ (fun c => sys.stepInputConst c (toReal Δt)) '' ContSet.construct (nominal U) := by
    intro v hv
    have hv' : v ∈ Q.construct := hv
    rw [← Real.Zonotope.mtimes_exact] at hv'
    obtain ⟨c, hc, rfl⟩ := hv'
    exact ⟨c, hc, rfl⟩
  have hzoh := sys.discretize_reachSet_subset_inputReach (S := fun k => Real.Zonotope (Vec ℝ k))
    hΔt (nominal R₀) (nominal U) Q (Real.Zonotope.isBounded_construct _)
    ⟨_, Real.Zonotope.centre_mem_construct _⟩ hstep k
  exact (Zonotope.minkDiffRep_inner hD).trans (hinner.trans (hzoh.trans
    (sys.mulVecLin_image_add_inputReach_subset_reachSet
      (S := fun k => Real.Zonotope (Vec ℝ k)) (nominal R₀) (nominal U) (by positivity)
      (Real.Zonotope.isBounded_construct _))))

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
