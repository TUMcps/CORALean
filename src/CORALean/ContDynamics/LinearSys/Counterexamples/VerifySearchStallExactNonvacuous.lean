module

public import CORALean.ContDynamics.LinearSys.Counterexamples.VerifySearchStall

@[expose] public section

/-!
# The oracles of the stall at the algorithm's own tests exist

The hypotheses of `LinearSys.verifySearch_stall_exact_counterexample` on the support function
oracles of [1, Alg. 3 (termination)] can be met for every `η`: the exact support function of the
zonotopes, the point `0` of `X₀`, the generator end `1` of `U`, the one point of `L`, and a support
vector of the outer approximation at the value of `ρR`. The corollary is not vacuous.

## Inputs
* `η` – Taylor order

## Hypotheses
* none

## Conclusion
* sound support function oracles with matching support vectors exist

## References

* [1] [M. Wetzlinger, N. Kochdumper, S. Bak and M. Althoff. "Fully-Automated Verification of
      Linear Systems Using Reachability Analysis with Support Functions". Proceedings of the 26th
      ACM International Conference on Hybrid Systems: Computation and Control,
      2023.](../../../../../references/2023/wetzlinger-hscc-support-functions.md)
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       27-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real
open Matrix ContSet Scalar NormedSpace

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Alg. 3 (termination)]: for every `η` there are support function oracles meeting every
hypothesis of `LinearSys.verifySearch_stall_exact_counterexample`. -/
theorem LinearSys.verifySearch_stall_exact_nonvacuous (η : ℕ) : -- --- CONCL ---
    let sys : LinearSys ℝ 1 := LinearSys.canonical 1
    let X₀ : Zonotope (Vec ℝ 1) := Zonotope.ofPoint 0
    let U : Zonotope (Vec ℝ 1) := ⟨1, 0, fun _ => fun _ => 1⟩
    let c : ℝ := (∑ i ∈ Finset.range (η + 1), 1 / ((i + 1).factorial : ℝ)) +
      1 / ((η + 1).factorial : ℝ)
    let L : Set (Vec ℝ 1) := {fun _ => c}
    let ℓ₁ : Vec ℝ 1 →ₗ[ℝ] ℝ := LinearMap.proj 0
    ∃ (ρ : Zonotope (Vec ℝ 1) → (Vec ℝ 1 →ₗ[ℝ] ℝ) → ℝ)
      (_ : ∀ X : Zonotope (Vec ℝ 1), ∀ x ∈ construct X, ∀ d : Vec ℝ 1 →ₗ[ℝ] ℝ, d x ≤ ρ X d)
      (ν₀ νU νL : (Vec ℝ 1 →ₗ[ℝ] ℝ) → Vec ℝ 1) (_ : ∀ d, ν₀ d ∈ construct X₀)
      (_ : ∀ d, νU d ∈ construct U) (_ : ∀ d, νL d ∈ L)
      (ρL : (Vec ℝ 1 →ₗ[ℝ] ℝ) → ℝ) (_ : ∀ d, ∀ y ∈ L, d y ≤ ρL d)
      (νhat : ℝ → (Vec ℝ 1 →ₗ[ℝ] ℝ) → Vec ℝ 1),
      ℓ₁ (νhat 1 ℓ₁) = (sys.supportUpper (S := 𝒵) 1 η X₀ U ρ ℓ₁ 1).ρR := by -- --- PROOF ---
  intro sys X₀ U c L ℓ₁
  -- the exact support function of a zonotope: bounded, so the supremum bounds every point
  have hbdd : ∀ (X : Zonotope (Vec ℝ 1)) (d : Vec ℝ 1 →ₗ[ℝ] ℝ),
      BddAbove ((fun x => d x) '' construct X) := fun X d =>
    ((LinearMap.toContinuousLinearMap d).lipschitz.isBounded_image
      (CompactSet.isBounded_construct X)).bddAbove
  refine ⟨fun X d => sSup ((fun x => d x) '' construct X),
    fun X x hx d => le_csSup (hbdd X d) ⟨x, hx, rfl⟩, fun _ => 0, fun _ => fun _ => 1,
    fun _ => fun _ => c, fun _ => OfPoint.mem_ofPoint (0 : Vec ℝ 1), fun _ => ?_, fun _ => rfl,
    fun d => d (fun _ => c), fun d y hy => by rw [Set.mem_singleton_iff.mp hy],
    fun _ _ => fun _ => (sys.supportUpper (S := 𝒵) 1 η X₀ U
      (fun X d => sSup ((fun x => d x) '' construct X)) ℓ₁ 1).ρR, rfl⟩
  exact ⟨fun _ => 1, by simp, by funext i; simp [U]⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
