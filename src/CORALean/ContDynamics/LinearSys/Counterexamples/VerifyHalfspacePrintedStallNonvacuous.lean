module

public import CORALean.ContDynamics.LinearSys.Counterexamples.VerifyHalfspacePrintedStall

@[expose] public section

/-!
# The oracles of the printed `Alg. 2` stall exist

The hypotheses of `LinearSys.verifyHalfspacePrinted_stall_counterexample` on the oracles of
[1, Sec. 5.1 (termination)] can be met: the exact support function of the zonotopes, the point `1`
of `X₀`, and the end `±1` of `U` on the side `d` points to, which reaches at least the center `0`.
The counterexample is not vacuous.

## Inputs
* none

## Hypotheses
* none

## Conclusion
* a sound support function oracle and support vectors meeting the contracts exist

## References

* [1] [M. Wetzlinger, N. Kochdumper, S. Bak and M. Althoff. "Fully-Automated Verification of Linear
      Systems Using Reachability Analysis with Support Functions". Proceedings of the 26th ACM
      International Conference on Hybrid Systems: Computation and Control,
      2023.](../../../../../references/2023/wetzlinger-hscc-support-functions.md)
-/

-- Authors:       Claude Opus 5.5
-- Written:       27-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real
open ContSet


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Sec. 5.1 (termination)]: there are oracles meeting every hypothesis of
`LinearSys.verifyHalfspacePrinted_stall_counterexample`. -/
theorem LinearSys.verifyHalfspacePrinted_stall_nonvacuous : -- --- CONCL ---
    let X₀ : Zonotope (Vec ℝ 1) := Zonotope.ofPoint (fun _ => 1)
    let U : Zonotope (Vec ℝ 1) := ⟨1, 0, fun _ => fun _ => 1⟩
    ∃ (ρ : Zonotope (Vec ℝ 1) → (Vec ℝ 1 →ₗ[ℝ] ℝ) → ℝ)
      (_ : ∀ X : Zonotope (Vec ℝ 1), ∀ x ∈ construct X, ∀ d : Vec ℝ 1 →ₗ[ℝ] ℝ, d x ≤ ρ X d)
      (ν₀ νU : (Vec ℝ 1 →ₗ[ℝ] ℝ) → Vec ℝ 1) (_ : ∀ d, ν₀ d ∈ construct X₀)
      (_ : ∀ d, νU d ∈ construct U),
      ∀ d : Vec ℝ 1 →ₗ[ℝ] ℝ, d 0 ≤ d (νU d) := by -- --- PROOF ---
  intro X₀ U
  -- the exact support function of a zonotope: bounded, so the supremum bounds every point
  have hbdd : ∀ (X : Zonotope (Vec ℝ 1)) (d : Vec ℝ 1 →ₗ[ℝ] ℝ),
      BddAbove ((fun x => d x) '' construct X) := fun X d =>
    ((LinearMap.toContinuousLinearMap d).lipschitz.isBounded_image
      (CompactSet.isBounded_construct X)).bddAbove
  -- the end of `U` on the side of `d`
  let νU : (Vec ℝ 1 →ₗ[ℝ] ℝ) → Vec ℝ 1 := fun d =>
    if 0 ≤ d (fun _ => 1) then fun _ => 1 else fun _ => -1
  have hνU : ∀ d, νU d ∈ construct U := by
    intro d
    by_cases h : 0 ≤ d (fun _ => 1)
    · exact ⟨fun _ => 1, by simp, by funext i; simp [νU, h, U]⟩
    · exact ⟨fun _ => -1, by simp, by funext i; simp [νU, h, U]⟩
  refine ⟨fun X d => sSup ((fun x => d x) '' construct X),
    fun X x hx d => le_csSup (hbdd X d) ⟨x, hx, rfl⟩, fun _ => fun _ => 1, νU,
    fun _ => OfPoint.mem_ofPoint _, hνU, fun d => ?_⟩
  rw [map_zero]
  by_cases h : 0 ≤ d (fun _ => 1)
  · simp [νU, h]
  · have hneg : (fun _ => (-1 : ℝ) : Vec ℝ 1) = -(fun _ => 1) := by funext i; simp
    simp only [νU, h, if_false, hneg, map_neg]
    linarith

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
