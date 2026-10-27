module

public import CORALean.Specification.Counterexamples.VerifyHalfspacePrinted
public import CORALean.ContDynamics.LinearSys.Operations.Canonical
public import CORALean.ContDynamics.LinearSys.Theorems.SupportUpperOuter
public import CORALean.ContDynamics.LinearSys.Theorems.SupportLowerTimeIntervalLe
public import CORALean.ContDynamics.LinearSys.Theorems.SupportLowerMemImageReachSetExact
public import CORALean.ContDynamics.LinearSys.Theorems.IsTrajectoryHeldInput
public import CORALean.ContDynamics.LinearSys.Theorems.ClosedFormZero
public import CORALean.ContSet.ContSet.Theorems.Basic
public import CORALean.ContSet.Zonotope.Real.Instances

@[expose] public section

/-!
# [1, Sec. 5.1 (termination)]: an unsafe, decidable instance on which `Alg. 2` never halts

`Alg. 2` as printed tests falsification (line 9) only under a failed safety test (line 7), and a
lower bound of `Alg. 1` never exceeds the upper bound of the same step. For `ẋ = x + u`,
`X₀ = {1}`, `U = [-1, 1]`, `t_end = 1` and the safe set `x ≤ 0`, the state `1` of `R(0)` violates
it by `1`. Yet line 9 never fires, the upper bound of the first step stays above `0` in every
round, and `verifyHalfspacePrinted` answers `undecided` for every `fuel`, truncation order and
sound oracle.

## Inputs
* `m` – Taylor order `η = m + 2`

## Hypotheses
* none

## Conclusion
* the unsafe instance stays undecided for every fuel and sound oracle

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
open Matrix ContSet Scalar NormedSpace

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Sec. 5.1 (termination)]: `R(0)` holds a state `1` above the offset `0`, yet `Alg. 2` as
printed answers `undecided` for every `fuel`, `η` and sound oracle. -/
theorem LinearSys.verifyHalfspacePrinted_stall_counterexample (m : ℕ) : -- --- CONCL ---
    let sys : LinearSys ℝ 1 := LinearSys.canonical 1
    let X₀ : Zonotope (Vec ℝ 1) := Zonotope.ofPoint (fun _ => 1)
    let U : Zonotope (Vec ℝ 1) := ⟨1, 0, fun _ => fun _ => 1⟩
    let H : Unit → (Vec ℝ 1 →ₗ[ℝ] ℝ) := fun _ => LinearMap.proj 0
    let f : Unit → ℝ := fun _ => 0
    -- decidable: a state of `R(0)` violates `H x ≤ f` by `1`
    (∃ x ∈ sys.reachSetExact (S := 𝒵) (Set.Icc 0 1) X₀ U 0, ∀ i, f i + 1 ≤ H i x) ∧
    -- and yet, for every sound oracle, `Alg. 2` as printed never exits
    ∀ (ρ : Zonotope (Vec ℝ 1) → (Vec ℝ 1 →ₗ[ℝ] ℝ) → ℝ)
      (_ : ∀ X : Zonotope (Vec ℝ 1), ∀ x ∈ construct X, ∀ d : Vec ℝ 1 →ₗ[ℝ] ℝ, d x ≤ ρ X d)
      (ν₀ νU : (Vec ℝ 1 →ₗ[ℝ] ℝ) → Vec ℝ 1) (_ : ∀ d, ν₀ d ∈ construct X₀)
      (_ : ∀ d, νU d ∈ construct U) (_ : ∀ d : Vec ℝ 1 →ₗ[ℝ] ℝ, d 0 ≤ d (νU d))
      (fuel : ℕ),
      verifyHalfspacePrinted
        (fun r k i => (sys.supportUpper (S := 𝒵) (1 / 2 ^ r) (m + 2) X₀ U ρ (H i)
          ((k : ℕ) + 1)).ρRτ)
        (fun r k i => (sys.supportLower (1 / 2 ^ r) ν₀ νU 0 (H i) ((k : ℕ) + 1)).ρRτ)
        f fuel [()] = .undecided := by -- --- PROOF ---
  intro sys X₀ U H f
  have hA : toRealMat sys.A = 1 := rfl
  have hnormA : ‖toRealMat sys.A‖ = 1 := by rw [hA]; exact norm_one
  have hUbdd : Bornology.IsBounded (construct U) := CompactSet.isBounded_construct U
  have hX₀ : ∀ z ∈ construct X₀, z 0 = 1 := by
    rintro z ⟨β, -, rfl⟩
    simp [X₀, Zonotope.ofPoint]
  have h0U : (0 : Vec ℝ 1) ∈ construct U := ⟨fun _ => 0, by simp, by funext i; simp [U]⟩
  refine ⟨?_, ?_⟩
  · -- the run from `1` under the input `0` sits at `1` at time `0`
    have hx₀ : (fun _ => (1 : ℝ)) ∈ construct X₀ := OfPoint.mem_ofPoint _
    refine ⟨_, ⟨_, _, sys.isTrajectory_heldInput (S := 𝒵) X₀ U hUbdd zero_le_one 1 hx₀
      (v := fun _ => 0) (fun _ => h0U), rfl⟩, fun _ => ?_⟩
    rw [sys.closedForm_zero]
    simp [f, H]
  intro ρ hρ ν₀ νU hν₀ hνU hc fuel
  -- the steps of every round are `Δt = 1 / 2 ^ r ≤ 1`, small enough for `Alg. 1`
  have hΔt : ∀ r : ℕ, (0 : ℝ) < 1 / 2 ^ r := fun r => by positivity
  have hε : ∀ r : ℕ, ‖(1 / 2 ^ r : ℝ) • toRealMat sys.A‖ / (((m + 2 : ℕ) : ℝ) + 2) < 1 := by
    intro r
    rw [norm_smul, hnormA, mul_one, Real.norm_of_nonneg (hΔt r).le,
      div_lt_one (by positivity)]
    have : (1 : ℝ) / 2 ^ r ≤ 1 := div_le_one_of_le₀ (one_le_pow₀ (by norm_num)) (by positivity)
    push_cast
    linarith
  -- line 16 is at most line 13 at every step: both bound `R` over `τ_k`
  have hle : ∀ (r : ℕ) (k : Fin (2 ^ r)) (i : Unit),
      (sys.supportLower (1 / 2 ^ r) ν₀ νU 0 (H i) ((k : ℕ) + 1)).ρRτ ≤
        (sys.supportUpper (S := 𝒵) (1 / 2 ^ r) (m + 2) X₀ U ρ (H i) ((k : ℕ) + 1)).ρRτ := by
    intro r k i
    have hlo := sys.supportLower_timeInterval_le (1 / 2 ^ r) ν₀ νU hc (H i) k
    obtain ⟨x, hx, hxe⟩ := sys.supportLower_mem_image_reachSetExact (S := 𝒵) X₀ U hUbdd
      (hΔt r) hν₀ hνU 0 (H i) k
    obtain ⟨x', hx', hxe'⟩ := sys.supportLower_mem_image_reachSetExact (S := 𝒵) X₀ U hUbdd
      (hΔt r) hν₀ hνU 0 (H i) (k + 1)
    have hup := (sys.supportUpper_outer (S := 𝒵) (hΔt r) (hε r) X₀ U hρ (H i) k).2
    have hkk : ((k : ℕ) : ℝ) * (1 / 2 ^ r) ≤ (((k : ℕ) + 1 : ℕ) : ℝ) * (1 / 2 ^ r) := by
      gcongr
      exact_mod_cast Nat.le_succ _
    have h1 := hup _ ⟨le_rfl, hkk⟩ x hx
    have h2 := hup _ ⟨hkk, le_rfl⟩ x' hx'
    rw [hxe] at h1
    rw [hxe'] at h2
    exact hlo.trans (max_le h1 h2)
  -- line 13 of the first step bounds the state `1` of `R(0)`, so line 7 fires in every round
  have hup : ∀ r : ℕ, ∃ k : Fin (2 ^ r), f () <
      (sys.supportUpper (S := 𝒵) (1 / 2 ^ r) (m + 2) X₀ U ρ (H ()) ((k : ℕ) + 1)).ρRτ := by
    intro r
    refine ⟨⟨0, by positivity⟩, ?_⟩
    obtain ⟨x, hx, hxe⟩ := sys.supportLower_mem_image_reachSetExact (S := 𝒵) X₀ U hUbdd
      (hΔt r) hν₀ hνU 0 (H ()) 0
    have hval : (sys.supportLower (1 / 2 ^ r) ν₀ νU 0 (H ()) 0).ρR = 1 := by
      simp only [LinearSys.supportLower, add_zero, H, LinearMap.proj_apply]
      exact hX₀ _ (hν₀ _)
    have h0 : ((0 : ℕ) : ℝ) * (1 / 2 ^ r) ≤ ((0 + 1 : ℕ) : ℝ) * (1 / 2 ^ r) := by
      push_cast; simp only [zero_mul, one_mul]; exact (hΔt r).le
    have h1 := (sys.supportUpper_outer (S := 𝒵) (hΔt r) (hε r) X₀ U hρ (H ()) 0).2 _
      ⟨le_rfl, h0⟩ x hx
    rw [hxe, hval] at h1
    simp only [f]
    linarith
  exact verifyHalfspacePrinted_eq_undecided hle hup fuel [()] (List.mem_singleton_self _)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
