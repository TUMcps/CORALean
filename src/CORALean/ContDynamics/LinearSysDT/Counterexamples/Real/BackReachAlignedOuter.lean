module

public import CORALean.ContDynamics.LinearSysDT.Theorems.Real.BackReachAlignedOuter
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.LinearAlgebra.Matrix.Notation

@[expose] public section

/-!
# (13) with (max-in) over `W`'s halfspaces does not enclose the robust backward reachable set

[1, Prop. 5], the outer half `X_k ⊆ Z̄_k`, takes each step's aligned zonotope from (max-in),
built from the H-representation `(H, h)` of `W` and not of `EW`. One dimension is enough:
`A = 1`, `B = 0`, `K = 0`, `U = {0}`, `E = ½`, `W = [-1, 1]` (`H = (1, -1)ᵀ`, `h = (1, 1)`) and
`Z₀ = [-1, 1]`. The maximizer of (max-in) at `Z₀` with [1]'s weights `dᵢ = ‖gᵢ‖` is `α = 1`,
`c = 0` (`Zonotope.aligned_subset_of_maxIn_counterexample`), so the first step of (13) is
`Z₀ ⊖ Z₀ = {0}`, while `X₁ = [-½, ½]`.

## Inputs
* none

## Hypotheses
* none

## Conclusion
* the aligned-zonotope enclosure fails for some system

## References

* [1] L. Yang and N. Ozay. "Scalable zonotopic under-approximation of backward reachable sets for
      uncertain linear systems". IEEE Control Systems Letters, 2022.
-/

-- Authors:       Claude Opus 5.5
-- Written:       08-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real
open Matrix Pointwise


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Prop. 5], `X_k ⊆ Z̄_k`, as printed: every step's scalings a maximizer of (max-in) over
`W`'s halfspaces, with `A` invertible (A3). -/
theorem LinearSysDT.backReachAligned_outer_counterexample : -- --- CONCL ---
    ¬ ∀ (n m q : ℕ) (A : Mat ℝ n n), IsUnit A.det → ∀ (B : Mat ℝ n m) (E : Mat ℝ n n)
      (K : Vec ℝ n) (U : Zonotope (Vec ℝ m)) (H : Mat ℝ q n) (h : Vec ℝ q)
      (Z₀ : Zonotope (Vec ℝ n)) (σ : (Z : Zonotope (Vec ℝ n)) → Vec ℝ n × (Fin Z.h → ℝ))
      (k : ℕ),
      (∀ j < k, let Zj := Zonotope.backReachAligned A B K U Z₀ σ j
        (∀ i, 0 ≤ (σ Zj).2 i ∧ (σ Zj).2 i ≤ 1) ∧
        (∀ l, (H *ᵥ (σ Zj).1) l + ∑ i, |(H *ᵥ Zj.G i) l| * (σ Zj).2 i ≤ h l) ∧
        (∀ (c' : Vec ℝ n) (a' : Fin Zj.h → ℝ), (∀ i, 0 ≤ a' i ∧ a' i ≤ 1) →
          (∀ l, (H *ᵥ c') l + ∑ i, |(H *ᵥ Zj.G i) l| * a' i ≤ h l) →
          ∑ i, ‖Zj.G i‖ * Real.log (a' i) ≤ ∑ i, ‖Zj.G i‖ * Real.log ((σ Zj).2 i))) →
      LinearSysDT.backReachSetRobustExact A B E K U.construct {w | ∀ l, (H *ᵥ w) l ≤ h l}
          Z₀.construct k
        ⊆ (Zonotope.backReachAligned A B K U Z₀ σ k).construct := by -- --- PROOF ---
  intro hall
  -- the maximizer of (max-in) at `Z₀` is `α = 1`, `c = 0`
  have hsub := hall 1 1 2 1 (by simp) 0 !![1 / 2] 0 ⟨0, 0, fun i => i.elim0⟩ !![1; -1] ![1, 1]
    ⟨1, 0, fun _ _ => 1⟩ (fun _ => (0, fun _ => 1)) 1 (by
      intro j hj
      obtain rfl : j = 0 := by omega
      intro Zj
      have hZ : Zj = ⟨1, 0, fun _ _ => 1⟩ := rfl
      rw [hZ]
      refine ⟨fun _ => ⟨zero_le_one, le_rfl⟩, ?_, ?_⟩
      -- feasible: `±0 + 1 ≤ 1`
      · intro l
        fin_cases l <;> simp [Matrix.mulVec, dotProduct]
      -- maximal: every feasible `α' ≤ 1` has `log α' ≤ 0 = log 1`
      · intro c' a' ha' _
        simp only [Real.log_one, mul_zero, Finset.sum_const_zero]
        exact Finset.sum_nonpos fun i _ =>
          mul_nonpos_of_nonneg_of_nonpos (norm_nonneg _)
            (Real.log_nonpos (ha' i).1 (ha' i).2))
  -- `1/2` is in `X₁`: `u = 0`, and `1/2 + w/2 ∈ [-1, 1]` for every `w ∈ [-1, 1]`
  have hmem := hsub (show (fun _ => 1 / 2 : Vec ℝ 1) ∈ _ from
    ⟨0, ⟨fun j => j.elim0, fun j => j.elim0, by simp⟩, fun w hw => by
      have h0 := hw 0
      have h1 := hw 1
      simp [Matrix.mulVec, dotProduct] at h0 h1
      refine ⟨fun _ => 1 / 2 + w 0 / 2, fun _ => abs_le.mpr ⟨by linarith, by linarith⟩, ?_⟩
      funext i
      fin_cases i
      simp [dotProduct]
      ring⟩)
  -- but `Z̄₁ = Z₀ ⊖ Z₀ = {0}`
  obtain ⟨d, hd, _, ⟨u, hu, rfl⟩, hsum⟩ :=
    (Zonotope.mem_backReachAligned_succ_iff (A := (1 : Mat ℝ 1 1)) (by simp) _ _ _ _ _ 0 _).mp hmem
  obtain ⟨β, hβ, hd0⟩ := hd
  have hd' : d = 0 := by
    rw [hd0]
    simp [Zonotope.minkDiffAligned, Zonotope.aligned, Zonotope.backReachAligned]
  have h1 := congrFun hsum 0
  simp [hd'] at h1

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
