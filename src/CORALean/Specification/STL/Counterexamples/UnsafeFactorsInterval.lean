module

public import CORALean.Specification.STL.Operations.UnsafeFactors
public import CORALean.Specification.STL.Theorems.DepReachIntervalSumEval
public import CORALean.Specification.STL.Theorems.DepBloatingC
public import CORALean.Specification.STL.Theorems.ExpIntegralZeroOne
public import CORALean.ContDynamics.LinearSys.Operations.Canonical

@[expose] public section

/-!
# [1, Prop. 2] is false for the time interval polytope `K_i2`

A factor `α̃` outside `K_i2 = ⟨[C G_i2(·,N_i) 0], d - C c_i2 + Σ_{j∈M_i} |C G_i2(·,j)|⟩_P` of
`R(τ_i)`
of [1, Alg. 1] is claimed to have `ξ(t,x₀,u(·)) ∉ P` for all `t ∈ τ_i`; `N_i` is the layout of
`R(τ_i)` (the generators of `X₀`, then the input generators after those of the hull), `M_i` the
others. For `ẋ = u`, `X₀ = {0}`, `U = [-1,1]`, `Δt = 1`, `i = 0`, `R(τ₀) = [-1,1]`, `P = {x ≤ 1/2}`
the factor `α̃ = 1` is outside `K_i2` (`α̃ ≤ 1/2`), yet `ξ(1/4) = 1/4` is in `P`. The cause is [1,
Prop. 1] failing between the time points (`STL.depReachInterval_dependency_counterexample`); the
half for `K_i1` holds (`STL.not_mem_of_not_mem_unsafeFactors_point`).

## Inputs
* none

## Hypotheses
* none

## Conclusion
* the unsafe factor claim fails for the time interval polytope

## References

* [1] N. Kochdumper and S. Bak. "Fully Automated Verification of Linear Time-Invariant Systems
      against Signal Temporal Logic Specifications via Reachability Analysis". Nonlinear Analysis:
      Hybrid Systems, vol. 53, 2024, 101491.
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real Matrix NormedSpace

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The generators of `R(τ₀)` of the example: `(0, 1, 0, 0)`, read off the weighted sums. -/
theorem STL.aux_interval_G (k : Fin (STL.depReach (0 : Mat ℝ 1 1) (1 : Mat ℝ 1 1)
    (⟨0, 0, Fin.elim0⟩ : Zonotope (Vec ℝ 1)) (⟨1, 0, fun _ => fun _ => 1⟩ : Zonotope (Vec ℝ 1))
    1 1 0).2.h) : -- --- CONCL ---
    (STL.depReach (0 : Mat ℝ 1 1) (1 : Mat ℝ 1 1) (⟨0, 0, Fin.elim0⟩ : Zonotope (Vec ℝ 1))
      (⟨1, 0, fun _ => fun _ => 1⟩ : Zonotope (Vec ℝ 1)) 1 1 0).2.G k
      = if (k : ℕ) = 1 then (fun _ => (1 : ℝ) : Vec ℝ 1) else 0 := by -- --- PROOF ---
  -- the weighted sum with the indicator of `k` is the generator `k`
  have h := STL.depReachInterval_sum_eval (fun j => if j = (k : ℕ) then (1 : ℝ) else 0)
  simp only [] at h
  rw [Finset.sum_eq_single k] at h
  · simpa [eq_comm] using h
  · intro b _ hb
    have : (b : ℕ) ≠ k := fun e => hb (Fin.ext e)
    simp [this]
  · simp

theorem STL.aux_interval_c :
    (STL.depReach (0 : Mat ℝ 1 1) (1 : Mat ℝ 1 1) (⟨0, 0, Fin.elim0⟩ : Zonotope (Vec ℝ 1))
      (⟨1, 0, fun _ => fun _ => 1⟩ : Zonotope (Vec ℝ 1)) 1 1 0).2.c = 0 := by
  simp [STL.depReach, STL.depReachInterval, STL.depReachAt, STL.depReachStep, STL.depReachInit,
    STL.depReachConsts, STL.depBox, Zonotope.plus, Zonotope.mtimes, Zonotope.ofPoint,
    Zonotope.linComb, Zonotope.mtimesIntervalMat, STL.expIntegral_zero_one]
  exact STL.depBloating_c _ _ _ _ rfl

theorem STL.aux_interval_h : -- --- CONCL ---
    1 < (STL.depReach (0 : Mat ℝ 1 1) (1 : Mat ℝ 1 1) (⟨0, 0, Fin.elim0⟩ : Zonotope (Vec ℝ 1))
      (⟨1, 0, fun _ => fun _ => 1⟩ : Zonotope (Vec ℝ 1)) 1 1 0).2.h := by -- --- PROOF ---
  -- the indicator of `1` sums to `1 ≠ 0`, so there is a generator `1`
  by_contra hle
  have h := STL.depReachInterval_sum_eval (fun j => if j = 1 then (1 : ℝ) else 0)
  simp only [] at h
  rw [Finset.sum_eq_zero] at h
  · have := congrFun h 0
    simp at this
  · intro k _
    have hk : (k : ℕ) ≠ 1 := by have := k.2; omega
    simp [hk]


-- =======================================  MAIN THEOREM  ======================================= --

theorem STL.unsafeFactors_interval_counterexample : -- --- CONCL ---
    ¬ ∀ (n m : ℕ) (A : Mat ℝ n n) (B : Mat ℝ n m) (X₀ : Zonotope (Vec ℝ n))
      (U : Zonotope (Vec ℝ m)) (Δt : ℝ), 0 < Δt → ∀ (κ : ℕ) (α : ℕ → ℝ), (∀ k, |α k| ≤ 1) →
      ∀ (i : ℕ) (s : ℕ) (C : Matrix (Fin s) (Fin n) ℝ) (d : Fin s → ℝ) (h p : ℕ) (hp : h ≤ p),
      let R := (STL.depReach A B X₀ U Δt κ i).2
      ∀ (H : Fin h → Fin R.h) (K : Finset (Fin R.h)), StrictMono H →
      (∀ k : Fin R.h, k ∈ Set.range H ↔
        ((k : ℕ) < X₀.h ∨ (2 * X₀.h + 1 ≤ k ∧ (k : ℕ) < 2 * X₀.h + 1 + U.h * (i + 1)))) →
      (∀ k, k ∈ K ↔ k ∉ Set.range H) →
      (fun l : Fin p => α l) ∉
        STL.unsafeFactors C d R.c (Matrix.of fun j k => R.G k j) H K hp →
      ∀ t : ℝ, i * Δt ≤ t → t ≤ (i + 1) * Δt →
      ¬ (∀ r, C.mulVec ((LinearSys.canonical A).closedForm (X₀.c + ∑ l : Fin X₀.h, α l • X₀.G l)
        (LinearSys.heldInput Δt
          (fun j => B *ᵥ (U.c + ∑ l : Fin U.h, α (X₀.h + j * U.h + l) • U.G l))) t) r
        ≤ d r) := by -- --- PROOF ---
  -- the claim at the example, with `P = {x ≤ 1/2}`, the factor `1` and the time `1/4`
  intro hall
  have h1 := STL.aux_interval_h
  let H : Fin 1 → Fin (STL.depReach (0 : Mat ℝ 1 1) (1 : Mat ℝ 1 1)
      (⟨0, 0, Fin.elim0⟩ : Zonotope (Vec ℝ 1))
      (⟨1, 0, fun _ => fun _ => 1⟩ : Zonotope (Vec ℝ 1)) 1 1 0).2.h := fun _ => ⟨1, h1⟩
  refine hall 1 1 0 1 ⟨0, 0, Fin.elim0⟩ ⟨1, 0, fun _ => fun _ => 1⟩ 1 one_pos 1 (fun _ => 1)
    (fun _ => by simp) 0 1 1 (fun _ => 1/2) 1 1 le_rfl H
    (Finset.univ.filter fun k => (k : ℕ) ≠ 1) ?_ ?_ ?_ ?_ (1/4) (by norm_num) (by norm_num) ?_
  · intro a b hab
    fin_cases a; fin_cases b; simp at hab
  · -- the range of `H` is the one generator `N₀ = (2)`
    intro k
    simp only [Set.mem_range, H]
    constructor
    · rintro ⟨_, rfl⟩
      right; simp
    · rintro (hk | ⟨hk1, hk2⟩)
      · simp at hk
      · exact ⟨0, Fin.ext (by simp at hk2 ⊢; omega)⟩
  · intro k
    simp [H, Fin.ext_iff]
  · -- `α̃ = 1` is outside `α̃ ≤ 1/2`
    intro hmem
    have := hmem 0
    simp only [Matrix.mul_apply, Matrix.of_apply, Fin.sum_univ_one, Matrix.mulVec,
      dotProduct] at this
    have hG : ∀ x, (STL.depReach (0 : Mat ℝ 1 1) (1 : Mat ℝ 1 1)
        (⟨0, 0, Fin.elim0⟩ : Zonotope (Vec ℝ 1))
        (⟨1, 0, fun _ => fun _ => 1⟩ : Zonotope (Vec ℝ 1)) 1 1 0).2.G x 0
        = if (x : ℕ) = 1 then 1 else 0 := fun x => by
      rw [STL.aux_interval_G x]; split_ifs <;> simp
    have hc := congrFun STL.aux_interval_c 0
    simp only [hG, hc, H] at this
    simp [Finset.sum_filter] at this
    rw [Finset.sum_eq_zero (fun x _ => by
      by_cases hx : (x : ℕ) = 1 <;> simp only [hx, if_true, if_false, abs_zero])] at this
    norm_num at this
  · -- `ξ(1/4) = 1/4 ≤ 1/2`
    intro r
    fin_cases r
    simp [LinearSys.closedForm, LinearSys.heldInput]
    norm_num

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
