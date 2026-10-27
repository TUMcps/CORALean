module

public import CORALean.ContDynamics.LinearSys.Definitions.ClosedForm
public import CORALean.ContDynamics.LinearSys.Definitions.HeldInput
public import CORALean.Specification.STL.Operations.DepReach
public import CORALean.Specification.STL.Theorems.DepBloatingC
public import CORALean.Specification.STL.Theorems.DepReachIntervalSumEval
public import CORALean.Specification.STL.Theorems.ExpIntegralZeroOne
public import CORALean.ContSet.Zonotope.Real.Operations.LinComb
public import CORALean.ContDynamics.LinearSys.Operations.Canonical

@[expose] public section

/-!
# The time interval half of [1, Prop. 1] fails at an interior time

`R(τ_i) = conv(H(t_i), H(t_{i+1})) ⊕ P(t_{i+1}) ⊕ C_i` weights the generators of the input solution
`P_c(t_{i+1})` by their value at the *end* of the step, and `μ = [G_{i2}(·,N_i) 0] α̃` keeps them,
so the state `ξ(t)` of a piecewise constant input, which has only reached `(t - t_i)/Δt` of the
last step's effect, is not in `μ ⊕ E(t)`: the generators of `E(t)` do not absorb the difference.
The statement is [1, Prop. 1] with `N_i` of the generator layout (`2γ_x + 1` generators of the hull,
then `γ_u(i+1)` input generators), in 0-based indices. It fails for `ẋ = u`, `X₀ = {0}`,
`U = [-1,1]`, `Δt = 1`, at `i = 0`, `t = 1/2`, and the factor `α_{u,1} = 1`: `ξ = 1/2` and
`μ ⊕ E = {1}`.

## Inputs
* none

## Hypotheses
* none

## Conclusion
* the time interval half of the dependency claim fails

## References

* [1] [N. Kochdumper and S. Bak. "Fully Automated Verification of Linear Time-Invariant Systems
      against Signal Temporal Logic Specifications via Reachability Analysis". Nonlinear Analysis:
      Hybrid Systems, 2024.](../../../../../references/2024/kochdumper-nahs-stl-lti-verification.md)
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      20-October-2026 (Tobias Ladner)


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real Matrix NormedSpace

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra


-- =======================================  MAIN THEOREM  ======================================= --

theorem STL.depReachInterval_dependency_counterexample : -- --- CONCL ---
    ¬ ∀ (n m : ℕ) (A : Mat ℝ n n) (B : Mat ℝ n m) (X₀ : Zonotope (Vec ℝ n))
      (U : Zonotope (Vec ℝ m)) (Δt : ℝ), 0 < Δt → ∀ (κ : ℕ) (α : ℕ → ℝ), (∀ k, |α k| ≤ 1) →
      ∀ (i : ℕ) (t : ℝ), i * Δt ≤ t → t ≤ (i + 1) * Δt →
      let R := (STL.depReach A B X₀ U Δt κ i).2
      let idx : ℕ → ℕ := fun k => if k < X₀.h then k else k - X₀.h - 1
      let ξ := (LinearSys.canonical A).closedForm (X₀.c + ∑ l : Fin X₀.h, α l • X₀.G l)
        (LinearSys.heldInput Δt
          (fun j => B *ᵥ (U.c + ∑ l : Fin U.h, α (X₀.h + j * U.h + l) • U.G l))) t
      ∃ β : ℕ → ℝ, (∀ k, |β k| ≤ 1) ∧
        ξ = ∑ k : Fin R.h, (if (k : ℕ) < X₀.h ∨
            (2 * X₀.h + 1 ≤ k ∧ (k : ℕ) < 2 * X₀.h + 1 + U.h * (i + 1))
            then α (idx k) else 0) • R.G k
          + (R.c + ∑ k : Fin R.h, (if (k : ℕ) < X₀.h ∨
            (2 * X₀.h + 1 ≤ k ∧ (k : ℕ) < 2 * X₀.h + 1 + U.h * (i + 1))
            then 0 else β k) • R.G k) := by -- --- PROOF ---
  -- the claim at the system, the first step and the middle of it, with the factor `1`
  intro h
  have := h 1 1 0 1 ⟨0, 0, Fin.elim0⟩ ⟨1, 0, fun _ => fun _ => 1⟩ 1 one_pos 1 (fun _ => 1)
    (fun _ => by simp) 0 (1 / 2) (by norm_num) (by norm_num)
  obtain ⟨β, hβ, heq⟩ := this
  -- the sums over the generators of `R(τ₀)` are `depReachInterval_sum_eval`'s
  have hA := STL.depReachInterval_sum_eval (fun k =>
    if k < 0 ∨ (2 * 0 + 1 ≤ k ∧ k < 2 * 0 + 1 + 1 * (0 + 1)) then (1 : ℝ) else 0)
  have hB := STL.depReachInterval_sum_eval (fun k =>
    if k < 0 ∨ (2 * 0 + 1 ≤ k ∧ k < 2 * 0 + 1 + 1 * (0 + 1)) then (0 : ℝ) else β k)
  -- the center of `R(τ₀)` is `0`
  dsimp only at hA hB heq
  rw [hA, hB] at heq
  have hRc : (STL.depReach (0 : Mat ℝ 1 1) (1 : Mat ℝ 1 1) (⟨0, 0, Fin.elim0⟩ : Zonotope (Vec ℝ 1))
      (⟨1, 0, fun _ => fun _ => 1⟩ : Zonotope (Vec ℝ 1)) 1 1 0).2.c = 0 := by
    simp [STL.depReach, STL.depReachInterval, STL.depReachAt, STL.depReachStep, STL.depReachInit,
      STL.depReachConsts, STL.depBox, Zonotope.plus, Zonotope.mtimes, Zonotope.ofPoint,
      Zonotope.linComb, Zonotope.mtimesIntervalMat, STL.expIntegral_zero_one]
    exact STL.depBloating_c _ _ _ _ rfl
  rw [hRc] at heq
  -- the solution at `t = 1/2` of `ẋ = u` held at `1` is `1/2`, and the claim says `1`
  have hcf : (LinearSys.canonical (0 : Mat ℝ 1 1)).closedForm
      (0 + ∑ l : Fin 0, (1:ℝ) • (l.elim0 : Vec ℝ 1))
      (LinearSys.heldInput 1 fun j : ℕ =>
        (1 : Mat ℝ 1 1) *ᵥ (0 + ∑ l : Fin 1, (1:ℝ) • (fun _ => 1 : Vec ℝ 1)))
      (1 / 2) = (1/2 : ℝ) • (fun _ => (1 : ℝ) : Vec ℝ 1) := by
    simp [LinearSys.closedForm, LinearSys.heldInput]
  rw [hcf] at heq
  have h0 := congrFun heq 0
  norm_num at h0

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
