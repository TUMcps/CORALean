module

public import CORALean.ContDynamics.LinearSys.MatExp.Definitions.HomogeneousRemainderError
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.AbsEntryLeOfMemInputCorrectionSet
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.AbsEntryLeOfMemStateCorrectionSet
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.TendstoExpRemainderMatZero
public import CORALean.Global.IsErrorConvergingToZero

@[expose] public section

/-!
# `Prop. 3`: `ε_H` of eq. (21) converges to `0` with the step

[1, Prop. 3]: the error `ε_H([t_i,t_{i+1}]) = err(e^{At_i} F_x(Δt_i,η_i) X_0 ⊕ e^{At_i}
F_u(Δt_i,η_i) c_u)` of eq. (21) converges to `0` for `Δt_i → 0`, and so satisfies `Assumption 1`.
[1]'s proof: it suffices that `F_x` and `F_u` converge to `[0_n, 0_n]`, since each Taylor
interval `[c_k Δt^k, 0]` has `k ≥ 2` and `E(Δt,η) → 0`. Here that is quantitative: every entry of
a member of `F_x(Δt,η)`, likewise of `F_u(Δt,η)`, is within
`Σₖ |c_k Δt^k| |(A^k/k!)_{ij}| + ‖E(Δt,η)‖` of `0` (`abs_entry_le_of_mem_stateCorrectionSet`), so
every point of the set is within `C·(b_x(Δt)·err(X_0) + b_u(Δt)·‖c_u‖₂)` of the origin, `C` the
row norms of `e^{At_i}`. `X_0` bounded makes `err(X_0)` the enclosing radius.

## Inputs
* `A` – system matrix
* `ti` – step start time
* `X₀` – initial set
* `cu` – input center
* `η` – Taylor order

## Hypotheses
* `hX₀` – initial set bounded

## Conclusion
* the homogeneous remainder error converges to zero with the step

## References

* [1] M. Wetzlinger, N. Kochdumper and M. Althoff. "Adaptive parameter tuning for reachability
      analysis of linear systems". 2020 59th IEEE Conference on Decision and Control (CDC), 2020.
-/

-- Authors:       Claude Opus 5.5
-- Written:       23-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix NormedSpace Filter Topology

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- A matrix entrywise within `b` of `0` scales the Euclidean norm by at most `Σᵢ Σⱼ b_{ij}`. -/
private theorem aux_norm₂_mulVec_le_of_abs_entry_le (M b : Mat ℝ n n) (hM : ∀ i j, |M i j| ≤ b i j)
    (x : Vec ℝ n) : ‖M.mulVec x‖₂ ≤ (∑ i, ∑ j, b i j) * ‖x‖₂ := by
  refine (norm₂_mulVec_le M x).trans (mul_le_mul_of_nonneg_right ?_ (norm₂_nonneg x))
  exact Finset.sum_le_sum fun i _ =>
    (norm₂_le_sum_abs _).trans (Finset.sum_le_sum fun j _ => hM i j)

/-- A Taylor interval `[c_k Δt^k, 0]` with `k ≥ 2`, scaling a fixed entry, vanishes with `Δt`. -/
private theorem aux_tendsto_taylor_term {k : ℕ} (hk : k ≠ 0) (b : ℝ) : -- --- CONCL ---
    Tendsto (fun Δt : ℝ => |MatExp.corrCoeff k * Δt ^ k| * b) (𝓝[>] (0 : ℝ))
      (𝓝 0) := by -- --- PROOF ---
  have hc : Continuous fun Δt : ℝ => |MatExp.corrCoeff k * Δt ^ k| * b :=
    (continuous_const.mul (continuous_pow k)).abs.mul continuous_const
  have h := (hc.tendsto (0 : ℝ)).mono_left (nhdsWithin_le_nhds (s := Set.Ioi (0 : ℝ)))
  simp only [zero_pow hk, mul_zero, abs_zero, zero_mul] at h
  exact h


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Prop. 3]: `ε_H([t_i,t_i+Δt]) = err(e^{At_i} F_x(Δt,η) X_0 ⊕ e^{At_i} F_u(Δt,η) c_u)`
converges to `0` as `Δt → 0⁺`, at every step start `t_i`, order `η` and input center `c_u` —
`Assumption 1` for `ε_H`. -/
theorem MatExp.errorConvergesToZero_homogeneousRemainderError (A : Mat ℝ n n) (ti : ℝ)
    {X₀ : Set (Vec ℝ n)} (hX₀ : Bornology.IsBounded X₀) (cu : Vec ℝ n) (η : ℕ) : -- --- CONCL ---
    IsErrorConvergingToZero
      (fun Δt => MatExp.homogeneousRemainderError A ti X₀ cu Δt η) := by -- --- PROOF ---
  set C := ∑ i, ‖(fun j => (exp (ti • A)) i j)‖₂ with hC
  have hC0 : 0 ≤ C := Finset.sum_nonneg fun i _ => norm₂_nonneg _
  -- the entry bounds of `F_x` and `F_u`, summed over all entries
  set bx : ℝ → ℝ := fun Δt => ∑ i, ∑ j, ((∑ k ∈ Finset.Icc 2 η, |MatExp.corrCoeff k * Δt ^ k|
      * |((((Nat.factorial k : ℝ))⁻¹ • A ^ k) : Mat ℝ n n) i j|)
      + ‖MatExp.expRemainderMat A Δt η‖) with hbx
  set bu : ℝ → ℝ := fun Δt => ∑ i, ∑ j, ((∑ k ∈ Finset.Icc 2 (η + 1), |MatExp.corrCoeff k * Δt ^ k|
      * |((((Nat.factorial k : ℝ))⁻¹ • A ^ (k - 1)) : Mat ℝ n n) i j|)
      + |Δt| * ‖MatExp.expRemainderMat A Δt η‖) with hbu
  have hbx0 : ∀ Δt, 0 ≤ bx Δt := fun Δt => Finset.sum_nonneg fun i _ => Finset.sum_nonneg
    fun j _ => add_nonneg (Finset.sum_nonneg fun k _ => by positivity) (norm_nonneg _)
  have hbu0 : ∀ Δt, 0 ≤ bu Δt := fun Δt => Finset.sum_nonneg fun i _ => Finset.sum_nonneg
    fun j _ => add_nonneg (Finset.sum_nonneg fun k _ => by positivity) (by positivity)
  -- every point of the set is within `C·(b_x·err(X_0) + b_u·‖c_u‖₂)` of the origin
  have hbound : ∀ Δt : ℝ, MatExp.homogeneousRemainderError A ti X₀ cu Δt η
      ≤ Real.sqrt n * (C * (bx Δt * err X₀ + bu Δt * ‖cu‖₂)) := by
    intro Δt
    have hr : 0 ≤ C * (bx Δt * err X₀ + bu Δt * ‖cu‖₂) := mul_nonneg hC0 (add_nonneg
      (mul_nonneg (hbx0 Δt) (err_nonneg X₀)) (mul_nonneg (hbu0 Δt) (norm₂_nonneg cu)))
    refine err_le_of_forall_norm₂_le hr ?_
    rintro _ ⟨_, ⟨_, ⟨M, hM, x, hx, rfl⟩, rfl⟩, _, ⟨_, ⟨N, hN, rfl⟩, rfl⟩, rfl⟩
    have hMx : ‖M.mulVec x‖₂ ≤ bx Δt * err X₀ :=
      (aux_norm₂_mulVec_le_of_abs_entry_le M _
        (MatExp.abs_entry_le_of_mem_stateCorrectionSet hM) x).trans
        (mul_le_mul_of_nonneg_left (norm₂_le_err_of_mem hX₀ hx) (hbx0 Δt))
    have hNc : ‖N.mulVec cu‖₂ ≤ bu Δt * ‖cu‖₂ :=
      aux_norm₂_mulVec_le_of_abs_entry_le N _ (MatExp.abs_entry_le_of_mem_inputCorrectionSet hN) cu
    calc ‖(exp (ti • A)).mulVec (M.mulVec x) + (exp (ti • A)).mulVec (N.mulVec cu)‖₂
        ≤ C * ‖M.mulVec x‖₂ + C * ‖N.mulVec cu‖₂ :=
          (norm₂_add_le _ _).trans (add_le_add (norm₂_mulVec_le _ _) (norm₂_mulVec_le _ _))
      _ ≤ C * (bx Δt * err X₀ + bu Δt * ‖cu‖₂) := by
          rw [mul_add]
          exact add_le_add (mul_le_mul_of_nonneg_left hMx hC0)
            (mul_le_mul_of_nonneg_left hNc hC0)
  -- both entry bounds vanish with the step: each Taylor term does, and so does `‖E(Δt,η)‖`
  have hE : Tendsto (fun Δt : ℝ => ‖MatExp.expRemainderMat A Δt η‖) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    simpa only [norm_zero] using (MatExp.tendsto_expRemainderMat_zero A η).norm
  have habs : Tendsto (fun Δt : ℝ => |Δt|) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    simpa only [abs_zero] using (continuous_abs.tendsto (0 : ℝ)).mono_left nhdsWithin_le_nhds
  -- summed over every entry and every order, still `0` in the limit
  have hbxlim : Tendsto bx (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have h := tendsto_finsetSum (Finset.univ : Finset (Fin n)) fun i _ =>
      tendsto_finsetSum (Finset.univ : Finset (Fin n)) fun j _ =>
        (tendsto_finsetSum (Finset.Icc 2 η) fun k hk =>
          aux_tendsto_taylor_term (k := k) (by have := (Finset.mem_Icc.mp hk).1; omega)
            |((((Nat.factorial k : ℝ))⁻¹ • A ^ k) : Mat ℝ n n) i j|).add hE
    simp only [Finset.sum_const_zero, add_zero] at h
    exact h
  have hbulim : Tendsto bu (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have h := tendsto_finsetSum (Finset.univ : Finset (Fin n)) fun i _ =>
      tendsto_finsetSum (Finset.univ : Finset (Fin n)) fun j _ =>
        (tendsto_finsetSum (Finset.Icc 2 (η + 1)) fun k hk =>
          aux_tendsto_taylor_term (k := k) (by have := (Finset.mem_Icc.mp hk).1; omega)
            |((((Nat.factorial k : ℝ))⁻¹ • A ^ (k - 1)) : Mat ℝ n n) i j|).add (habs.mul hE)
    simp only [Finset.sum_const_zero, mul_zero, add_zero] at h
    exact h
  -- so the whole radius vanishes, and `ε_H` is squeezed between it and `0`
  have hlim := (((hbxlim.mul_const (err X₀)).add (hbulim.mul_const ‖cu‖₂)).const_mul C).const_mul
    (Real.sqrt n)
  simp only [zero_mul, add_zero, mul_zero] at hlim
  exact squeeze_zero (fun Δt => err_nonneg _) hbound hlim

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
