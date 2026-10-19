module

public import CORALean.ContDynamics.LinearSysDT.LinearSysDT
public import CORALean.ContSet.Zonotope.Real.Theorems.MtimesExact
public import CORALean.ContSet.Zonotope.Real.Theorems.UnderSSubset
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

@[expose] public section

/-!
# Control synthesis from the under-approximation

[1, Sec. 5.2]: let `y = u + Σⱼ αⱼgⱼ`, `Σⱼ |αⱼ| ≤ 1`, be a point of `Ω̲_N`, which by
[1, Lemma 1] is `Φ^NΩ₀ ⊞ Φ^{N-1}U ⊞ … ⊞ U`: `u = u^N + u^{N-1} + … + u⁰` and
`gⱼ = g^N_j + … + g⁰_j`, `(u^N, [g^N]_S)` the under-approximation of `Φ^NΩ₀` and `(uⁱ, [gⁱ]_S)`
that of `ΦⁱU`. If `Φ` is invertible, `x₀ = Φ^{-N}(u^N + Σⱼ αⱼg^N_j)` and
`vᵢ = Φ^{i+1-N}(u^{N-1-i} + Σⱼ αⱼg^{N-1-i}_j)` give `x₀ ∈ Ω₀`, `vᵢ ∈ U`, and the run
`x_{i+1} = Φxᵢ + vᵢ` ends at `x_N = y`. Each point `Φ^{-k}(uᵏ + Σⱼ αⱼgᵏ_j)` is in the set
because the under-approximation lies in `ΦᵏU` (`Zonotope.underS_subset`), the image of `U`;
and the run sums the `N + 1` points back into `y`, the same `α` throughout.

## References

* [1] A. Girard, C. Le Guernic and O. Maler. "Efficient Computation of Reachable Sets of
      Linear Time-Invariant Systems with Inputs". In Hybrid Systems: Computation and
      Control (HSCC), LNCS 3927, Springer, 2006, pp. 257-271.
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --
namespace CORALean

open CORALean.Real
open Matrix

variable {n ℓ : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Sec. 5.2]: from `y ∈ Ω̲_N`, the printed `x₀ ∈ Ω₀` and `vᵢ ∈ U` steer the run to `y`. -/
theorem LinearSysDT.control_of_mem_underS (sys : LinearSysDT ℝ n) (hΦ : IsUnit sys.A.det)
    (Ω₀ U : Zonotope (Vec ℝ n)) (s : Fin ℓ → Vec ℝ n) (N : ℕ) (α : Fin ℓ → ℝ)
    (hα : ∑ j, |α j| ≤ 1) (y : Vec ℝ n)
    (hy : y = (Ω₀.mtimes (sys.A ^ N)).c + ∑ k ∈ Finset.range N, (U.mtimes (sys.A ^ k)).c
      + ∑ j, α j • ((Ω₀.mtimes (sys.A ^ N)).extremalGen (s j)
        + ∑ k ∈ Finset.range N, (U.mtimes (sys.A ^ k)).extremalGen (s j))) : -- --- CONCL ---
    let w := fun Z : Zonotope (Vec ℝ n) => Z.c + ∑ j, α j • Z.extremalGen (s j)
    let x₀ := sys.A⁻¹ ^ N *ᵥ w (Ω₀.mtimes (sys.A ^ N))
    let v := fun i => sys.A⁻¹ ^ (N - 1 - i) *ᵥ w (U.mtimes (sys.A ^ (N - 1 - i)))
    x₀ ∈ Ω₀.construct ∧ (∀ i < N, v i ∈ U.construct) ∧
      ∀ x : ℕ → Vec ℝ n, x 0 = x₀ → (∀ i < N, x (i + 1) = sys.A *ᵥ x i + v i) →
        x N = y := by -- --- PROOF ---
  intro w x₀ v
  -- `Φ^{-k}` undoes `Φᵏ` on either side
  have hl : ∀ k, sys.A⁻¹ ^ k * sys.A ^ k = 1 := fun k => by
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ, pow_succ', mul_assoc, ← mul_assoc sys.A⁻¹, nonsing_inv_mul _ hΦ, one_mul, ih]
  have hr : ∀ k, sys.A ^ k * sys.A⁻¹ ^ k = 1 := fun k => by
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ, pow_succ', mul_assoc, ← mul_assoc sys.A, mul_nonsing_inv _ hΦ, one_mul, ih]
  -- `Φ^{-k}` of the point of `(ΦᵏZ)̲` with coefficients `α` lies in `Z`
  have hin : ∀ (Z : Zonotope (Vec ℝ n)) (k : ℕ),
      sys.A⁻¹ ^ k *ᵥ w (Z.mtimes (sys.A ^ k)) ∈ Z.construct := fun Z k => by
      have h := (Z.mtimes (sys.A ^ k)).underS_subset s ⟨α, hα, rfl⟩
      rw [← Zonotope.mtimes_exact] at h
      obtain ⟨z, hz, hzw⟩ := h
      simp only at hzw
      show sys.A⁻¹ ^ k *ᵥ ((Z.mtimes (sys.A ^ k)).c
        + ∑ j, α j • (Z.mtimes (sys.A ^ k)).extremalGen (s j)) ∈ _
      rw [← hzw, mulVec_mulVec, hl, one_mulVec]
      exact hz
  refine ⟨hin Ω₀ N, fun i _ => hin U (N - 1 - i), fun x hx0 hstep => ?_⟩
  -- the run in closed form: `x_k = Φᵏx₀ + Σ_{i<k} Φ^{k-1-i}vᵢ`
  have hrun : ∀ k ≤ N,
      x k = sys.A ^ k *ᵥ x₀ + ∑ i ∈ Finset.range k, sys.A ^ (k - 1 - i) *ᵥ v i := by
    intro k hk
    induction k with
    | zero => simp [hx0]
    | succ k ih =>
      rw [hstep k (by omega), ih (by omega), mulVec_add, mulVec_mulVec, ← pow_succ', mulVec_sum,
        Finset.sum_range_succ, Nat.add_sub_cancel, Nat.sub_self, pow_zero, one_mulVec, add_assoc]
      congr 2
      refine Finset.sum_congr rfl fun i hi => ?_
      rw [Finset.mem_range] at hi
      rw [mulVec_mulVec, ← pow_succ']
      congr 2
      omega
  -- each term is a point of an under-approximation, reflected back into `u` and the `gⱼ`
  rw [hrun N le_rfl]
  have hx : sys.A ^ N *ᵥ x₀ = w (Ω₀.mtimes (sys.A ^ N)) := by
    simp only [x₀, mulVec_mulVec, hr, one_mulVec]
  have hv : ∀ i, sys.A ^ (N - 1 - i) *ᵥ v i = w (U.mtimes (sys.A ^ (N - 1 - i))) := fun i => by
    simp only [v, mulVec_mulVec, hr, one_mulVec]
  rw [hx, Finset.sum_congr rfl fun i _ => hv i,
    Finset.sum_range_reflect (fun k => w (U.mtimes (sys.A ^ k))) N, hy]
  simp only [w, Finset.sum_add_distrib, smul_add, Finset.smul_sum,
    Finset.sum_comm (s := Finset.range N)]
  abel

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
