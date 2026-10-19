module

public import CORALean.ContSet.Zonotope.Real.Operations.AveragingWeights
public import CORALean.ContSet.Zonotope.Real.Operations.AndAveraging
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith

@[expose] public section

/-!
# The averaging weights minimize the Frobenius norm

[1, Prop. 1]: among the weights of sum one, `wʲ = 1 / (αⱼ Σᵣ 1 / αᵣ)` with `αⱼ = tr(Ḡʲ Ḡʲᵀ)`
Eq. 19 of [1, Prop. 1] minimizes `‖Ǵ‖²_F = Σᵣ (wʳ)² αᵣ` Eq. 20 of [1, Prop. 1]. The paper finds
the extremum by a Lagrange multiplier and a bordered Hessian; here the objective at any weights
`v` of sum one is the objective at `w` plus `Σⱼ αⱼ (vⱼ - wⱼ)²`, which is the same minimum
without a second-order test. The traces must be positive: a zero generator matrix has no weight.

## References

* [1] A. Alanwar, J. J. Rath, H. Said, K. H. Johansson and M. Althoff. "Distributed Set-Based
      Observers Using Diffusion Strategies". Journal of the Franklin Institute,
      360(10):6976-6993, 2023. arXiv:2003.10347.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       09-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n N : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- Eq. 20: at weights of sum one the squared Frobenius norm of `Ǵ` is `Σⱼ αⱼ (vʲ)²`. -/
theorem Zonotope.aux_frobSq_andAveraging (Z : Fin N → Zonotope (Vec ℝ n)) (v : Fin N → ℝ)
    (hv : ∑ j, v j = 1) :
    ∑ i, ∑ k, ((Zonotope.andAveraging Z v).G k i) ^ 2 =
      ∑ j, (∑ i, ∑ l, (Z j).G l i ^ 2) * v j ^ 2 := by -- --- PROOF ---
  let e : Fin (∑ j, (Z j).h) ≃ (Σ j, Fin (Z j).h) := (finSigmaFinEquiv (n := fun j => (Z j).h)).symm
  -- each term, with the sigma-type index read off `e`
  have hterm : ∀ i, ∑ k : Fin (∑ j, (Z j).h), ((Zonotope.andAveraging Z v).G k i) ^ 2 =
      ∑ j, ∑ l, (v j * (Z j).G l i) ^ 2 := by
    intro i
    change ∑ k : Fin (∑ j, (Z j).h), (((∑ j, v j)⁻¹ * v (e k).1) • (Z (e k).1).G (e k).2) i ^ 2 = _
    rw [hv, Equiv.sum_comp e (fun p => (((1 : ℝ)⁻¹ * v p.1) • (Z p.1).G p.2) i ^ 2),
      Fintype.sum_sigma]
    simp
  refine (Finset.sum_congr rfl fun i _ => hterm i).trans ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [mul_pow, ← Finset.mul_sum]
  ring


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zonotope.averagingWeights_optimal [NeZero N] (Z : Fin N → Zonotope (Vec ℝ n))
    (hα : ∀ j, 0 < ∑ i, ∑ k, (Z j).G k i ^ 2) : -- --- CONCL ---
    ∑ j, Zonotope.averagingWeights Z j = 1 ∧
      ∀ v : Fin N → ℝ, ∑ j, v j = 1 →
        ∑ i, ∑ k, ((Zonotope.andAveraging Z (Zonotope.averagingWeights Z)).G k i) ^ 2 ≤
          ∑ i, ∑ k, ((Zonotope.andAveraging Z v).G k i) ^ 2 := by -- --- PROOF ---
  -- the algebra over any positive traces `α`, with `S = Σᵣ 1 / αᵣ` and `wⱼ = 1 / (αⱼ S)`
  have alg : ∀ α : Fin N → ℝ, (∀ j, 0 < α j) →
      ∑ j, (α j * ∑ r, (α r)⁻¹)⁻¹ = 1 ∧ ∀ v : Fin N → ℝ, ∑ j, v j = 1 →
        ∑ j, α j * ((α j * ∑ r, (α r)⁻¹)⁻¹) ^ 2 ≤ ∑ j, α j * v j ^ 2 := by
    intro α hpos
    have hSpos : 0 < ∑ r, (α r)⁻¹ :=
      Finset.sum_pos (fun r _ => inv_pos.mpr (hpos r)) Finset.univ_nonempty
    set S : ℝ := ∑ r, (α r)⁻¹ with hS
    -- `αⱼ wⱼ = 1 / S`
    have hαw : ∀ j, α j * (α j * S)⁻¹ = S⁻¹ := fun j => by
      have := (hpos j).ne'
      field_simp
    have hsum : ∑ j, (α j * S)⁻¹ = 1 := by
      have : ∀ j, (α j * S)⁻¹ = (α j)⁻¹ * S⁻¹ := fun j => mul_inv _ _
      simp only [this, ← Finset.sum_mul]
      rw [← hS]
      exact mul_inv_cancel₀ hSpos.ne'
    refine ⟨hsum, fun v hv => ?_⟩
    -- the objective at `v` is the objective at `w` plus `Σⱼ αⱼ (vⱼ - wⱼ)²`
    have hsq : ∑ j, α j * (v j - (α j * S)⁻¹) ^ 2 =
        ∑ j, α j * v j ^ 2 - 2 * S⁻¹ + ∑ j, α j * ((α j * S)⁻¹) ^ 2 := by
      -- termwise, using `αⱼ wⱼ = 1 / S`
      have hterm : ∀ j, α j * (v j - (α j * S)⁻¹) ^ 2 =
          α j * v j ^ 2 - 2 * (v j * S⁻¹) + α j * ((α j * S)⁻¹) ^ 2 := fun j => by
        have := hαw j
        calc α j * (v j - (α j * S)⁻¹) ^ 2
            = α j * v j ^ 2 - 2 * v j * (α j * (α j * S)⁻¹) + α j * ((α j * S)⁻¹) ^ 2 := by ring
          _ = _ := by rw [this]; ring
      -- sum the terms; `Σⱼ vⱼ = 1`
      simp only [hterm, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.sum_mul, hv,
        ← Finset.mul_sum]
      ring
    -- the optimum has objective `1 / S`
    have hww : ∑ j, α j * ((α j * S)⁻¹) ^ 2 = S⁻¹ := by
      have hterm : ∀ j, α j * ((α j * S)⁻¹) ^ 2 = (α j * S)⁻¹ * S⁻¹ := fun j => by
        have := hαw j
        calc α j * ((α j * S)⁻¹) ^ 2 = (α j * (α j * S)⁻¹) * (α j * S)⁻¹ := by ring
          _ = _ := by rw [this]; ring
      simp only [hterm, ← Finset.sum_mul, hsum, one_mul]
    have hnn : 0 ≤ ∑ j, α j * (v j - (α j * S)⁻¹) ^ 2 :=
      Finset.sum_nonneg fun j _ => mul_nonneg (hpos j).le (sq_nonneg _)
    linarith
  obtain ⟨hsum, hopt⟩ := alg _ hα
  have hsum' : ∑ j, Zonotope.averagingWeights Z j = 1 := hsum
  refine ⟨hsum', fun v hv => ?_⟩
  rw [Zonotope.aux_frobSq_andAveraging Z _ hsum', Zonotope.aux_frobSq_andAveraging Z _ hv]
  exact hopt v hv

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
