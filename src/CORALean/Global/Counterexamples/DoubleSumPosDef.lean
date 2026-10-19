module

public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Tactic.FinCases
public import Mathlib.Algebra.Order.Star.Real

@[expose] public section

/-!
# The double-sum relaxation as printed

[1, Lemma 2] concludes `Σᵢ Σⱼ μᵢ μⱼ Γᵢⱼ ≻ 0` from `Γᵢᵢ ≻ 0` (its Eq. 28a) and
`2/(r-1) Γᵢᵢ + Γᵢⱼ + Γⱼᵢ ≽ 0` for `1 ≤ i < j ≤ r` (its Eq. 28b). With `r = 2`, `Γ₁₁ = Γ₂₂ = 1`,
`Γ₁₂ = Γ₂₁ = -1` (scalars) both hold, Eq. 28b with equality, and at `μ = (1/2, 1/2)` the sum is
`1/4 + 1/4 - 1/2 = 0`. With Eq. 28b strict and for every ordered pair `i ≠ j` the lemma holds
(`doubleSum_posDef`).

## References

* [1] Y. Wang, Z. Wang, V. Puig and G. Cembrano. "Zonotopic set-membership state estimation for
      discrete-time descriptor LPV systems". IEEE Transactions on Automatic Control,
      64(5):2092-2099, 2019.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix


-- =======================================  MAIN THEOREM  ======================================= --

theorem doubleSum_posDef_counterexample : -- --- CONCL ---
    let Γ : Fin 2 → Fin 2 → Matrix (Fin 1) (Fin 1) ℝ := fun i j => if i = j then 1 else -1
    let μ : Fin 2 → ℝ := fun _ => 1 / 2
    (∀ i, 0 ≤ μ i) ∧ ∑ i, μ i = 1 ∧ (∀ i j, (Γ i j)ᵀ = Γ i j) ∧ (∀ i, (Γ i i).PosDef) ∧
      (∀ i j, i < j → ((2 / ((2 : ℝ) - 1)) • Γ i i + Γ i j + Γ j i).PosSemidef) ∧
      ¬ (∑ i, ∑ j, (μ i * μ j) • Γ i j).PosDef := by -- --- PROOF ---
  intro Γ μ
  refine ⟨fun _ => by norm_num [μ], by simp [μ], fun i j => ?_,
    fun i => by simpa [Γ] using PosDef.one, fun i j hij => ?_, fun h => ?_⟩
  · -- every `Γᵢⱼ` is a multiple of the identity
    by_cases hij : i = j <;> simp [Γ, hij]
  · -- `2 - 1 - 1 = 0`
    fin_cases i <;> fin_cases j <;> simp at hij
    have : (2 / ((2 : ℝ) - 1)) • Γ 0 0 + Γ 0 1 + Γ 1 0 = 0 := by
      ext a b; fin_cases a; fin_cases b; simp [Γ]; norm_num
    simpa [this] using PosSemidef.zero
  · -- the sum vanishes at `μ = (1/2, 1/2)`
    have h0 : ∑ i, ∑ j, (μ i * μ j) • Γ i j = 0 := by
      ext a b; fin_cases a; fin_cases b
      simp [Γ, μ, Fin.sum_univ_two]
    rw [h0] at h
    have := (posDef_iff_dotProduct_mulVec.mp h).2 (x := fun _ => 1) (by
      intro hx; have := congrFun hx 0; simp at this)
    simp at this

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
