module

public import CORALean.ContSet.Zonotope.Real.Theorems.CenterMemConstruct
public import Mathlib.Analysis.Convex.Combination
public import Mathlib.Algebra.Order.Chebyshev
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.FieldSimp

@[expose] public section

/-!
# Zonotope in a convex hull of zonotopes, sufficiently

`[1, Cor. 4]`: `⟨x̄, X⟩ ⊆ conv(⋃ᵢ ⟨ȳᵢ, Yᵢ⟩)` if `‖(Γᵢ | βᵢ)‖∞ ≤ λᵢ`, `λ ≥ 0`, `∑ λᵢ = 1`,
`∑ᵢ (Yᵢ βᵢ + λᵢ ȳᵢ) = x̄` and `∑ᵢ Yᵢ Γᵢ = X` (`[1, Cor. 4, Eq. 33]`). A point `x̄ + X a` is
`∑ᵢ (λᵢ ȳᵢ + Yᵢ bᵢ)` with `bᵢ = Γᵢ a + βᵢ` and `|bᵢ| ≤ λᵢ` row by row, so each summand is
`λᵢ` times a point of `⟨ȳᵢ, Yᵢ⟩` — its center when `λᵢ = 0`, where `bᵢ` vanishes.
Zonotopes are nonempty and bounded, so `[1, Cor. 3]`'s gap does not arise. In generators,
over any real module.

## References

* [1] S. Sadraddini and R. Tedrake. "Linear Encodings for Polytope Containment Problems". In
      Proc. of the 58th IEEE Conference on Decision and Control (CDC), pp. 4367-4372, 2019.
      arXiv:1903.05214.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α] {N : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zonotope.construct_subset_convexHull_of_cert (Zx : Zonotope α) (Zy : Fin N → Zonotope α)
    (Γ : (i : Fin N) → Mat ℝ (Zy i).h Zx.h) (β : (i : Fin N) → Vec ℝ (Zy i).h)
    (lam : Fin N → ℝ) (hn : ∀ i k, ∑ j, |Γ i k j| + |β i k| ≤ lam i) (hlam : ∀ i, 0 ≤ lam i)
    (hsum : ∑ i, lam i = 1)
    (hc : ∑ i, ((∑ k, β i k • (Zy i).G k) + lam i • (Zy i).c) = Zx.c)
    (hX : ∀ j, ∑ i, ∑ k, Γ i k j • (Zy i).G k = Zx.G j) :
    Zx.construct ⊆ convexHull ℝ (⋃ i, (Zy i).construct) := by -- --- PROOF ---
  rintro _ ⟨a, ha, rfl⟩
  -- the coefficients `bᵢ = Γᵢ a + βᵢ`, bounded by `λᵢ`
  let b : (i : Fin N) → Vec ℝ (Zy i).h := fun i k => ∑ j, Γ i k j * a j + β i k
  have hb : ∀ i k, |b i k| ≤ lam i := by
    intro i k
    have h1 : |∑ j, Γ i k j * a j| ≤ ∑ j, |Γ i k j| := by
      refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
      rw [abs_mul]
      exact mul_le_of_le_one_right (abs_nonneg _) (ha j)
    exact (abs_add_le _ _).trans (by linarith [hn i k])
  -- each summand is `λᵢ zᵢ` for a point `zᵢ` of `Zy i`
  have hz : ∀ i, ∃ z ∈ (Zy i).construct,
      lam i • (Zy i).c + ∑ k, b i k • (Zy i).G k = lam i • z := by
    intro i
    rcases (hlam i).lt_or_eq with hpos | hzero
    · refine ⟨(Zy i).c + ∑ k, ((lam i)⁻¹ * b i k) • (Zy i).G k,
        ⟨fun k => (lam i)⁻¹ * b i k, fun k => ?_, rfl⟩, ?_⟩
      · rw [abs_mul, abs_inv, abs_of_pos hpos, inv_mul_le_iff₀ hpos, mul_one]
        exact hb i k
      · rw [smul_add, Finset.smul_sum]
        simp only [smul_smul, ← mul_assoc, mul_inv_cancel₀ hpos.ne', one_mul]
    · refine ⟨(Zy i).c, Zonotope.center_mem_construct _, ?_⟩
      have hb0 : ∀ k, b i k = 0 := fun k => abs_nonpos_iff.mp (hzero ▸ hb i k)
      simp [hb0, ← hzero]
  choose z hzmem hzeq using hz
  -- regroup `x̄ + X a` summand by summand
  have e1 : ∑ j, a j • Zx.G j = ∑ i, ∑ k, (∑ j, Γ i k j * a j) • (Zy i).G k := by
    simp only [← hX, Finset.smul_sum, smul_smul, Finset.sum_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => by rw [mul_comm]
  have hx' : Zx.c + ∑ j, a j • Zx.G j = ∑ i, lam i • z i := by
    rw [← hc, e1, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← hzeq i]
    simp only [b, add_smul, Finset.sum_add_distrib]
    abel
  rw [hx']
  exact (convex_convexHull ℝ _).sum_mem (fun i _ => hlam i) hsum
    fun i _ => subset_convexHull ℝ _ (Set.mem_iUnion.mpr ⟨i, hzmem i⟩)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
