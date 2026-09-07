import CORALean.ContSet.ContSet.ContSet
import CORALean.ContSet.Zonotope.Real.Operations.MinkDiffAligned

/-!
# `Zonotope.minkDiffAligned` is an inner approximation of the Minkowski difference

Every membership splits `x = (c₁-c₂) + ∑ βᵢ(G₁ᵢ-G₂ᵢ)` and `y = c₂ + ∑ γᵢG₂ᵢ`,
and `hG` rewrites `G₂ᵢ` as `μᵢ G₁ᵢ`, collecting `x + y` into `c₁ + ∑ δᵢ G₁ᵢ`
with `δᵢ = βᵢ(1-μᵢ) + γᵢμᵢ`. Both bounds on `μ` are what keep `|δᵢ| ≤ 1`: one
on each summand of the triangle inequality.

`Fin.castOrderIso hh` reindexes the subtrahend's sum onto the minuend's own
generator count — `hh` says the counts agree, so the reindexing is a bijection,
not merely a function.
-/

-- Authors:       Tobias Ladner
-- Written:       07-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zonotope.minkDiffAligned_inner (Z₁ Z₂ : Zonotope α) (hh : Z₁.h = Z₂.h)
    (μ : Fin Z₁.h → ℝ) (hμ0 : ∀ i, 0 ≤ μ i) (hμ1 : ∀ i, μ i ≤ 1)
    (hG : ∀ i, Z₂.G (Fin.cast hh i) = μ i • Z₁.G i) :
    (Z₁.minkDiffAligned Z₂ hh).construct
      ⊆ minkowskiDiff Z₁.construct Z₂.construct := by -- --- PROOF ---
  intro x hx y hy
  dsimp only [Zonotope.minkDiffAligned] at hx
  obtain ⟨β, hβ, rfl⟩ := hx
  obtain ⟨γ, hγ, rfl⟩ := hy
  -- δᵢ = βᵢ(1-μᵢ) + γᵢμᵢ: the bound first, the equation second
  refine ⟨fun i => β i * (1 - μ i) + γ (Fin.cast hh i) * μ i, fun i => ?_, ?_⟩
  · have h3 := hμ0 i
    have h4 := hμ1 i
    calc |β i * (1 - μ i) + γ (Fin.cast hh i) * μ i|
        ≤ |β i * (1 - μ i)| + |γ (Fin.cast hh i) * μ i| := abs_add_le _ _
      _ = |β i| * (1 - μ i) + |γ (Fin.cast hh i)| * μ i := by
          rw [abs_mul, abs_mul, abs_of_nonneg (by linarith : (0:ℝ) ≤ 1 - μ i),
            abs_of_nonneg h3]
      _ ≤ 1 * (1 - μ i) + 1 * μ i := by gcongr <;> [exact hβ i; exact hγ _]
      _ = 1 := by ring
  · -- reindex the subtrahend's sum onto Z₁'s own generator count first
    have hsum : ∑ k : Fin Z₂.h, γ k • Z₂.G k
        = ∑ j : Fin Z₁.h, γ (Fin.cast hh j) • Z₂.G (Fin.cast hh j) :=
      (Equiv.sum_comp (Fin.castOrderIso hh).toEquiv (fun k => γ k • Z₂.G k)).symm
    have heq : ∀ j : Fin Z₁.h,
        β j • (Z₁.G j - Z₂.G (Fin.cast hh j)) + γ (Fin.cast hh j) • Z₂.G (Fin.cast hh j)
          = (β j * (1 - μ j) + γ (Fin.cast hh j) * μ j) • Z₁.G j := by
      intro j; rw [hG j]; module
    calc Z₁.c - Z₂.c + ∑ j, β j • (Z₁.G j - Z₂.G (Fin.cast hh j))
          + (Z₂.c + ∑ k, γ k • Z₂.G k)
        = Z₁.c + (∑ j, β j • (Z₁.G j - Z₂.G (Fin.cast hh j))
            + ∑ j, γ (Fin.cast hh j) • Z₂.G (Fin.cast hh j)) := by rw [hsum]; abel
      _ = Z₁.c + ∑ j, (β j • (Z₁.G j - Z₂.G (Fin.cast hh j))
            + γ (Fin.cast hh j) • Z₂.G (Fin.cast hh j)) := by rw [← Finset.sum_add_distrib]
      _ = Z₁.c + ∑ i, (β i * (1 - μ i) + γ (Fin.cast hh i) * μ i) • Z₁.G i := by
          rw [Finset.sum_congr rfl (fun j _ => heq j)]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
