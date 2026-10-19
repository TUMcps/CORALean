module

public import CORALean.ContSet.Zonotope.Real.Theorems.CoeffEqSignOfMemArgmax

@[expose] public section

/-!
# The points of a zonotope that maximize a functional

A point of `Z = c + ∑ βⱼgⱼ, |βⱼ| ≤ 1` maximizes `u` over `Z` exactly when some coefficients of it
have `βⱼ = sign(u gⱼ)` wherever `u gⱼ ≠ 0`. Forward is `coeff_eq_sign_of_mem_argmax`, which gives it
for every coefficient vector; back, such coefficients make every term `βⱼ u gⱼ` equal to `|u gⱼ|`,
the most a term can be. The exposed face in direction `u` is therefore read off the generators alone
[1, Sec. 3 (faces)], `u gⱼ = 0` leaving `gⱼ` free and the others pinned to a sign
(`construct_face`).

## References

* [1] M. Černý. "Goffin's algorithm for zonotopes". Kybernetika, 48(5):890-906, 2012.
-/

-- Authors:       Claude Opus 5.5
-- Written:       11-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- `sign r · r = |r|`. -/
theorem Zonotope.aux_sign_mul_self_mai (r : ℝ) : Real.sign r * r = |r| := by
  rcases lt_trichotomy r 0 with h | h | h
  · rw [Real.sign_of_neg h, abs_of_neg h, neg_one_mul]
  · rw [h, Real.sign_zero, abs_zero, mul_zero]
  · rw [Real.sign_of_pos h, abs_of_pos h, one_mul]


-- =======================================  MAIN THEOREM  ======================================= --

/-- `x` maximizes `u` over `Z` iff some coefficients of it are `sign(u gⱼ)` wherever
`u gⱼ ≠ 0`. -/
theorem Zonotope.mem_argmax_iff (Z : Zonotope α) (u : α →ₗ[ℝ] ℝ) (x : α) : -- --- CONCL ---
    x ∈ {x | x ∈ Z.construct ∧ ∀ y ∈ Z.construct, u y ≤ u x} ↔
      ∃ β : Fin Z.h → ℝ, (∀ j, |β j| ≤ 1) ∧
        (∀ j, u (Z.G j) ≠ 0 → β j = Real.sign (u (Z.G j))) ∧
        x = Z.c + ∑ j, β j • Z.G j := by -- --- PROOF ---
  constructor
  · intro hx
    obtain ⟨β, hβ, hxβ⟩ := hx.1
    exact ⟨β, hβ, fun j hj => Z.coeff_eq_sign_of_mem_argmax u hx hβ hxβ j hj, hxβ⟩
  · rintro ⟨β, hβ, hpin, rfl⟩
    refine ⟨⟨β, hβ, rfl⟩, ?_⟩
    rintro _ ⟨γ, hγ, rfl⟩
    -- every term of `x` is the largest a term can be
    have hterm : ∀ j, β j * u (Z.G j) = |u (Z.G j)| := fun j => by
      by_cases hj : u (Z.G j) = 0
      · rw [hj, mul_zero, abs_zero]
      · rw [hpin j hj, aux_sign_mul_self_mai]
    have hle : ∑ j, γ j * u (Z.G j) ≤ ∑ j, |u (Z.G j)| :=
      Finset.sum_le_sum fun j _ =>
        calc γ j * u (Z.G j) ≤ |γ j * u (Z.G j)| := le_abs_self _
          _ = |γ j| * |u (Z.G j)| := abs_mul _ _
          _ ≤ 1 * |u (Z.G j)| := mul_le_mul_of_nonneg_right (hγ j) (abs_nonneg _)
          _ = |u (Z.G j)| := one_mul _
    rw [map_add, map_sum, map_add, map_sum]
    simp only [map_smul, smul_eq_mul]
    rw [Finset.sum_congr rfl fun j _ => hterm j]
    linarith

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
