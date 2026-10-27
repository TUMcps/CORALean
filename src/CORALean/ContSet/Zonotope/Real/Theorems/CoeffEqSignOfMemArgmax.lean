module

public import CORALean.ContSet.Zonotope.Real.Zonotope
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Data.Real.Sign
public import Mathlib.Tactic.Linarith

@[expose] public section

/-!
# On an exposed face, the coefficients off the annihilated generators are signs

A point `x` of the zonotope `Z = c + ∑ βⱼgⱼ, |βⱼ| ≤ 1` that maximizes the functional `u` over `Z`
has `u x = u c + ∑ⱼ |u gⱼ|`, the largest value any coefficients reach. So every coefficient vector
`β` representing `x`, not only some, has `βⱼ u gⱼ = |u gⱼ|` for every `j`, which pins `βⱼ = sign(u
gⱼ)` wherever `u gⱼ ≠ 0`. The same forcing argument as `face_centrally_symmetric`, read off as a
statement about the coefficients behind [1, Sec. 3 (faces)]: it is what makes the face `c + ∑ sign(u
gⱼ)gⱼ` plus the zonotope of the generators `u` annihilates (`construct_face`), and what makes a
point's coefficients usable on every face through it at once (`exists_raise_degree`).

## Inputs
* `Z` – zonotope
* `u` – linear functional
* `x` – maximizing point
* `β` – generator coefficients
* `j` – generator index

## Hypotheses
* `hx` – `x` maximizes `u` over `Z`
* `hβ` – coefficients within the unit box
* `hxβ` – `x` is the center plus the generator sum
* `hj` – `u` does not vanish on generator `j`

## Conclusion
* coefficient `j` equals the sign of `u` on generator `j`

## References

* [1] [M. Černý. "Goffin's algorithm for zonotopes". Kybernetika,
      2012.](../../../../../../references/2012/cerny-kybernetika-goffin-zonotopes.md)
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
private theorem Zonotope.aux_sign_mul_self_cesm (r : ℝ) : Real.sign r * r = |r| := by
  rcases lt_trichotomy r 0 with h | h | h
  · rw [Real.sign_of_neg h, abs_of_neg h, neg_one_mul]
  · rw [h, Real.sign_zero, abs_zero, mul_zero]
  · rw [Real.sign_of_pos h, abs_of_pos h, one_mul]

/-- A coefficient of modulus at most one contributes at most `|r|`. -/
private theorem Zonotope.aux_term_le_cesm {b r : ℝ} (hb : |b| ≤ 1) : b * r ≤ |r| :=
  calc b * r ≤ |b * r| := le_abs_self _
    _ = |b| * |r| := abs_mul _ _
    _ ≤ 1 * |r| := mul_le_mul_of_nonneg_right hb (abs_nonneg _)
    _ = |r| := one_mul _


-- =======================================  MAIN THEOREM  ======================================= --

/-- Every coefficient vector of a point maximizing `u` over `Z` has `βⱼ = sign(u gⱼ)` wherever
`u gⱼ ≠ 0`. -/
theorem Zonotope.coeff_eq_sign_of_mem_argmax (Z : Zonotope α) (u : α →ₗ[ℝ] ℝ) {x : α}
    (hx : x ∈ {x | x ∈ Z.construct ∧ ∀ y ∈ Z.construct, u y ≤ u x}) {β : Fin Z.h → ℝ}
    (hβ : ∀ j, |β j| ≤ 1) (hxβ : x = Z.c + ∑ j, β j • Z.G j) (j : Fin Z.h)
    (hj : u (Z.G j) ≠ 0) : -- --- CONCL ---
    β j = Real.sign (u (Z.G j)) := by -- --- PROOF ---
  -- the farthest point, with the sign coefficients, bounds `u x` from below
  have hmem : Z.c + ∑ i, Real.sign (u (Z.G i)) • Z.G i ∈ Z.construct := by
    refine ⟨fun i => Real.sign (u (Z.G i)), fun i => ?_, rfl⟩
    show |Real.sign (u (Z.G i))| ≤ 1
    rcases Real.sign_apply_eq (u (Z.G i)) with h | h | h <;> rw [h] <;> simp
  have h1 := hx.2 _ hmem
  rw [hxβ, map_add, map_sum, map_add, map_sum] at h1
  simp only [map_smul, smul_eq_mul, aux_sign_mul_self_cesm] at h1
  have hnn : ∀ i ∈ Finset.univ, 0 ≤ |u (Z.G i)| - β i * u (Z.G i) :=
    fun i _ => sub_nonneg.mpr (aux_term_le_cesm (hβ i))
  have hle : ∑ i, β i * u (Z.G i) ≤ ∑ i, |u (Z.G i)| :=
    Finset.sum_le_sum fun i _ => aux_term_le_cesm (hβ i)
  have hsum : ∑ i, (|u (Z.G i)| - β i * u (Z.G i)) = 0 := by
    rw [Finset.sum_sub_distrib]
    linarith
  -- a vanishing sum of nonnegative terms vanishes termwise, so `βⱼ u gⱼ = |u gⱼ|`
  have hj0 := (Finset.sum_eq_zero_iff_of_nonneg hnn).mp hsum j (Finset.mem_univ j)
  have hr : β j * u (Z.G j) = Real.sign (u (Z.G j)) * u (Z.G j) := by
    rw [aux_sign_mul_self_cesm]
    linarith
  exact mul_right_cancel₀ hj hr

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
