module

public import CORALean.ContSet.Zonotope.Float.Operations.Radius
public import CORALean.ContSet.Zonotope.Float.Theorems.MemNominalSet

@[expose] public section

/-!
# Every point of a float zonotope is within `radius` of the stored center

A point is `c + ∑ⱼ βⱼ Gⱼ + e` with `|βⱼ| ≤ 1` and `e` in the error box. Against the generator
lengths it is the triangle inequality, `‖∑ βⱼ Gⱼ‖₂ ≤ ∑ⱼ ‖Gⱼ‖₂`, and `‖e‖₂ ≤ ‖err‖₂`. Against the
box it is coordinatewise, `|∑ⱼ βⱼ Gᵢⱼ| ≤ ∑ⱼ |Gᵢⱼ|` and `|eᵢ| ≤ errᵢ`, then the norm.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Pointwise FloatOps SoundFloatArithmetic InflatedContSet

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zonotope.radius_le (k : ℕ) (Z : Zonotope (Vec 𝕋 n)) {x : Vec ℝ n} (hx : x ∈ Z.construct) :
    ‖x - toRealVec Z.c‖₂ ≤ toReal (Z.radius k) := by -- --- PROOF ---
  obtain ⟨z, hzmem, e, he, rfl⟩ := hx
  obtain ⟨β, hβ, hz⟩ := Zonotope.mem_nominalSet_iff.mp hzmem
  -- the error box, by its largest magnitude
  set mg : Fin n → 𝕋 := fun i => maximum (absolute (Z.I_error.inf i)) (absolute (Z.I_error.sup i))
  have herr : ∀ i, |e i| ≤ |toReal (mg i)| := by
    intro i
    have h := abs_le_max_abs_abs (he i).1 (he i).2
    rw [toReal_maximum, toReal_absolute, toReal_absolute]
    exact le_trans h (le_abs_self _)
  have hvec : z + e - toRealVec Z.c =
      (∑ j, β j • fun i => toReal (Z.G j i)) + e := by
    funext i
    simp only [Pi.sub_apply, Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    rw [hz i, toRealVec]
    rw [Finset.sum_congr rfl fun j _ => mul_comm (β j) (toReal (Z.G j i))]
    ring
  have hErr := norm₂_le_normUp k herr
  -- the same bound is nonnegative
  have herr₀ : ∀ i, 0 ≤ toReal (mg i) := by
    intro i
    rw [toReal_maximum, toReal_absolute]
    exact le_max_of_le_left (abs_nonneg _)
  show _ ≤ toReal (minimum _ _)
  rw [toReal_minimum]
  refine le_min ?_ ?_
  · -- the generator lengths
    rw [hvec]
    have hsum : ‖∑ j, β j • fun i => toReal (Z.G j i)‖₂ ≤
        toReal (sumUp fun j => normUp k (Z.G j)) := by
      refine le_trans (norm₂_sum_le _ _) (le_trans ?_ (sum_le_sumUp _))
      refine Finset.sum_le_sum fun j _ => ?_
      rw [norm₂_smul]
      exact le_trans (mul_le_of_le_one_left (norm₂_nonneg _) (hβ j))
        (norm₂_le_normUp k fun _ => le_rfl)
    have h₁ := add_le_addUp (sumUp fun j => normUp k (Z.G j))
      (normUp k mg)
    exact le_trans (norm₂_add_le _ _) (le_trans (add_le_add hsum hErr) h₁)
  · -- the box
    refine norm₂_le_normUp k fun i => ?_
    have hgen := abs_sum_le_radius (d := fun i j => Z.G j i) (Δ := fun i j => toReal (Z.G j i))
      (fun _ _ => le_refl _) hβ i
    have h₁ := add_le_addUp (CORALean.Float.radius (fun i j => Z.G j i) i) (mg i)
    have h₂ : |e i| ≤ toReal (mg i) := by rw [← abs_of_nonneg (herr₀ i)]; exact herr i
    have hv : (z + e - toRealVec Z.c) i = ∑ j, toReal (Z.G j i) * β j + e i := by
      simp only [Pi.sub_apply, Pi.add_apply, toRealVec]
      rw [hz i]; ring
    rw [hv]
    refine le_trans (abs_add_le _ _) (le_trans ?_ (le_abs_self _))
    linarith

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
