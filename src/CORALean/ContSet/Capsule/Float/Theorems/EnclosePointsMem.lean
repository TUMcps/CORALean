import CORALean.ContSet.Capsule.Float.Operations.EnclosePoints

/-!
# `Capsule.enclosePoints` holds every point

For a point `p`, the stored centre `c`, generator `g` and the clamped parameter `t`, the
residual `p - (c + t g)` is bounded entry by entry between two directed roundings, so its length is
at most `normUp` of the larger absolute bound, which the stored radius takes the maximum of.
Nothing here depends on the mean, the farthest point or the projection being computed accurately:
they only decide how large the radius becomes.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- One entry of the residual lies between the two roundings, so its magnitude is under the
larger of theirs. -/
theorem Capsule.aux_residual_le (p c g t : 𝕋) :
    |toReal p - (toReal c + toReal t * toReal g)| ≤
      |toReal (maximum (absolute (subDown (subDown p c) (mulUp t g)))
        (absolute (subUp (subUp p c) (mulDown t g))))| := by -- --- PROOF ---
  have l₁ := subDown_le_sub (subDown p c) (mulUp t g)
  have l₂ := subDown_le_sub p c
  have l₃ := mul_le_mulUp t g
  have u₁ := sub_le_subUp (subUp p c) (mulDown t g)
  have u₂ := sub_le_subUp p c
  have u₃ := mulDown_le_mul t g
  rw [toReal_maximum, toReal_absolute, toReal_absolute]
  refine le_trans ?_ (le_abs_self _)
  have a₁ := neg_abs_le (toReal (subDown (subDown p c) (mulUp t g)))
  have a₂ := le_abs_self (toReal (subUp (subUp p c) (mulDown t g)))
  have m₁ := le_max_left |toReal (subDown (subDown p c) (mulUp t g))|
    |toReal (subUp (subUp p c) (mulDown t g))|
  have m₂ := le_max_right |toReal (subDown (subDown p c) (mulUp t g))|
    |toReal (subUp (subUp p c) (mulDown t g))|
  rw [abs_le]
  constructor <;> linarith


-- =======================================  MAIN THEOREM  ======================================= --

theorem Capsule.range_subset_construct (k : ℕ) {N : ℕ} (pts : Fin N → Vec 𝕋 n) :
    Set.range (fun j => toRealVec (pts j)) ⊆
      (Capsule.enclosePoints k pts).construct := by -- --- PROOF ---
  rintro _ ⟨j, rfl⟩
  -- a point exists, so the first branch of the definition is the one taken
  have hN : 0 < N := j.pos
  unfold Capsule.enclosePoints
  rw [dif_pos hN]
  dsimp only
  -- name the stored centre, farthest point, generator and parameter
  set c : Vec 𝕋 n := fun i => divUp (sumUp fun j => pts j i) (nsmulUp N one) with hc
  set d : Fin N → Vec 𝕋 n := fun j i => subUp (pts j i) (c i) with hd
  set jmax := (List.finRange N).foldl (fun b j =>
    if le (sqSumUp fun i => absolute (d b i)) (sqSumUp fun i => absolute (d j i)) then j else b)
    ⟨0, hN⟩ with hjmax
  set g : Vec 𝕋 n := d jmax with hg
  set t : Fin N → 𝕋 := fun j => minimum (maximum (divUp (dotUp (d j) g)
    (sqSumUp fun i => absolute (g i))) (neg one)) one with ht
  -- the clamped parameter is in `[-1, 1]`, whatever it was computed from
  have ht₁ : -1 ≤ toReal (t j) := by
    rw [ht]; dsimp only
    rw [toReal_minimum, toReal_maximum, toReal_neg, toReal_one]
    exact le_min (le_max_right _ _) (by norm_num)
  have ht₂ : toReal (t j) ≤ 1 := by
    rw [ht]; dsimp only
    rw [toReal_minimum, toReal_one]
    exact min_le_right _ _
  refine ⟨toReal (t j), ⟨ht₁, ht₂⟩, ?_⟩
  -- the residual is under `normUp` of its entrywise bounds, which the radius takes the maximum of
  refine le_trans (norm₂_le_normUp k (m := fun i => maximum
      (absolute (subDown (subDown (pts j i) (c i)) (mulUp (t j) (g i))))
      (absolute (subUp (subUp (pts j i) (c i)) (mulDown (t j) (g i))))) fun i => ?_)
    (le_maximumOver (fun j => normUp k fun i => maximum
      (absolute (subDown (subDown (pts j i) (c i)) (mulUp (t j) (g i))))
      (absolute (subUp (subUp (pts j i) (c i)) (mulDown (t j) (g i))))) j)
  exact Capsule.aux_residual_le (pts j i) (c i) (g i) (t j)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
