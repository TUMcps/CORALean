import CORALean.ContSet.Capsule.Float.Operations.ContainsPoint
import CORALean.ContSet.Capsule.Real.Theorems.MemConstructIffNorm

/-!
# `Capsule.containsPoint` is sound

A `true` answer exhibits the clipped parameter `t ∈ [-1, 1]` and a certified bound on the length
of `p - c - t g`: the squared length rounded up is at most `r²` rounded down, with `r ≥ 0`. So
the point is in the capsule. `false` refutes nothing.
-/

-- Authors:       Tobias Ladner
-- Written:       03-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Capsule.containsPoint_sound {C : Capsule 𝕋 n} {p : Vec 𝕋 n}
    (h : C.containsPoint p = true) : toRealVec p ∈ C.construct := by -- --- PROOF ---
  unfold Capsule.containsPoint at h
  rw [Bool.and_eq_true] at h
  obtain ⟨hr, hsq⟩ := h
  have hr0 : 0 ≤ toReal C.r := by simpa [toReal_zero] using toReal_le_of_le hr
  -- the clipped parameter lies in `[-1, 1]`
  set t := maximum (neg (one : 𝕋)) (minimum one
    (divUp (dotUp (fun i => subUp (p i) (C.c i)) C.g) (dotUp C.g C.g))) with ht
  have ht1 : -1 ≤ toReal t ∧ toReal t ≤ 1 := by
    rw [ht, toReal_maximum, toReal_neg, toReal_one, toReal_minimum, toReal_one]
    exact ⟨le_max_left _ _, max_le (by norm_num) (min_le_left _ _)⟩
  refine (Real.Capsule.mem_construct_iff_norm₂ C.nominal _).mpr ⟨toReal t, ht1, ?_⟩
  -- each entry of `p - c - t g` is below the magnitude the directed arithmetic bracketed
  have hm : ∀ j, |((toRealVec p - toRealVec C.c) - toReal t • toRealVec C.g) j| ≤ toReal
      (maximum (neg (subDown (addDown (C.c j) (mulDown t (C.g j))) (p j)))
        (subUp (addUp (C.c j) (mulUp t (C.g j))) (p j))) := by
    intro j
    -- the bracket `lo ≤ c + t g - p ≤ hi`
    have h1 := subDown_le_sub (addDown (C.c j) (mulDown t (C.g j))) (p j)
    have h2 := sub_le_subUp (addUp (C.c j) (mulUp t (C.g j))) (p j)
    have h3 := addDown_le_add (C.c j) (mulDown t (C.g j))
    have h4 := add_le_addUp (C.c j) (mulUp t (C.g j))
    have h5 := mulDown_le_mul t (C.g j)
    have h6 := mul_le_mulUp t (C.g j)
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, toRealVec]
    have hmax := toReal_maximum (neg (subDown (addDown (C.c j) (mulDown t (C.g j))) (p j)))
      (subUp (addUp (C.c j) (mulUp t (C.g j))) (p j))
    rw [toReal_neg] at hmax
    rw [hmax, abs_le]
    have h7 := le_max_left (-toReal (subDown (addDown (C.c j) (mulDown t (C.g j))) (p j)))
      (toReal (subUp (addUp (C.c j) (mulUp t (C.g j))) (p j)))
    have h8 := le_max_right (-toReal (subDown (addDown (C.c j) (mulDown t (C.g j))) (p j)))
      (toReal (subUp (addUp (C.c j) (mulUp t (C.g j))) (p j)))
    constructor <;> linarith
  have hn := norm₂_le_of_sq_le hm (toReal_le_of_le hsq)
  rw [toReal_absolute, abs_of_nonneg hr0] at hn
  exact hn

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
