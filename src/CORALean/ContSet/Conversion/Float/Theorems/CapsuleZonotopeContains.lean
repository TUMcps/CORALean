module

public import CORALean.ContSet.Conversion.Float.Operations.Capsule_to_Zonotope
public import CORALean.ContSet.Conversion.Float.Theorems.IntervalZonotopeContains
public import CORALean.ContSet.Zonotope.Float.Theorems.PlusOuter
public import CORALean.Global.EuclideanNorm

@[expose] public section

/-!
# A capsule as a zonotope, over a floating-point scalar

As over ℝ: a point of the capsule is a point `c + t g` of the segment, which `Z` carries with the
capsule's error box, plus a vector `y` of length at most `r`, whose coordinates are at most `r`
in absolute value, so `y` is in the box `[-r, r]ⁿ`, that box is in its zonotope
(`Interval.zonotope_contains`), and `Zonotope.plus_outer` joins the two. Where `le` finds `r`
zero, `y` is zero and the segment is all there is.
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   19-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Pointwise FloatOps SoundFloatArithmetic InflatedContSet

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Capsule.zonotope_contains (C : Capsule 𝕋 n) :
    C.construct ⊆ C.zonotope.construct := by -- --- PROOF ---
  rintro _ ⟨x, ⟨t, ht, hle⟩, e, he, rfl⟩
  -- what the segment point `c + t g` leaves of `x`, and the segment with the error box
  set y : Vec ℝ n := x - (toRealVec C.c + t • toRealVec C.g) with hy
  have hy2 : CORALean.norm₂ y ≤ toReal C.r := by
    have h : CORALean.norm₂ y =
        Real.sqrt (∑ i, (x i - (toReal (C.c i) + t * toReal (C.g i))) ^ 2) := by
      simp [CORALean.norm₂, hy, toRealVec]
    rw [h]
    exact hle
  have hseg : toRealVec C.c + t • toRealVec C.g + e ∈
      (⟨1, C.c, fun _ => C.g, C.I_error⟩ : Zonotope (Vec 𝕋 n)).construct :=
    ⟨_, ⟨fun _ => t, fun _ => abs_le.mpr ht,
      by simp [InflatedContSet.nominal, Zonotope.nominal, RealImage.realImage]⟩, e, he, rfl⟩
  unfold Capsule.zonotope
  split_ifs with hr
  · -- `r` is zero: `y = 0`, and the segment alone
    have hr0 : toReal C.r = 0 := by
      simp only [Bool.and_eq_true] at hr
      exact le_antisymm (by simpa [toReal_zero] using toReal_le_of_le hr.1)
        (by simpa [toReal_zero] using toReal_le_of_le hr.2)
    have hx : x = toRealVec C.c + t • toRealVec C.g := by
      have h0 : CORALean.norm₂ y = 0 := le_antisymm (hr0 ▸ hy2) (CORALean.norm₂_nonneg y)
      have h1 : y = 0 := by
        funext i
        have := CORALean.abs_le_norm₂ y i
        rw [h0] at this
        simpa using this
      exact sub_eq_zero.mp h1
    rwa [hx]
  · -- the ball's part: `y` in the box `[-r, r]ⁿ`, and the box in its zonotope
    have hB : y ∈ (⟨fun _ => neg C.r, fun _ => C.r⟩ : Interval (Vec 𝕋 n)).construct := fun i => by
      have h := CORALean.abs_le_norm₂ y i
      have h' := abs_le.mp (le_trans h hy2)
      show toReal (neg C.r) ≤ y i ∧ y i ≤ toReal C.r
      rw [toReal_neg]
      exact h'
    refine Zonotope.plus_outer _ _ ⟨_, hseg, y, Interval.zonotope_contains _ hB, ?_⟩
    rw [hy]
    abel

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
