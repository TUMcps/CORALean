module

public import CORALean.ContSet.Capsule.Float.Capsule
public import CORALean.ContSet.InflatedContSet.Operations.Bound
public import CORALean.ContSet.Interval.Float.Operations.BoundDot
public import CORALean.ContSet.Capsule.Real.Operations.SupportBound
public import CORALean.Global.Float.EuclideanNorm
public import CORALean.Global.Float.FloatBound
public import CORALean.Global.Float.Sqrt

@[expose] public section

/-!
# A capsule answers a direction in floats, the root computed

`Capsule.boundDot` with the ball's length no longer proposed by the caller: the norm of the
direction is `normUp`, Newton's iteration from above run for `p` steps, so there is no
certificate to supply and nothing to prove at the call site. The exact value is
`⟨a, c⟩ + |⟨a, g⟩| + r ‖a‖₂`, the three terms added upward.

A negative radius denotes `∅`, where the bound is vacuous, as over ℝ. The error box's own bound
(`Interval.boundDot`) is added upward.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       02-October-2026
-- Last update:   18-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def Capsule.boundDotUp (C : Capsule 𝕋 n) {f : Vec ℝ n →ₗ[ℝ] ℝ} (a : Vec 𝕋 n)
    (hf : ∀ x : Vec ℝ n, f x = ∑ i, toReal (a i) * x i) (p : ℕ) :
    FloatBound 𝕋 C.construct f :=
  let segment : 𝕋 := maximum (dotUp a C.g) (neg (dotDown a C.g))
  -- the nominal capsule's bound, then the error box's, added upward
  let nominalPart : FloatBound 𝕋 (InflatedContSet.nominalSet C) f :=
    { val := addUp (addUp (dotUp a C.c) segment) (mulUp C.r (normUp p a))
      le := fun x hx => by
        -- the three terms' roundings, then the exact bound they cover
        have h₁ : f C.nominal.c ≤ toReal (dotUp a C.c) := by
          rw [hf]
          exact le_dotUp a C.c
        have h₂ : |f C.nominal.g| ≤ toReal segment := by
          have hval : f C.nominal.g = ∑ k, toReal (a k) * toReal (C.g k) := hf _
          rw [hval, toReal_maximum, toReal_neg]
          refine abs_le.mpr ⟨?_, ?_⟩
          · have hdown := dotDown_le a C.g
            have hm := le_max_right (toReal (dotUp a C.g)) (-toReal (dotDown a C.g))
            linarith
          · have hup := le_dotUp a C.g
            have hm := le_max_left (toReal (dotUp a C.g)) (-toReal (dotDown a C.g))
            linarith
        have h₃ := add_le_addUp (dotUp a C.c) segment
        have h₄ := add_le_addUp (addUp (dotUp a C.c) segment) (mulUp C.r (normUp p a))
        have hx' := C.nominal.supportBound f |>.le x hx
        by_cases hr : 0 ≤ C.nominal.r
        · -- a nonnegative radius: the norm's certified length times it, rounded up
          have hw : Real.sqrt (∑ i, f (Pi.single i 1) ^ 2) ≤ toReal (normUp p a) := by
            refine norm₂_le_normUp (m := a) p (fun j => ?_)
            rw [hf]
            simp [Pi.single_apply]
          have h₅ : C.nominal.r * Real.sqrt (∑ i, f (Pi.single i 1) ^ 2)
              ≤ toReal (mulUp C.r (normUp p a)) :=
            le_trans (mul_le_mul_of_nonneg_left hw hr) (mul_le_mulUp _ _)
          have h₆ : f C.nominal.c + |f C.nominal.g|
              + C.nominal.r * Real.sqrt (∑ i, f (Pi.single i 1) ^ 2)
              ≤ toReal (addUp (addUp (dotUp a C.c) segment) (mulUp C.r (normUp p a))) := by
            linarith
          exact le_trans hx' h₆
        · -- a negative radius denotes `∅`: the witness bounds a norm by a negative number
          obtain ⟨t, _, hle⟩ := hx
          exact absurd (le_trans (norm₂_nonneg _) hle) hr }
  InflatedContSet.boundOfParts nominalPart (C.I_error.boundDot a hf)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
