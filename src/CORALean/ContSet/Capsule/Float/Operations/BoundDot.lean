import CORALean.ContSet.Capsule.Float.Capsule
import CORALean.ContSet.Capsule.Real.Operations.SupportBound
import CORALean.Global.Float.EuclideanNorm
import CORALean.Global.Float.FloatBound

/-!
# A capsule answers a direction in floats, without a linear program or a square root

The exact value is `⟨a, c⟩ + |⟨a, g⟩| + r ‖a‖₂`. The segment's term is the larger of the
upward-rounded dot product and the negated downward-rounded one, and the norm is a
square root the scalar has not got: the caller hands in a proposed length `s`, and
`Global.Float.EuclideanNorm` turns `s` into a bound by one multiplication in each rounding
direction. The three terms are added upward.

No `0 ≤ r` hypothesis, as over ℝ: a negative radius denotes `∅`, where the bound is
vacuous. A capsule has no error box, so nothing is added for one.
-/

-- Authors:       Tobias Ladner
-- Written:       02-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def Capsule.boundDot (C : Capsule 𝕋 n) {f : Vec ℝ n →ₗ[ℝ] ℝ} (a : Vec 𝕋 n)
    (hf : ∀ x : Vec ℝ n, f x = ∑ i, toReal (a i) * x i) (s : 𝕋)
    (hs : toReal (sqSumUp fun i => absolute (a i)) ≤ toReal (mulDown s s)) :
    FloatBound 𝕋 C.construct f :=
  let segment : 𝕋 := maximum (dotUp a C.g) (neg (dotDown a C.g))
  { val := addUp (addUp (dotUp a C.c) segment) (mulUp C.r (absolute s))
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
      have h₄ := add_le_addUp (addUp (dotUp a C.c) segment) (mulUp C.r (absolute s))
      have hx' := C.nominal.supportBound f |>.le x hx
      by_cases hr : 0 ≤ C.nominal.r
      · -- a nonnegative radius: the norm's certified length times it, rounded up
        have hw : Real.sqrt (∑ i, f (Pi.single i 1) ^ 2) ≤ toReal (absolute s) := by
          refine norm₂_le_of_sq_le (m := fun i => absolute (a i)) (fun j => ?_) hs
          rw [toReal_absolute, hf]
          simp [Pi.single_apply]
        have h₅ : C.nominal.r * Real.sqrt (∑ i, f (Pi.single i 1) ^ 2)
            ≤ toReal (mulUp C.r (absolute s)) :=
          le_trans (mul_le_mul_of_nonneg_left hw hr) (mul_le_mulUp _ _)
        have h₆ : f C.nominal.c + |f C.nominal.g|
            + C.nominal.r * Real.sqrt (∑ i, f (Pi.single i 1) ^ 2)
            ≤ toReal (addUp (addUp (dotUp a C.c) segment) (mulUp C.r (absolute s))) := by
          linarith
        exact le_trans hx' h₆
      · -- a negative radius denotes `∅`: the witness bounds a norm by a negative number
        obtain ⟨t, _, hle⟩ := hx
        exact absurd (le_trans (norm₂_nonneg _) hle) hr }

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
