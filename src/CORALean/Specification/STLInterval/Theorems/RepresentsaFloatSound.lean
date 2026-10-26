module

public import CORALean.Specification.STLInterval.Definitions.Representsa
public import CORALean.Specification.STLInterval.Operations.RepresentsaFloat
public import CORALean.Specification.STLInterval.Theorems.WithinTolFloatIff

@[expose] public section

/-!
# `representsaFloat` is sound

A `true` answer of `representsaFloat` holds for the interval read as reals and the tolerance read as
a real: the shape tests are exact, the `'origin'` test is the exact `withinTol` of the bounds, and
the `'point'` test bounds the radius from above.

## Inputs
* `tol` – tolerance
* `I` – STL interval
* `type` – set type asked about

## Hypotheses
* `h` – the float answer is `true`

## Conclusion
* the interval can be represented by the set type
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       26-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Float FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] [ExactLe 𝕋]


-- =======================================  MAIN THEOREM  ======================================= --

theorem STLInterval.representsaFloat_sound (tol : 𝕋) (I : STLInterval 𝕋)
    (type : STLInterval.RepresentsaType) (h : I.representsaFloat tol type = true) : -- --- CONCL ---
    I.representsa_ (toReal tol) type := by -- --- PROOF ---
  rcases I with _ | ⟨l, u, lc, rc, hu, hlt, h0⟩
  · cases type <;> simp_all [STLInterval.representsaFloat, STLInterval.representsa_]
  · cases type
    · simp [STLInterval.representsaFloat] at h
    · simp [STLInterval.representsa_]
    · -- the point: the rounded-up radius within the tolerance bounds the radius
      simp only [STLInterval.representsaFloat, Bool.and_eq_true] at h
      obtain ⟨⟨hl, hr⟩, hm⟩ := h
      refine ⟨hl, hr, ?_⟩
      rcases u with _ | u
      · simp at hm
      · -- the radius is nonnegative and at most the rounded-up one
        have hle : toReal l ≤ toReal u := by
          rcases hlt with h | ⟨h, -⟩ <;> rw [STLInterval.toEReal_some] at h
          · exact (EReal.coe_lt_coe_iff.1 h).le
          · exact (EReal.coe_eq_coe_iff.1 h).le
        have hup : (toReal u - toReal l) / 2 ≤ toReal (half (addUp u (neg l))) := by
          have := add_le_addUp u (neg l)
          rw [toReal_neg] at this
          rw [toReal_half]
          linarith
        refine ⟨toReal u, STLInterval.toEReal_some .., ?_⟩
        rw [ExactLe.withinTol_iff, toReal_zero] at hm
        refine Or.inl ⟨(toReal u - toReal l) / 2, 0, rfl, by simp, ?_⟩
        rcases hm with h | h
        · left
          rw [sub_zero] at h ⊢
          rw [abs_of_nonneg (by linarith)]
          exact hup.trans ((le_abs_self _).trans h)
        · right
          -- a radius of zero: the rounded-up radius is zero, and so is the radius
          simp only [sub_zero, abs_zero] at h ⊢
          rw [min_eq_right (abs_nonneg _), mul_zero] at h ⊢
          have hr0 : toReal (half (addUp u (neg l))) ≤ 0 := (le_abs_self _).trans h
          exact abs_nonpos_iff.2 (le_antisymm (hup.trans hr0) (by linarith))
    · -- the origin: both bounds within the tolerance of zero, decided exactly
      simp only [STLInterval.representsaFloat, Bool.and_eq_true] at h
      obtain ⟨⟨⟨hl, hr⟩, h1⟩, h2⟩ := h
      refine ⟨hl, hr, ?_, ?_⟩
      · have := (STLInterval.withinTolFloat_iff tol (l : WithTop 𝕋) (zero : 𝕋)).mp h1
        simpa [toReal_zero] using this
      · have := (STLInterval.withinTolFloat_iff tol u (zero : 𝕋)).mp h2
        simpa [toReal_zero] using this

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
