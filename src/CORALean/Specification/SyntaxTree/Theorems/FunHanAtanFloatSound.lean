module

public import CORALean.Specification.SyntaxTree.Definitions.IsSoundFloat
public import CORALean.Specification.SyntaxTree.Operations.FunHanAtanFloat
public import CORALean.Specification.SyntaxTree.Theorems.Basic
public import CORALean.Specification.SyntaxTree.Theorems.MeetContainsFloat
public import CORALean.Specification.SyntaxTree.Theorems.PiFloatContains

@[expose] public section

/-!
# `aaux_tan_` over floats is sound

`SyntaxTree.funHanAtanFloat` keeps every solution of `atan s ∈ int`: `s` is the tangent of its
inverse, which lies strictly inside `(-pi/2, pi/2)`, where the tangent is increasing; a bound is
used only where it is certified inside that range with a positive cosine, so `tanDown` and `tanUp`
bound it.

## Inputs
* `p` – precision of the tangent and of `pi`
* `k` – Newton steps of `pi`
* `prev` – previous interval
* `v` – value interval

## Hypotheses
* none

## Conclusion
* the float inverse of the inverse tangent keeps every solution
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       25-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Float Float.FloatOps Float.SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋]


-- =======================================  MAIN THEOREM  ======================================= --

/-- `aaux_tan_` over floats is sound for `atan`. -/
theorem SyntaxTree.funHanAtanFloat_sound (p k : ℕ)
    (prev v : Float.SyntaxTree.Dom 𝕋) : -- --- CONCL ---
    SyntaxTree.IsUnarySoundFloat SyntaxTree.Unary.atan.fn prev v
      (SyntaxTree.funHanAtanFloat p k) := by -- --- PROOF ---
  intro int _ s hs hi
  have hi' : int.contains (Real.arctan s) := hi
  have hπ := SyntaxTree.piFloat_contains (𝕋 := 𝕋) p k
  have hlo : toReal (half (SyntaxTree.piFloat (𝕋 := 𝕋) p k).inf) ≤ Real.pi / 2 := by
    rw [toReal_half]; linarith [hπ.1]
  have hhi : Real.pi / 2 ≤ toReal (half (SyntaxTree.piFloat (𝕋 := 𝕋) p k).sup) := by
    rw [toReal_half]; linarith [hπ.2]
  have ha1 := Real.neg_pi_div_two_lt_arctan s
  have ha2 := Real.arctan_lt_pi_div_two s
-- the upper bound is not below the range of the inverse tangent
  have hnd : ¬ ltStrict (int.sup 0) (neg (half (SyntaxTree.piFloat (𝕋 := 𝕋) p k).sup)) = true :=
    fun hc => by
    have := toReal_lt_of_ltStrict hc
    rw [toReal_neg] at this
    linarith [hi'.2]
-- the target is not rejected as out of domain
  unfold SyntaxTree.funHanAtanFloat
  dsimp only
  rw [if_neg hnd]
  refine ⟨_, rfl, SyntaxTree.meet_containsFloat hs (show _ ∧ _ from ⟨?_, ?_⟩)⟩
  · by_cases hc : ltStrict (neg (half (SyntaxTree.piFloat (𝕋 := 𝕋) p k).inf)) (int.inf 0) = true ∧
        ltStrict zero (cosDown p (int.inf 0)) = true
    · rw [if_pos hc]
      have h1 := toReal_lt_of_ltStrict hc.1
      rw [toReal_neg] at h1
      have h2 := toReal_lt_of_ltStrict hc.2
      rw [toReal_zero] at h2
      refine (tanDown_le p _ h2).trans ?_
      calc Real.tan (toReal (int.inf 0)) ≤ Real.tan (Real.arctan s) :=
            Real.strictMonoOn_tan.monotoneOn ⟨by linarith, by linarith [hi'.1]⟩ ⟨ha1, ha2⟩ hi'.1
        _ = s := Real.tan_arctan s
    · rw [if_neg hc]; exact hs.1
-- the upper bound is the tangent of the upper end where certified
  · by_cases hc : ltStrict (int.sup 0) (half (SyntaxTree.piFloat (𝕋 := 𝕋) p k).inf) = true ∧
        ltStrict zero (cosDown p (int.sup 0)) = true
    · rw [if_pos hc]
      have h1 := toReal_lt_of_ltStrict hc.1
      have h2 := toReal_lt_of_ltStrict hc.2
      rw [toReal_zero] at h2
      refine le_trans ?_ (le_tanUp p _ h2)
      calc s = Real.tan (Real.arctan s) := (Real.tan_arctan s).symm
        _ ≤ Real.tan (toReal (int.sup 0)) :=
            Real.strictMonoOn_tan.monotoneOn ⟨ha1, ha2⟩ ⟨by linarith [hi'.2], by linarith⟩ hi'.2
    · rw [if_neg hc]; exact hs.2

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
