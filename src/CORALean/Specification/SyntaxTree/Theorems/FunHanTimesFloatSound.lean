module

public import CORALean.ContSet.Interval.Float.Theorems.RdivideOuter
public import CORALean.Specification.SyntaxTree.Definitions.IsSoundFloat
public import CORALean.Specification.SyntaxTree.Operations.FunHanTimesFloat
public import CORALean.Specification.SyntaxTree.Theorems.Basic
public import CORALean.Specification.SyntaxTree.Theorems.MeetContainsFloat

@[expose] public section

/-!
# `aux_times_` over floats is sound

`SyntaxTree.funHanTimesFloat` keeps every solution of `s₁ * s₂ ∈ int`: where `0` is certified
outside the partner, the operand is the product over the partner, which the rounded quotient
encloses; elsewhere it keeps its interval.

## Inputs
* `prev₁` – first previous interval
* `prev₂` – second previous interval
* `v` – value interval

## Hypotheses
* none

## Conclusion
* the float backpropagation of the product keeps every solution
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       25-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Float Float.FloatOps Float.SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋]


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The quotient of a point of `int` by a point of an interval avoiding `0` lies in the quotient. -/
private theorem SyntaxTree.aux_quotient_containsFloat {int J : Float.SyntaxTree.Dom 𝕋} {c t : ℝ}
    (hJ : ltStrict zero (J.inf 0) = true ∨ ltStrict (J.sup 0) zero = true) (hc : int.contains c)
    (ht : J.contains t) : -- --- CONCL ---
    Float.SyntaxTree.Dom.contains (Float.Interval.rdivide int J) (c / t) := by -- --- PROOF ---
  have hJ' : ∀ i, ltStrict zero (J.inf i) = true ∨ ltStrict (J.sup i) zero = true := fun i => by
    obtain rfl : i = 0 := Subsingleton.elim i 0
    exact hJ
  have hmem := Float.Interval.rdivide_outer int J hJ'
    ⟨fun _ => c, fun i => by obtain rfl : i = 0 := Subsingleton.elim i 0; exact hc, fun _ => t,
      fun i => by obtain rfl : i = 0 := Subsingleton.elim i 0; exact ht, rfl⟩
  exact hmem 0

/-- A certified exclusion of `0` keeps the point away from `0`. -/
private theorem SyntaxTree.aux_ne_zero_of_certFloat {J : Float.SyntaxTree.Dom 𝕋} {t : ℝ}
    (hJ : ltStrict zero (J.inf 0) = true ∨ ltStrict (J.sup 0) zero = true)
    (ht : J.contains t) : -- --- CONCL ---
    t ≠ 0 := by -- --- PROOF ---
  rcases hJ with h | h
  · have := toReal_lt_of_ltStrict h
    rw [toReal_zero] at this
    exact (this.trans_le ht.1).ne'
  · have := toReal_lt_of_ltStrict h
    rw [toReal_zero] at this
    exact (ht.2.trans_lt this).ne

/-- The operand of a product that lies in `int` is held by `int` over a partner avoiding `0`. -/
private theorem SyntaxTree.aux_operand_containsFloat {int J : Float.SyntaxTree.Dom 𝕋} {s t : ℝ}
    (hJ : ltStrict zero (J.inf 0) = true ∨ ltStrict (J.sup 0) zero = true)
    (hi : int.contains (s * t)) (ht : J.contains t) :
    Float.SyntaxTree.Dom.contains (Float.Interval.rdivide int J) s := by
  have q := SyntaxTree.aux_quotient_containsFloat hJ hi ht
  rwa [mul_div_cancel_right₀ _ (SyntaxTree.aux_ne_zero_of_certFloat hJ ht)] at q


-- =======================================  MAIN THEOREM  ======================================= --

/-- `aux_times_` over floats is sound for the product. -/
theorem SyntaxTree.funHanTimesFloat_sound
    (prev₁ prev₂ v : Float.SyntaxTree.Dom 𝕋) : -- --- CONCL ---
    SyntaxTree.IsBinarySoundFloat SyntaxTree.Binary.times.fn prev₁ prev₂ v
      SyntaxTree.funHanTimesFloat := by -- --- PROOF ---
  intro int _ s₁ s₂ h₁ h₂ hi
  have hi' : int.contains (s₁ * s₂) := hi
  have hi'' : int.contains (s₂ * s₁) := by rwa [mul_comm] at hi'
  unfold SyntaxTree.funHanTimesFloat
  dsimp only
-- each interval holds its operand where the partner avoids `0`, and lies inside the previous one
  refine ⟨?_, ?_, ?_, ?_⟩
  · by_cases hc : ltStrict zero (prev₂.inf 0) = true ∨ ltStrict (prev₂.sup 0) zero = true
    · rw [if_pos hc]
      exact (SyntaxTree.meet_containsFloat h₁ (SyntaxTree.aux_operand_containsFloat hc hi' h₂)).1
    · rw [if_neg hc]; exact h₁
  · by_cases hc : ltStrict zero (prev₁.inf 0) = true ∨ ltStrict (prev₁.sup 0) zero = true
    · rw [if_pos hc]
      exact (SyntaxTree.meet_containsFloat h₂ (SyntaxTree.aux_operand_containsFloat hc hi'' h₁)).1
    · rw [if_neg hc]; exact h₂
  · by_cases hc : ltStrict zero (prev₂.inf 0) = true ∨ ltStrict (prev₂.sup 0) zero = true
    · rw [if_pos hc]
      exact (SyntaxTree.meet_containsFloat h₁ (SyntaxTree.aux_operand_containsFloat hc hi' h₂)).2
    · rw [if_neg hc]
      exact ⟨le_rfl, le_rfl⟩
  · by_cases hc : ltStrict zero (prev₁.inf 0) = true ∨ ltStrict (prev₁.sup 0) zero = true
    · rw [if_pos hc]
      exact (SyntaxTree.meet_containsFloat h₂ (SyntaxTree.aux_operand_containsFloat hc hi'' h₁)).2
    · rw [if_neg hc]
      exact ⟨le_rfl, le_rfl⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
