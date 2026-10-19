module

public import CORALean.ContSet.Interval.Real.Operations.Intersection
public import CORALean.ContSet.Interval.Real.Operations.Rdivide
public import CORALean.ContSet.Interval.Real.Operations.Times
public import CORALean.ContSet.Interval.Real.Theorems.RdivideExact
public import CORALean.Specification.SyntaxTree.Definitions.Basic
public import CORALean.Specification.SyntaxTree.Definitions.BinarySound
public import CORALean.Specification.SyntaxTree.Definitions.DomWithin
public import CORALean.Specification.SyntaxTree.Operations.Basic
public import CORALean.Specification.SyntaxTree.SyntaxTree

@[expose] public section

/-!
# `aux_times_` is sound

`aux_times_` keeps every solution of `x₁ x₂ ∈ int`: an operand whose interval contains `0` is left
alone, the other is met with the quotient, exactly (`Interval.rdivide_exact`).
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {n : ℕ} {B : Real.Interval (Vec ℝ n)} {t : SyntaxTree n}


-- =======================================  MAIN THEOREM  ======================================= --

/-- One operand of `aux_times_` keeps `a`, and lies inside its interval. -/
private theorem SyntaxTree.funHanTimes_operand {int prev other : Dom} {a b : ℝ} (hb : Dom.contains
    prev b)
    (ha : Dom.contains other a) (hi : Dom.contains int (a * b)) : -- --- CONCL ---
    Dom.contains (if prev.inf 0 ≤ 0 ∧ 0 ≤ prev.sup 0 then other
      else Real.Interval.intersection other (Real.Interval.rdivide int prev)) a ∧
    Dom.within (if prev.inf 0 ≤ 0 ∧ 0 ≤ prev.sup 0 then other
      else Real.Interval.intersection other (Real.Interval.rdivide int prev))
        other := by -- --- PROOF ---
  split_ifs with h
  · exact ⟨ha, le_rfl, le_rfl⟩
  · -- the denominator keeps its sign, so the quotient is exact
    have h0 : ∀ i : Fin 1, 0 < prev.inf i ∨ prev.sup i < 0 := fun i => by
      obtain rfl : i = 0 := Subsingleton.elim i 0
      rcases not_and_or.1 h with h1 | h1
      · exact Or.inl (not_le.1 h1)
      · exact Or.inr (not_le.1 h1)
    have hI : int.IsNonempty := fun i => by
      obtain rfl : i = 0 := Subsingleton.elim i 0
      exact hi.1.trans hi.2
    have hJ : prev.IsNonempty := fun i => by
      obtain rfl : i = 0 := Subsingleton.elim i 0
      exact hb.1.trans hb.2
    -- the fact `b ≠ 0`
    have hb0 : b ≠ 0 := by
      rcases h0 0 with h1 | h1
      · exact (h1.trans_le hb.1).ne'
      · exact (hb.2.trans_lt h1).ne
    have hx : (fun _ => a * b : Vec ℝ 1) ∈ int.construct := by
      intro i; obtain rfl : i = 0 := Subsingleton.elim i 0; exact hi
    have hy : (fun _ => b : Vec ℝ 1) ∈ prev.construct := by
      intro i; obtain rfl : i = 0 := Subsingleton.elim i 0; exact hb
    have hq : (fun i => (fun _ => a * b : Vec ℝ 1) i / (fun _ => b : Vec ℝ 1) i : Vec ℝ 1) ∈
        (Real.Interval.rdivide int prev).construct := by
      rw [Real.Interval.rdivide_exact hI hJ h0]; exact ⟨_, hx, _, hy, rfl⟩
    have hq0 := hq 0
    -- the fact `Dom.contains (Real.Interval.rdivide int prev) a`
    have hqa : Dom.contains (Real.Interval.rdivide int prev) a := by
      have e : a * b / b = a := mul_div_cancel_right₀ a hb0
      simp only [e] at hq0
      exact hq0
    simp only [Dom.contains, Dom.within, Real.Interval.intersection] at ha hqa ⊢
    exact ⟨⟨max_le ha.1 hqa.1, le_min ha.2 hqa.2⟩, le_max_left _ _, min_le_left _ _⟩

/-- `aux_times_` is sound for `*`. -/
theorem SyntaxTree.times_sound (prev₁ prev₂ : Dom) :
    BinarySound Binary.times.fn prev₁ prev₂ (Real.Interval.times prev₁ prev₂)
      funHanTimes := by -- --- PROOF ---
  intro int _ s₁ s₂ h₁ h₂ hi
  have a := funHanTimes_operand (int := int) (prev := prev₂) (other := prev₁) h₂ h₁ hi
  have b := funHanTimes_operand (int := int) (prev := prev₁) (other := prev₂) h₁ h₂
    (by rwa [mul_comm])
  exact ⟨a.1, b.1, a.2, b.2⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
