module

public import CORALean.ContSet.Interval.Real.Operations.Basic

@[expose] public section

/-!
# A point of an appended box

A point lies in `I₁.append I₂` iff its first block lies in `I₁` and its second in `I₂`: the box of
a product is the product of the boxes, with no hypothesis.

## Inputs
* `I₁` – first interval box
* `I₂` – second interval box
* `x` – point of the concatenated space

## Hypotheses
* none

## Conclusion
* `x` lies in the appended box iff both parts lie in their boxes
-/

-- Authors:       Claude Opus 5.5
-- Written:       19-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n₁ n₂ : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- A point of the appended box is one whose two blocks lie in the two boxes. -/
theorem Interval.mem_append_iff (I₁ : Interval (Vec ℝ n₁)) (I₂ : Interval (Vec ℝ n₂))
    (x : Vec ℝ (n₁ + n₂)) : -- --- CONCL ---
    x ∈ (I₁.append I₂).construct
      ↔ (fun k => x (Fin.castAdd n₂ k)) ∈ I₁.construct
        ∧ (fun k => x (Fin.natAdd n₁ k)) ∈ I₂.construct := by -- --- PROOF ---
  constructor
  · intro hx
    refine ⟨fun k => ?_, fun k => ?_⟩
    · have h : Fin.append I₁.inf I₂.inf (Fin.castAdd n₂ k) ≤ x (Fin.castAdd n₂ k)
          ∧ x (Fin.castAdd n₂ k) ≤ Fin.append I₁.sup I₂.sup (Fin.castAdd n₂ k) := hx _
      simp only [Fin.append_left] at h
      exact h
    · have h : Fin.append I₁.inf I₂.inf (Fin.natAdd n₁ k) ≤ x (Fin.natAdd n₁ k)
          ∧ x (Fin.natAdd n₁ k) ≤ Fin.append I₁.sup I₂.sup (Fin.natAdd n₁ k) := hx _
      simp only [Fin.append_right] at h
      exact h
  · rintro ⟨h₁, h₂⟩ k
    show Fin.append I₁.inf I₂.inf k ≤ x k ∧ x k ≤ Fin.append I₁.sup I₂.sup k
    refine Fin.addCases (fun k => ?_) (fun k => ?_) k
    · simp only [Fin.append_left]
      exact h₁ k
    · simp only [Fin.append_right]
      exact h₂ k

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
