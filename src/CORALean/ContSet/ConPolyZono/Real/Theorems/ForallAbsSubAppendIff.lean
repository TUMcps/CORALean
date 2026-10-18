module

public import Mathlib.Data.Real.Basic
public import Mathlib.Data.Fin.Tuple.Basic

@[expose] public section

/-!
# Rows within their slack, two blocks side by side

Two blocks of rows side by side are each within their slack exactly when both blocks are: the
form the slack of a constraint system stacked from two takes.
-/

-- Authors:       Claude Opus 5.5
-- Written:       18-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =======================================  MAIN THEOREM  ======================================= --

/-- Two blocks of rows side by side are each within their slack exactly when both blocks are. -/
theorem ConPolyZono.forall_abs_sub_append_iff {m₁ m₂ : ℕ} (u₁ c₁ s₁ : Fin m₁ → ℝ)
    (u₂ c₂ s₂ : Fin m₂ → ℝ) :
    (∀ i, |Fin.append u₁ u₂ i - Fin.append c₁ c₂ i| ≤ |Fin.append s₁ s₂ i|)
      ↔ (∀ i, |u₁ i - c₁ i| ≤ |s₁ i|) ∧ ∀ i, |u₂ i - c₂ i| ≤ |s₂ i| :=
  ⟨fun h => ⟨fun i => by simpa using h (Fin.castAdd m₂ i),
      fun i => by simpa using h (Fin.natAdd m₁ i)⟩,
    fun ⟨h₁, h₂⟩ => Fin.addCases (fun i => by simpa using h₁ i) fun i => by simpa using h₂ i⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
