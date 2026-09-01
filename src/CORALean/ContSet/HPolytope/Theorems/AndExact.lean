import CORALean.ContSet.HPolytope.Operations.And

/-!
# `HPolytope.and` is exactly the intersection

Both constraint lists have to hold, which is what concatenating them says.
`Fin.addCases` splits the quantifier the same way `Fin.append` splits the list.
-/

-- Authors:       Tobias Ladner
-- Written:       01-September-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]

theorem HPolytope.mem_and_iff {P₁ P₂ : HPolytope α} {x : α} :
    x ∈ (P₁.and P₂).construct ↔ x ∈ P₁.construct ∧ x ∈ P₂.construct := by
  constructor
  · rintro ⟨hle, heq⟩
    refine ⟨⟨fun i => ?_, fun i => ?_⟩, ⟨fun i => ?_, fun i => ?_⟩⟩
    · have h := hle (Fin.castAdd P₂.m i)
      simp only [HPolytope.and, Fin.append_left] at h
      exact h
    · have h := heq (Fin.castAdd P₂.me i)
      simp only [HPolytope.and, Fin.append_left] at h
      exact h
    · have h := hle (Fin.natAdd P₁.m i)
      simp only [HPolytope.and, Fin.append_right] at h
      exact h
    · have h := heq (Fin.natAdd P₁.me i)
      simp only [HPolytope.and, Fin.append_right] at h
      exact h
  · rintro ⟨⟨h₁, he₁⟩, h₂, he₂⟩
    constructor
    · refine Fin.addCases (fun i => ?_) fun i => ?_
      · simp only [HPolytope.and, Fin.append_left]; exact h₁ i
      · simp only [HPolytope.and, Fin.append_right]; exact h₂ i
    · refine Fin.addCases (fun i => ?_) fun i => ?_
      · simp only [HPolytope.and, Fin.append_left]; exact he₁ i
      · simp only [HPolytope.and, Fin.append_right]; exact he₂ i

theorem HPolytope.and_exact (P₁ P₂ : HPolytope α) :
    P₁.construct ∩ P₂.construct = (P₁.and P₂).construct :=
  Set.ext fun _ => HPolytope.mem_and_iff.symm

end CORALean.Real
