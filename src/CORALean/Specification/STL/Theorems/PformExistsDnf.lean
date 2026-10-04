import CORALean.Specification.STL.Definitions.Halfspace

/-!
# A predicate over halfspaces has a disjunctive normal form

[1, Sec. 5]: "the logical part `ϱ` can be transformed into disjunctive normal form `ϱ = ⋁ᵢ ⋀ⱼ
(aᵀᵢⱼ x ∼ bᵢⱼ)` with `∼ ∈ {<, ≤}`". So has its negation: `¬(f x < b)` is `(-f) x ≤ -b`, `¬(f x ≤
b)` is `(-f) x < -b`, `>` and `≥` are those with the sign flipped, and `¬(ϱ₁ ∨ ϱ₂)` distributes
over the two normal forms.

## References

* [1] H. Roehm, J. Oehlerking, T. Heinz and M. Althoff. "STL Model Checking of Continuous and
      Hybrid Systems". ATVA, LNCS 9938, pp. 412-427, 2016.
-/

-- Authors:       Tobias Ladner
-- Written:       04-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =======================================  MAIN THEOREM  ======================================= --

theorem Pform.exists_dnf (ϱ : Pform α) (h : ϱ.IsHalfspaceForm) :
    (∃ dnf : List (List (STL.Halfspace α)), ∀ x, ϱ.Sat x ↔ STL.Dnf.Holds dnf x) ∧
      ∃ dnf : List (List (STL.Halfspace α)), ∀ x, ¬ ϱ.Sat x ↔
        STL.Dnf.Holds dnf x := by -- --- PROOF ---
  induction ϱ with
  | atom p =>
    obtain ⟨f, b, r, rfl⟩ := h
    -- one halfspace for the atom and one for its negation, whichever the relation
    have one : ∀ (g : α →ₗ[ℝ] ℝ) (c : ℝ) (s : Bool) (P : α → Prop),
        (∀ x, P x ↔ (if s then g x < c else g x ≤ c)) →
          ∃ dnf : List (List (STL.Halfspace α)), ∀ x, P x ↔ STL.Dnf.Holds dnf x := fun g c s P hP =>
      ⟨[[⟨g, c, s⟩]], fun x => by simp [STL.Dnf.Holds, STL.Halfspace.Holds, hP x]⟩
    cases r
    · refine ⟨one f b true _ fun x => by simp [STL.Rel.Holds, Pform.Sat],
        one (-f) (-b) false _ fun x => by simp [STL.Rel.Holds, Pform.Sat]⟩
    · refine ⟨one f b false _ fun x => by simp [STL.Rel.Holds, Pform.Sat],
        one (-f) (-b) true _ fun x => by simp [STL.Rel.Holds, Pform.Sat]⟩
    · refine ⟨one (-f) (-b) true _ fun x => by simp [STL.Rel.Holds, Pform.Sat],
        one f b false _ fun x => by simp [STL.Rel.Holds, Pform.Sat]⟩
    · refine ⟨one (-f) (-b) false _ fun x => by simp [STL.Rel.Holds, Pform.Sat],
        one f b true _ fun x => by simp [STL.Rel.Holds, Pform.Sat]⟩
  | not ϱ ih =>
    obtain ⟨⟨d, hd⟩, ⟨d', hd'⟩⟩ := ih h
    exact ⟨⟨d', hd'⟩, ⟨d, fun x => by simpa [Pform.Sat] using hd x⟩⟩
  | or ϱ₁ ϱ₂ ih₁ ih₂ =>
    -- the normal forms of the two operands
    obtain ⟨⟨d₁, hd₁⟩, ⟨d₁', hd₁'⟩⟩ := ih₁ h.1
    obtain ⟨⟨d₂, hd₂⟩, ⟨d₂', hd₂'⟩⟩ := ih₂ h.2
    refine ⟨⟨d₁ ++ d₂, fun x => ?_⟩, ⟨d₁'.flatMap fun c₁ => d₂'.map fun c₂ => c₁ ++ c₂,
      fun x => ?_⟩⟩
    · -- a disjunction is the two lists joined
      simp only [Pform.Sat, hd₁, hd₂, STL.Dnf.Holds, List.mem_append]
      constructor
      · rintro (⟨cl, hcl, h'⟩ | ⟨cl, hcl, h'⟩)
        · exact ⟨cl, Or.inl hcl, h'⟩
        · exact ⟨cl, Or.inr hcl, h'⟩
      · rintro ⟨cl, hcl | hcl, h'⟩
        · exact Or.inl ⟨cl, hcl, h'⟩
        · exact Or.inr ⟨cl, hcl, h'⟩
    · -- `¬(ϱ₁ ∨ ϱ₂)` is the conjunction, which distributes over the two disjunctions
      simp only [Pform.Sat, not_or, hd₁', hd₂', STL.Dnf.Holds, List.mem_flatMap, List.mem_map]
      constructor
      · rintro ⟨⟨c₁, h₁, h₁'⟩, ⟨c₂, h₂, h₂'⟩⟩
        refine ⟨c₁ ++ c₂, ⟨c₁, h₁, c₂, h₂, rfl⟩, fun hh hm => ?_⟩
        rcases List.mem_append.1 hm with hm | hm
        · exact h₁' hh hm
        · exact h₂' hh hm
      · rintro ⟨cl, ⟨c₁, h₁, c₂, h₂, rfl⟩, h'⟩
        exact ⟨⟨c₁, h₁, fun hh hm => h' hh (List.mem_append.2 (Or.inl hm))⟩,
          ⟨c₂, h₂, fun hh hm => h' hh (List.mem_append.2 (Or.inr hm))⟩⟩


end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
