module

public import CORALean.Specification.AtomicProposition.Theorems.HoldsOfCanBeFalseEqFalse
public import CORALean.Specification.AtomicProposition.Theorems.NotHoldsOfCanBeTrueEqFalse
public import CORALean.Specification.OnlineAnalyzerNode.Operations.ApValue

@[expose] public section

/-!
# The value of an atomic proposition on a set

`apValue` is `True` only if every point of the set satisfies the proposition and `False` only if
none does (the Kleene reading of a set of states); it is undefined only if the proposition can be
neither true nor false, which a nonempty set never does.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open ContSet

variable {𝕋 : Type} [Scalar 𝕋] [ExactScalar 𝕋] {S : ℕ → Type} {d : ℕ}
  [∀ k, ContSet (S k) (Vec ℝ k)] [Mtimes (Mat 𝕋) S] [∀ k, Contains (S k) (S k)]
  [∀ k, IsDisjoint (S k) (S k)]


-- =======================================  MAIN THEOREM  ======================================= --

theorem OnlineAnalyzerNode.apValue_spec (ap : AtomicProposition S d) (set : S d)
    (loc : ℕ) : -- --- CONCL ---
    (OnlineAnalyzerNode.apValue (𝕋 := 𝕋) ap set loc = some .tt →
      ∀ x ∈ construct set, ap.Holds x loc) ∧
    (OnlineAnalyzerNode.apValue (𝕋 := 𝕋) ap set loc = some .ff →
      ∀ x ∈ construct set, ¬ ap.Holds x loc) ∧
    ((∃ x, x ∈ construct set) →
      OnlineAnalyzerNode.apValue (𝕋 := 𝕋) ap set loc ≠ none) := by -- --- PROOF ---
  unfold OnlineAnalyzerNode.apValue
  refine ⟨fun h x hx => ?_, fun h x hx => ?_, fun ⟨x, hx⟩ h => ?_⟩
  · -- true: it cannot be false
    cases hf : ap.canBeFalse (𝕋 := 𝕋) set loc <;> cases ht : ap.canBeTrue (𝕋 := 𝕋) set loc <;>
      simp [hf, ht] at h
    exact AtomicProposition.holds_of_canBeFalse_eq_false (𝕋 := 𝕋) ap set loc hf hx
  · -- false: it cannot be true
    cases hf : ap.canBeFalse (𝕋 := 𝕋) set loc <;> cases ht : ap.canBeTrue (𝕋 := 𝕋) set loc <;>
      simp [hf, ht] at h
    exact AtomicProposition.not_holds_of_canBeTrue_eq_false (𝕋 := 𝕋) ap set loc ht hx
  · -- a point of the set either satisfies the proposition or does not
    by_cases hh : ap.Holds x loc
    · have := AtomicProposition.canBeTrue_sound (𝕋 := 𝕋) ap set loc hx hh
      cases hf : ap.canBeFalse (𝕋 := 𝕋) set loc <;> simp [this, hf] at h
    · have := AtomicProposition.canBeFalse_sound (𝕋 := 𝕋) ap set loc hx hh
      cases ht : ap.canBeTrue (𝕋 := 𝕋) set loc <;> simp [this, ht] at h

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
