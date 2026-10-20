module

public import Mathlib.Data.List.Basic

@[expose] public section

/-!
# What `mapM` in `Option` gives

If `l.mapM f = some L` (no `f a` is `none`), then `L` consists of the values `f a` for `a` in `l`,
and each `a` of `l` has its value in `L`.

## Inputs
* `α` – input type
* `β` – output type
* `f` – partial function

## Hypotheses
* none

## Conclusion
* the output list consists of the values of the function on the inputs
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =======================================  MAIN THEOREM  ======================================= --

theorem mapM_option_spec {α β : Type} (f : α → Option β) :
    ∀ (l : List α) (L : List β), l.mapM f = some L →
      (∀ r ∈ L, ∃ a ∈ l, f a = some r) ∧ (∀ a ∈ l, ∃ r ∈ L, f a = some r) := by -- --- PROOF ---
  intro l
  induction l with
  | nil => intro L h; simp [List.mapM_nil] at h; subst h; simp
  | cons a l ih =>
    intro L h
    simp only [List.mapM_cons] at h
    -- the first value and the rest
    obtain ⟨r, hr, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨L', hL', h⟩ := Option.bind_eq_some_iff.mp h
    obtain rfl : L = r :: L' := by simpa using h.symm
    obtain ⟨ih1, ih2⟩ := ih L' hL'
    refine ⟨fun x hx => ?_, fun x hx => ?_⟩
    · rcases List.mem_cons.mp hx with rfl | hx
      · exact ⟨a, List.mem_cons_self, hr⟩
      · obtain ⟨b, hb, hfb⟩ := ih1 x hx
        exact ⟨b, List.mem_cons_of_mem _ hb, hfb⟩
    · rcases List.mem_cons.mp hx with rfl | hx
      · exact ⟨r, List.mem_cons_self, hr⟩
      · obtain ⟨y, hy, hfy⟩ := ih2 x hx
        exact ⟨y, List.mem_cons_of_mem _ hy, hfy⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
