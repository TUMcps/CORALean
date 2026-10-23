module

public import Mathlib.Data.List.Basic

@[expose] public section

/-!
# A fold in `Option` commutes with a map of its states

If one step of `f` followed by `g` is one step of `f'` from the mapped state on the mapped element,
then the whole fold of `f`, mapped by `g`, is the fold of `f'` over the mapped list from the mapped
start: a failing step fails on both sides.

## Inputs
* `α` – state type
* `β` – element type
* `γ` – mapped state type
* `δ` – mapped element type
* `f` – step
* `f'` – mapped step
* `g` – map of the states
* `h` – map of the elements

## Hypotheses
* `hf` – one step commutes with the maps

## Conclusion
* the fold commutes with the maps
-/

-- Authors:       Claude Opus 5.5
-- Written:       23-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =======================================  MAIN THEOREM  ======================================= --

theorem foldlM_option_map {α β γ δ : Type} (f : α → β → Option α) (f' : γ → δ → Option γ)
    (g : α → γ) (h : β → δ) (hf : ∀ x a, (f x a).map g = f' (g x) (h a)) :
    ∀ (l : List β) (x : α), (l.foldlM f x).map g = (l.map h).foldlM f' (g x)
  | [], _ => rfl
  | a :: l, x => by
    simp only [List.foldlM_cons, List.map_cons]
    rw [← hf]
    cases f x a with
    | none => rfl
    | some y => exact foldlM_option_map f f' g h hf l y

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
