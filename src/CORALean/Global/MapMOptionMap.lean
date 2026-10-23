module

public import Mathlib.Data.List.Basic

@[expose] public section

/-!
# `mapM` in `Option` commutes with a map of its values

Mapping every value of a `mapM` in `Option` is the `mapM` of the mapped function: a `none` on one
side is a `none` on the other.

## Inputs
* `α` – input type
* `β` – output type
* `γ` – mapped output type
* `f` – partial function
* `g` – map of the outputs

## Hypotheses
* none

## Conclusion
* the mapped `mapM` is the `mapM` of the mapped function
-/

-- Authors:       Claude Opus 5.5
-- Written:       23-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =======================================  MAIN THEOREM  ======================================= --

theorem mapM_option_map {α β γ : Type} (f : α → Option β) (g : β → γ) :
    ∀ l : List α, (l.mapM f).map (List.map g) = l.mapM fun a => (f a).map g
  | [] => rfl
  | a :: l => by
    simp only [List.mapM_cons]
    cases f a with
    | none => rfl
    | some b =>
      simp only [Option.map_some, ← mapM_option_map f g l]
      cases l.mapM f <;> rfl

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
