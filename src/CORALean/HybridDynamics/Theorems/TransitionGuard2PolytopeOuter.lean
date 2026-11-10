module

public import CORALean.HybridDynamics.Operations.TransitionGuard2Polytope

@[expose] public section

/-!
# `Transition.guard2polytope` with an outer conversion

An outer conversion (`⊆`) gives a guard that contains the old one, so every jump of the old
transition is a jump of the new one.

## Inputs
* `conv` – guard conversion
* `e` – transition

## Hypotheses
* `h` – the conversion encloses the guard

## Conclusion
* the converted guard contains the old guard
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open ContSetLike

variable {G P : ℕ → Type} [∀ n, ContSetLike (G n) (Vec ℝ n)] [∀ n, ContSetLike (P n) (Vec ℝ n)]
  {L : Type} {𝕋 : Type} {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- An outer conversion gives an outer guard: the old guard lies inside the new one. -/
theorem Transition.guard2polytope_outer (conv : G n → P n)
    (h : ∀ g, toSet g ⊆ toSet (conv g)) (e : Transition G L 𝕋 n) :
    toSet e.guard ⊆ toSet (e.guard2polytope conv).guard :=
  h e.guard

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
