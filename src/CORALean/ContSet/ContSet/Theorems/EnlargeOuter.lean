module

public import CORALean.ContSet.ContSet.Operations.Enlarge
public import CORALean.ContSet.ContSet.Theorems.MinusOuter
public import CORALean.ContSet.ContSet.Theorems.TimesOuter

@[expose] public section

/-!
# `enlarge` encloses the scaling about the center

## Inputs
* `s` – set
* `f` – per-coordinate scaling factor

## Hypotheses
* none

## Conclusion
* every scaled point about the center lies in the enlarged set
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      14-October-2026 (Tobias Ladner)


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open ContSet Scalar

variable {𝕋 : Type} [Scalar 𝕋] [ExactScalar 𝕋] {S : ℕ → Type}
variable [∀ n, ContSet (S n) (Vec ℝ n)] [Mtimes (Mat 𝕋) S] {n : ℕ}
variable [∀ n, Plus (S n) (Vec ℝ n)] [∀ n, OfPoint (S n) (Vec ℝ n)]
variable [∀ n, Recenter (S n) (Vec ℝ n)]


-- =======================================  MAIN THEOREM  ======================================= --

/-- Every point `c + f ⊙ (x - c)`, `x` in `S`, `c` its center and `f` read as reals, is in
`enlarge S f`: `minus_outer`, `times_outer` and `plus_outer` in turn. -/
theorem ContSet.enlarge_outer (s : S n) (f : Vec 𝕋 n) :
    (fun x : Vec ℝ n => Recenter.center s + fun i => toReal (f i) * (x i - Recenter.center s i)) ''
      construct s ⊆ construct (ContSet.enlarge s f) := by -- --- PROOF ---
  rintro _ ⟨x, hx, rfl⟩
  have h1 := ContSet.minus_outer s (Recenter.center s) ⟨x, hx, rfl⟩
  have h2 := ContSet.times_outer f (ContSet.minus s (Recenter.center s))
    ⟨x - Recenter.center s, h1, rfl⟩
  exact Plus.plus_outer _ _ ⟨_, h2, Recenter.center s, OfPoint.mem_ofPoint _, add_comm _ _⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
