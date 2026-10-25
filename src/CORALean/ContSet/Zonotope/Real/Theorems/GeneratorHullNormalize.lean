module

public import CORALean.ContSet.Zonotope.Real.Zonotope
public import CORALean.ContSet.Zonotope.Real.Theorems.GeneratorHullSymmetric
public import CORALean.ContSet.Zonotope.Real.Theorems.GeneratorHullEqConstruct
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

@[expose] public section

/-!
# Symmetrizing the generators does not change the zonotope

[1, Eq. 11]: replacing the generators `g₁, …, g_M` by the `2M` generators `½g₁, …, ½g_M,
−½g₁, …, −½g_M` leaves the zonotope unchanged "up to a shift": with the shift moved to the
center `s + ½ ∑ gᵢ`, `Z(s; g)` is `Z(s + ½ ∑ gᵢ; ½g, −½g)`. Both are the zonotope of that
center and generators `gᵢ/2` ([1, Lemma 3.1] and `generatorHull_eq_construct`).

## Inputs
* `s` – starting point
* `M` – generator count
* `g` – generators

## Hypotheses
* none

## Conclusion
* the hull equals the symmetric normalized form

## References

* [1] M. Černý. "Goffin's algorithm for zonotopes". Kybernetika, 2012.
-/

-- Authors:       Claude Opus 5.5
-- Written:       08-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Eq. 11]: `Z(s; g) = Z(s + ½ ∑ gᵢ; ½g, −½g)`. -/
theorem Zonotope.generatorHull_normalize (s : Vec ℝ n) (M : ℕ) (g : Fin M → Vec ℝ n) :
    Zonotope.generatorHull s M g
      = Zonotope.generatorHull (s + (1 / 2 : ℝ) • ∑ i, g i) (M + M)
          (Fin.append (fun i => (1 / 2 : ℝ) • g i) (-fun i => (1 / 2 : ℝ) • g i)) := by
  rw [Zonotope.generatorHull_symmetric, Zonotope.generatorHull_eq_construct]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
