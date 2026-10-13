import CORALean.ContSet.Zonotope.Real.Zonotope
import CORALean.ContSet.Zonotope.Real.Theorems.GeneratorHullSymmetric
import CORALean.ContSet.Zonotope.Real.Theorems.GeneratorHullEqConstruct
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Symmetrizing the generators does not change the zonotope

[1, Eq. 11]: replacing the generators `g₁, …, g_M` by the `2M` generators `½g₁, …, ½g_M,
−½g₁, …, −½g_M` leaves the zonotope unchanged "up to a shift": with the shift moved to the
centre `s + ½ ∑ gᵢ`, `Z(s; g)` is `Z(s + ½ ∑ gᵢ; ½g, −½g)`. Both are the zonotope of that
centre and generators `gᵢ/2` ([1, Lemma 3.1] and `generatorHull_eq_construct`).

## References

* [1] M. Černý. "Goffin's algorithm for zonotopes". Kybernetika, 48(5):890-906, 2012.
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
