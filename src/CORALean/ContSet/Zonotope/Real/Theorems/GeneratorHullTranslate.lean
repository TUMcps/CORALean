import CORALean.ContSet.Zonotope.Real.Zonotope
import CORALean.ContSet.Zonotope.Real.Theorems.GeneratorHullEq
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Changing the shift translates the zonotope

[1, Eq. 10]: changing the shift `s` to `s + v` translates `Z(s; g₁, …, g_m)` by `v`, so a
zonotope "can easily be centred at 0" by taking `v = −(s + ½ ∑ gᵢ)`. Both are the cube's
image, and the shift is the additive constant.

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

/-- [1, Eq. 10]: `Z(s + v; g) = Z(s; g) + v`. -/
theorem Zonotope.generatorHull_translate (s v : Vec ℝ n) (m : ℕ) (g : Fin m → Vec ℝ n) :
    Zonotope.generatorHull (s + v) m g
      = (fun y => y + v) '' Zonotope.generatorHull s m g := by -- --- PROOF ---
  rw [Zonotope.generatorHull_eq, Zonotope.generatorHull_eq]
  ext y
  simp only [Set.mem_setOf_eq, Set.mem_image]
  constructor
  · rintro ⟨α, hα, rfl⟩
    exact ⟨s + ∑ i, α i • g i, ⟨α, hα, rfl⟩, by abel⟩
  · rintro ⟨_, ⟨α, hα, rfl⟩, rfl⟩
    exact ⟨α, hα, by abel⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
