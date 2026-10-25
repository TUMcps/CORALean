module

public import CORALean.ContSet.Zonotope.Real.Zonotope
public import CORALean.ContSet.Zonotope.Real.Theorems.GeneratorHullEq
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

@[expose] public section

/-!
# Changing the shift translates the zonotope

[1, Eq. 10]: changing the shift `s` to `s + v` translates `Z(s; g₁, …, g_m)` by `v`, so a
zonotope is easily centered at 0 by taking `v = −(s + ½ ∑ gᵢ)`. Both are the cube's
image, and the shift is the additive constant.

## Inputs
* `s` – starting point
* `v` – translation
* `m` – generator count
* `g` – generators

## Hypotheses
* none

## Conclusion
* translating the start translates the hull

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

/-- [1, Eq. 10]: `Z(s + v; g) = Z(s; g) + v`. -/
theorem Zonotope.generatorHull_translate (s v : Vec ℝ n) (m : ℕ)
    (g : Fin m → Vec ℝ n) : -- --- CONCL ---
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
