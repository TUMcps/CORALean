module

public import CORALean.ContSet.Zonotope.Real.Zonotope
public import CORALean.ContSet.Zonotope.Real.Definitions.SegmentSum
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

@[expose] public section

/-!
# A zonotope as the evolution of a point under its generators

[1, Def. 1.3]: the zonotope `Z(s; g₁, …, g_m)` is `{s} ⊕ g₁ ⊕ ⋯ ⊕ g_m`, the shift `s` swept
along the generators one after another, left to right. It is defined by recursion on the
number `m` of generators, the last generator last (`Fin.init` drops it); `generatorHull_eq`
and `generatorHull_symmetric` are its parametrizations.

## Inputs
* `s` – starting point

## Output
* set swept by adding the generators in order

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


-- =====================================  MAIN DEFINITION  ====================================== --

/-- [1, Def. 1.3]: `{s} ⊕ g₁ ⊕ ⋯ ⊕ g_m`, the generators applied in order. -/
def Zonotope.generatorHull (s : Vec ℝ n) : (m : ℕ) → (Fin m → Vec ℝ n) → Set (Vec ℝ n)
  | 0, _ => {s}
  | m + 1, g => Zonotope.segmentSum (Zonotope.generatorHull s m (Fin.init g)) (g (Fin.last m))

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
