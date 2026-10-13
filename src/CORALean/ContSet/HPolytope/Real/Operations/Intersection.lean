import CORALean.ContSet.HPolytope.Real.HPolytope

/-!
# `HPolytope.intersection`

CORA's `@polytope/and_`: the constraint lists concatenate, so an intersection
costs nothing and loses nothing. The operation halfspaces are for.

The stacked system of [1, Eq. 36].

## References

* [1] M. Wetzlinger, V. Kotsev, A. Kulmburg and M. Althoff. "Implementation of Polyhedral
      Operations in CORA 2024". In Proc. of the 11th International Workshop on Applied
      Verification for Continuous and Hybrid Systems (ARCH24), EPiC Series in Computing,
      vol. 103, pp. 163-181, 2024.
-/

-- Authors:       Claude Opus 5
-- Written:       01-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =====================================  MAIN DEFINITION  ====================================== --

def HPolytope.intersection (P₁ P₂ : HPolytope α) : HPolytope α where
  m := P₁.m + P₂.m
  A := Fin.append P₁.A P₂.A
  b := Fin.append P₁.b P₂.b
  me := P₁.me + P₂.me
  Ae := Fin.append P₁.Ae P₂.Ae
  be := Fin.append P₁.be P₂.be

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
