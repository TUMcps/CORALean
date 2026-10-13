module

public import CORALean.ContSet.Ellipsoid.Real.Operations.Mtimes

@[expose] public section

/-!
# `Ellipsoid.map`

An ellipsoid lives at `Vec ℝ n` alone — it is described by a Euclidean norm,
which a general module has none of — and there every linear map is a matrix. So
`map` is `mtimes` at that matrix rather than a development of its own, which is
the reverse of the zonotope, where `map` is primary and `mtimes` the instance of
it at `A *ᵥ ·`.
-/

-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n m : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

noncomputable def Ellipsoid.map (f : Vec ℝ n →ₗ[ℝ] Vec ℝ m) (E : Ellipsoid n) : Ellipsoid m :=
  Ellipsoid.mtimes (LinearMap.toMatrix' f) E

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
