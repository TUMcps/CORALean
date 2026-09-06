import CORALean.ContSet.PolyZonotope.Real.Operations.Map
import CORALean.ContSet.PolyZonotope.Real.Operations.Point

/-!
# `PolyZonotope.map` moves the point by the map itself

`map` leaves the exponent matrix and the factor count alone, so one factor
vector names the same monomials before and after and the point commutes with
`f`.

Stated over `point` rather than over `construct`, which is what `map_exact`
already says and is not this: a recursion that pairs sets at *shared* factors —
a chain of graph convolutions, say — argues one factor vector at a time and
never reaches the independent block. `bilin_point` sits beside `bilin_exact` for
the same reason, and the two compose only if `map` has both as well.
-/

-- Authors:       Tobias Ladner
-- Written:       06-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α β : Type} [AddCommGroup α] [Module ℝ α] [AddCommGroup β] [Module ℝ β]


-- =======================================  MAIN THEOREM  ======================================= --

/-- `map`'s point is `f` at the point: the monomials are scalars, so only the
centre and the generators move. -/
theorem PolyZonotope.map_point (f : α →ₗ[ℝ] β) (S : PolyZonotope α) (a : Fin S.p → ℝ) :
    (S.map f).point a = f (S.point a) := by -- --- PROOF ---
  show f S.c + ∑ i, PolyZonotope.monomial S.E a i • f (S.G i)
      = f (S.c + ∑ i, PolyZonotope.monomial S.E a i • S.G i)
  -- linearity across the sum, then across each scaling
  rw [map_add, map_sum]
  refine congrArg (f S.c + ·) (Finset.sum_congr rfl fun i _ => ?_)
  exact (map_smul f _ (S.G i)).symm

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
