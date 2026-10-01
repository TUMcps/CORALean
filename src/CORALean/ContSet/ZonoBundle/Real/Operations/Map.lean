import CORALean.ContSet.Zonotope.Real.Operations.Map
import CORALean.ContSet.ZonoBundle.Real.ZonoBundle

/-!
# `ZonoBundle.map`

A linear map applied to every zonotope in the family [1, Prop. 1], the count `k` untouched:
`construct` reads only the family, so moving each member is all a bundle needs
to move.

## References

* [1] M. Althoff and B. H. Krogh. "Zonotope Bundles for the Efficient Computation of
      Reachable Sets". In Proc. of the 50th IEEE Conference on Decision and Control and
      European Control Conference (CDC-ECC), pp. 6814-6821, 2011.
-/

-- Authors:       Tobias Ladner
-- Written:       07-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α β : Type} [AddCommGroup α] [Module ℝ α] [AddCommGroup β] [Module ℝ β]


-- =====================================  MAIN DEFINITION  ====================================== --

def ZonoBundle.map (f : α →ₗ[ℝ] β) (zB : ZonoBundle α) : ZonoBundle β where
  k := zB.k
  Z := fun i => Zonotope.map f (zB.Z i)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
