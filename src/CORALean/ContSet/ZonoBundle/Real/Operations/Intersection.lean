import CORALean.ContSet.ZonoBundle.Real.ZonoBundle

/-!
# `ZonoBundle.intersection`

CORA's `zonoBundle`/`and`, the whole point of the representation: appending the
two families of zonotopes [1, Sec. III]. `Theorems.AndExact` is why appending denotes the
intersection of what each bundle denoted.

## References

* [1] M. Althoff and B. H. Krogh. "Zonotope Bundles for the Efficient Computation of
      Reachable Sets". In Proc. of the 50th IEEE Conference on Decision and Control and
      European Control Conference (CDC-ECC), pp. 6814-6821, 2011.
-/

-- Authors:       Tobias Ladner
-- Written:       06-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =====================================  MAIN DEFINITION  ====================================== --

def ZonoBundle.intersection (zB₁ zB₂ : ZonoBundle α) : ZonoBundle α where
  k := zB₁.k + zB₂.k
  Z := Fin.append zB₁.Z zB₂.Z

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
