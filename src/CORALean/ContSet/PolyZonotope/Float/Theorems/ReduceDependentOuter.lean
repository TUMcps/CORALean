import CORALean.ContSet.PolyZonotope.Float.Operations.ReduceDependent
import CORALean.ContSet.PolyZonotope.Float.Theorems.CompactOuter
import CORALean.ContSet.PolyZonotope.Float.Theorems.ReduceGirardDependentOuter

/-!
# `reduceDependent` over-approximates the set

`compact` first, then `reduceGirardDependent` — the tighter rule is sound on the
same line as the bounded one, what separates the two being the order bound and
nothing here.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   05-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- The tighter rule is sound on the same line as the bounded one, which is the
point of `reduceBy_outer` holding at every pair of partitions: what separates
the two is the order bound and nothing here. -/
theorem PolyZonotope.reduceDependent_outer (pZ : PolyZonotope 𝕋 n) (o : ℕ) :
    pZ.construct ⊆ (pZ.reduceDependent o).construct :=
  subset_trans (PolyZonotope.compact_outer pZ)
    (PolyZonotope.reduceGirardDependent_outer pZ.compact o)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
