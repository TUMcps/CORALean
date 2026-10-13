import CORALean.ContSet.ZonoBundle.Float.ZonoBundle
import CORALean.ContSet.Zonotope.Float.Operations.Reindex

/-!
# `ZonoBundle.reindex`

The relabelling applied to every member, the count `k` untouched. Nothing
rounds — a permutation moves stored floats without arithmetic — so each error
box is carried across rather than grown, exactly as `Zonotope.reindex` does.

The exact layer reaches this through `ZonoBundle.map` at `reindexLin e`; there
is no `map` over floats, a general linear map having no float matrix to be
applied by, so `reindex` is written out here instead.
-/

-- Authors:       Tobias Ladner
-- Written:       07-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] {n m : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def ZonoBundle.reindex (e : Fin m ≃ Fin n) (zB : ZonoBundle (Vec 𝕋 n)) : ZonoBundle (Vec 𝕋 m) where
  k := zB.k
  Z := fun i => Zonotope.reindex e (zB.Z i)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
