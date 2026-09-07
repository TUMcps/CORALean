import CORALean.ContSet.ZonoBundle.Real.Operations.Map
import CORALean.ContSet.Zonotope.Real.Theorems.MapExact

/-!
# `ZonoBundle.map` is exactly the image, under a bijective map

`Zonotope.map_exact` needs no hypothesis on `f`: one zonotope's coefficients
read through `f` are still its coefficients. A bundle intersects several, and
image only commutes with `⋂ i` one way without more — `f '' ⋂ i, s i ⊆
⋂ i, f '' s i` always holds, the direction that keeps the image the smaller
side. The reverse, which `Set.image_iInter` supplies, needs `f` *bijective*,
not merely injective: `zB.k = 0` already denotes `univ` in `α`, and only a
surjective `f` carries that to `univ` in `β` rather than to `range f`.
-/

-- Authors:       Tobias Ladner
-- Written:       07-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α β : Type} [AddCommGroup α] [Module ℝ α] [AddCommGroup β] [Module ℝ β]


-- =======================================  MAIN THEOREM  ======================================= --

theorem ZonoBundle.map_exact (f : α →ₗ[ℝ] β) (hf : Function.Bijective f) (zB : ZonoBundle α) :
    (zB.map f).construct = f '' zB.construct := by
  simp only [ZonoBundle.construct, ZonoBundle.map, Set.image_iInter hf]
  exact Set.iInter_congr fun i => (Zonotope.map_exact f (zB.Z i)).symm

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
