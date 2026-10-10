import CORALean.ContSet.ZonoBundle.Float.ZonoBundle
import CORALean.ContSet.Zonotope.Float.Theorems.IsClosed

/-!
# A nonempty float zonotope bundle is compact

`k = 0` denotes `univ`, not compact in a nontrivial space, so this needs
`0 < zB.k`, exactly as over ℝ: the bundle is then a closed subset of the one
compact member it names, and closed because every member is — each member's
error box included, that box being part of what the member denotes.
-/

-- Authors:       Tobias Ladner
-- Written:       07-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem ZonoBundle.isCompact_construct {zB : ZonoBundle 𝕋 n} (h : 0 < zB.k) :
    IsCompact zB.construct := by
  set i₀ : Fin zB.k := ⟨0, h⟩
  refine IsCompact.of_isClosed_subset (Zonotope.isCompact_construct (zB.Z i₀)) ?_
    (Set.iInter_subset _ i₀)
  exact isClosed_iInter fun i => Zonotope.isClosed_construct (zB.Z i)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
