module

public import CORALean.ContSet.ZonoBundle.Float.Operations.Intersection
public import CORALean.ContSet.SetIntersection.Theorems.IntersectionExact
public import Mathlib.Data.List.OfFn

@[expose] public section

/-!
# `ZonoBundle.intersection` denotes exactly the intersection

Appending the two families intersects what each bundle denoted: the general
`SetIntersection.intersection_exact`, once `List.ofFn_fin_append` reads the appended family
`Fin.append` as the appended lists of members. The members' error boxes ride along
inside their own `construct`, so the argument is the exact layer's unchanged —
this is the one operation here that loses nothing over floats either.

`Instances` is what turns it into the `Intersection (ZonoBundle (Vec 𝕋 n)) (Vec ℝ n)` instance,
whose obligation is only the outer half.
-/

-- Authors:       Claude Opus 5
-- Written:       07-September-2026
-- Last update:   ---
-- Reviewed:      19-October-2026 (Tobias Ladner)


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem ZonoBundle.intersection_exact (zB₁ zB₂ : ZonoBundle (Vec 𝕋 n)) :
    (zB₁.intersection zB₂).construct = zB₁.construct ∩ zB₂.construct := by
  show ContSet.construct (⟨List.ofFn (Fin.append zB₁.Z zB₂.Z)⟩ : SetIntersection _) = _
  rw [List.ofFn_fin_append]
  exact SetIntersection.intersection_exact zB₁.toSetIntersection zB₂.toSetIntersection

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
