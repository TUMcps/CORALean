module

public import CORALean.ContSet.ConZonotope.Float.Operations.MinkDiffV
public import CORALean.ContSet.ConZonotope.Float.Theorems.IntersectionOuter
public import CORALean.ContSet.Zonotope.Float.Theorems.PlusOuter
public import CORALean.ContSet.Zonotope.Float.Theorems.ConstructPoint
public import CORALean.ContSet.VPolytope.Real.Theorems.VertexMem
public import CORALean.ContSet.Conversion.Float.Operations.Basic
public import CORALean.ContSet.Conversion.Real.Operations.Zonotope_to_ConZonotope
public import CORALean.ContSet.Conversion.Float.Theorems.ZonotopeConZonotopeContains

@[expose] public section

/-!
# The float `minkDiffV` encloses the Minkowski difference

Every point `x` of `Z ⊖ ⟨v⟩_V` has `x + vᵢ ∈ Z` for each vertex, so `x` lies in `Z + {−vᵢ}`,
which the float sum encloses (`plus_outer`), and in every intersection of those
(`intersection_outer`). Outer only, where the exact layer's `minkDiffV_exact` is an equality.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Pointwise FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- A point of the start and of every intersected set is a point of the fold. -/
theorem ConZonotope.aux_mem_foldl_intersection {x : Vec ℝ n} :
    ∀ {m : ℕ} (g : Fin m → ConZonotope 𝕋 (Vec 𝕋 n)) (cZ : ConZonotope 𝕋 (Vec 𝕋 n)), x ∈
    cZ.construct →
      (∀ i, x ∈ (g i).construct) →
        x ∈ (Fin.foldl m (fun cZ i => cZ.intersection (g i)) cZ).construct
  | 0, _, _, h, _ => by simpa using h
  | m + 1, g, cZ, h, hg => by
    rw [Fin.foldl_succ]
    exact ConZonotope.aux_mem_foldl_intersection (fun i => g i.succ) _
      (ConZonotope.intersection_outer cZ (g 0) ⟨h, hg 0⟩) fun i => hg i.succ


-- =======================================  MAIN THEOREM  ======================================= --

theorem ConZonotope.minkDiffV_outer {k : ℕ} (Z : Zonotope (Vec 𝕋 n)) (v : Fin (k + 1) → Vec 𝕋 n) :
    minkowskiDiff Z.construct
        (⟨k + 1, fun i => toRealVec (v i)⟩ : Real.VPolytope (Vec ℝ n)).construct
      ⊆ (ConZonotope.minkDiffV Z v).construct := by -- --- PROOF ---
  intro x hx
  -- each translate holds `x`: `x = (x + vᵢ) + (−vᵢ)`
  have hs : ∀ i, x ∈ (Z.plus (Zonotope.point fun r => neg (v i r))).conZonotope.construct := by
    intro i
    have hv : x + toRealVec (v i) ∈ Z.construct :=
      hx _ (Real.VPolytope.vertex_mem (⟨k + 1, fun i => toRealVec (v i)⟩ : Real.VPolytope _) i)
    refine Zonotope.conZonotope_contains _ (Zonotope.plus_outer _ _ ?_)
    rw [Zonotope.construct_point]
    refine ⟨_, hv, _, rfl, ?_⟩
    funext r
    simp [toRealVec, toReal_neg]
  exact ConZonotope.aux_mem_foldl_intersection _ _ (hs 0) fun i => hs i.succ

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
