module

public import CORALean.ContSet.ZonoBundle.Float.Theorems.ConstructEqIInter
public import CORALean.ContSet.ZonoBundle.Float.Operations.IsFullDim
public import CORALean.ContSet.Zonotope.Float.Operations.InteriorPoint
public import CORALean.ContSet.Zonotope.Float.Theorems.MemInterior
public import CORALean.ContSet.Zonotope.Float.Theorems.DeviationBound
public import Mathlib.Topology.Algebra.Group.Pointwise

@[expose] public section

/-!
# A `true` from `ZonoBundle.isFullDim` proves an interior point

The bundle is the intersection of its members. A point interior to every member is interior to the
intersection of finitely many of them (`interior_iInter_of_finite`).

## Inputs
* `zB` – float zonotope bundle
* `H` – right inverse of each member's generator matrix
* `x₀` – candidate interior point

## Hypotheses
* `h` – the test answers true

## Conclusion
* the bundle has an interior point
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

section
open Pointwise InflatedContSet

/-- A `true` from `Zonotope.interiorPoint` proves the point interior. -/
theorem Zonotope.aux_interiorPoint_sound {Z : Zonotope (Vec 𝕋 n)} {H : Mat 𝕋 Z.h n} {p : Vec 𝕋 n}
    (h : Z.interiorPoint H p = true) : -- --- CONCL ---
    toRealVec p ∈ interior Z.construct := by -- --- PROOF ---
  simp only [Zonotope.interiorPoint, Bool.and_eq_true, List.all_eq_true, List.mem_finRange,
    forall_const] at h
  obtain ⟨⟨hc, hd⟩, hE⟩ := h
  have hdev := toReal_lt_of_ltStrict hd
  have hx : (fun i => toReal (p i) - toReal (Z.I_error.inf i)) ∈ interior (nominalSet Z) :=
    Zonotope.mem_interior hc _ fun i =>
      lt_of_le_of_lt (Zonotope.deviation_bound p Z.I_error.inf Z.c Z.c (toRealVec Z.c)
        (fun _ => le_refl _) (fun _ => le_refl _) i) hdev
  have he : (fun i => toReal (Z.I_error.inf i)) ∈ (I_error Z).construct := fun i =>
    ⟨le_refl _, toReal_le_of_le (hE i)⟩
  have hsum : toRealVec p = (fun i => toReal (p i) - toReal (Z.I_error.inf i))
      + fun i => toReal (Z.I_error.inf i) := by
    funext i
    simp [toRealVec]
  rw [hsum]
  exact subset_interior_add_left (Set.add_mem_add hx he)

end


-- =======================================  MAIN THEOREM  ======================================= --

theorem ZonoBundle.isFullDim_sound {zB : ZonoBundle (Vec 𝕋 n)}
    {H : (i : Fin zB.k) → Mat 𝕋 (zB.Z i).h n} {x₀ : Vec 𝕋 n}
    (h : zB.isFullDim H x₀ = true) : (interior zB.construct).Nonempty := by
  simp only [ZonoBundle.isFullDim, List.all_eq_true, List.mem_finRange, forall_const] at h
  refine ⟨toRealVec x₀, ?_⟩
  rw [ZonoBundle.construct_eq_iInter, interior_iInter_of_finite]
  exact Set.mem_iInter.mpr fun i => Zonotope.aux_interiorPoint_sound (h i)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
