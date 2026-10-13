import CORALean.ContSet.Zonotope.Float.Operations.IsFullDim
import CORALean.ContSet.Zonotope.Float.Operations.IsFullDimWith
import CORALean.ContSet.Zonotope.Float.Theorems.MemInterior
import Mathlib.Topology.Algebra.Group.Pointwise

/-!
# A `true` from `Zonotope.isFullDim` proves an interior point

The checked rows put every vector within `B` of the centre in the nominal zonotope
(`Zonotope.mem_interior`), so the open box of radius `B` around the centre lies inside it and
the centre is an interior point. Adding the error box's lower corner, a member of the nonempty
box, keeps an interior point (`subset_interior_add_left`).
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Matrix Pointwise FloatOps SoundFloatArithmetic InflatedContSet

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zonotope.isFullDim_sound {Z : Zonotope (Vec 𝕋 n)} {H : Mat 𝕋 Z.h n}
    (h : Z.isFullDimWith H = true) : (interior Z.construct).Nonempty := by -- --- PROOF ---
  simp only [Zonotope.isFullDimWith, Bool.and_eq_true, List.all_eq_true, List.mem_finRange,
    forall_const] at h
  obtain ⟨hc, hE⟩ := h
  obtain ⟨hB, -⟩ := Zonotope.ballCert_reach hc
  have hx : toRealVec Z.c ∈ interior (nominalSet Z) :=
    Zonotope.mem_interior hc _ fun i => by simpa [toRealVec] using hB
  have he : (fun i => toReal (Z.E.inf i)) ∈ (error Z).construct := fun i =>
    ⟨le_refl _, toReal_le_of_le (hE i)⟩
  exact ⟨_, subset_interior_add_left (Set.add_mem_add hx he)⟩

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
