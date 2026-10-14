module

public import CORALean.ContSet.Zonotope.Float.Operations.InteriorPoint
public import CORALean.ContSet.Zonotope.Float.Theorems.MemInterior
public import CORALean.ContSet.Zonotope.Float.Theorems.DeviationBound
public import Mathlib.Topology.Algebra.Group.Pointwise

@[expose] public section

/-!
# A `true` from `Zonotope.interiorPoint` proves the point interior

The point minus the error box's lower corner is strictly within `B` of the centre, so interior to
the nominal set (`Zonotope.mem_interior`); adding the corner keeps it interior.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Pointwise FloatOps SoundFloatArithmetic InflatedContSet

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zonotope.interiorPoint_sound {Z : Zonotope (Vec 𝕋 n)} {H : Mat 𝕋 Z.h n} {p : Vec 𝕋 n}
    (h : Z.interiorPoint H p = true) : toRealVec p ∈ interior Z.construct := by -- --- PROOF ---
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

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
