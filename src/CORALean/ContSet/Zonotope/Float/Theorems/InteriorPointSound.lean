import CORALean.ContSet.Zonotope.Float.Operations.InteriorPoint
import CORALean.ContSet.Zonotope.Float.Theorems.MemInterior
import CORALean.ContSet.Zonotope.Float.Theorems.DeviationBound
import Mathlib.Topology.Algebra.Group.Pointwise

/-!
# A `true` from `Zonotope.interiorPoint` proves the point interior

The point minus the error box's lower corner is strictly within `B` of the centre, so interior to
the nominal set (`Zonotope.mem_interior`); adding the corner keeps it interior.
-/

-- Authors:       Tobias Ladner
-- Written:       04-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Pointwise FloatOps SoundFloatArithmetic InflatedContSet

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zonotope.interiorPoint_sound {Z : Zonotope 𝕋 n} {H : Mat 𝕋 Z.h n} {p : Vec 𝕋 n}
    (h : Z.interiorPoint H p = true) : toRealVec p ∈ interior Z.construct := by -- --- PROOF ---
  simp only [Zonotope.interiorPoint, Bool.and_eq_true, List.all_eq_true, List.mem_finRange,
    forall_const] at h
  obtain ⟨⟨hc, hd⟩, hE⟩ := h
  have hdev := toReal_lt_of_ltStrict hd
  have hx : (fun i => toReal (p i) - toReal (Z.E.inf i)) ∈ interior (nominalSet Z) :=
    Zonotope.mem_interior hc _ fun i =>
      lt_of_le_of_lt (Zonotope.deviation_bound p Z.E.inf Z.c Z.c (toRealVec Z.c)
        (fun _ => le_refl _) (fun _ => le_refl _) i) hdev
  have he : (fun i => toReal (Z.E.inf i)) ∈ (error Z).construct := fun i =>
    ⟨le_refl _, toReal_le_of_le (hE i)⟩
  have hsum : toRealVec p = (fun i => toReal (p i) - toReal (Z.E.inf i))
      + fun i => toReal (Z.E.inf i) := by
    funext i
    simp [toRealVec]
  rw [hsum]
  exact subset_interior_add_left (Set.add_mem_add hx he)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
