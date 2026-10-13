import CORALean.ContSet.Zonotope.Float.Operations.ContainsPoint
import CORALean.ContSet.Zonotope.Float.Theorems.BoxSubset
import CORALean.ContSet.Zonotope.Float.Theorems.DeviationBound

/-!
# A `true` from `Zonotope.containsPoint` proves membership

The point minus the error box's lower corner is within `B` of the centre, so in the nominal set
(`Zonotope.box_subset`); adding the corner, a member of the nonempty box, gives the point.
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

theorem Zonotope.containsPoint_sound {Z : Zonotope (Vec 𝕋 n)} {H : Mat 𝕋 Z.h n} {p : Vec 𝕋 n}
    (h : Z.containsPoint H p = true) : toRealVec p ∈ Z.construct := by -- --- PROOF ---
  simp only [Zonotope.containsPoint, Bool.and_eq_true, List.all_eq_true, List.mem_finRange,
    forall_const] at h
  obtain ⟨⟨hc, hd⟩, hE⟩ := h
  have hdev := toReal_le_of_le hd
  have hx : (fun i => toReal (p i) - toReal (Z.E.inf i)) ∈ nominalSet Z :=
    Zonotope.box_subset hc _ fun i =>
      le_trans (Zonotope.deviation_bound p Z.E.inf Z.c Z.c (toRealVec Z.c)
        (fun _ => le_refl _) (fun _ => le_refl _) i) hdev
  have he : (fun i => toReal (Z.E.inf i)) ∈ (error Z).construct := fun i =>
    ⟨le_refl _, toReal_le_of_le (hE i)⟩
  have hsum : toRealVec p = (fun i => toReal (p i) - toReal (Z.E.inf i))
      + fun i => toReal (Z.E.inf i) := by
    funext i
    simp [toRealVec]
  rw [hsum]
  exact Set.add_mem_add hx he

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
