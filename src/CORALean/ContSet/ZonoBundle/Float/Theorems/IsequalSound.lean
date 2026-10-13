import CORALean.ContSet.ZonoBundle.Float.Operations.Isequal
import CORALean.ContSet.Zonotope.Float.Theorems.IsequalSound

/-!
# `ZonoBundle.isequal` is sound

A `true` answer says every member pair is `Zonotope.isequal`, so the members denote the same
sets and so do the intersections. `false` refutes nothing.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem ZonoBundle.isequal_sound {zB S : ZonoBundle (Vec 𝕋 n)} (h : zB.isequal S = true) :
    zB.construct = S.construct := by -- --- PROOF ---
  unfold ZonoBundle.isequal at h
  split at h
  · rename_i e
    simp only [List.all_eq_true, List.mem_finRange, forall_const] at h
    obtain ⟨k₁, Z₁⟩ := zB
    obtain ⟨k₂, Z₂⟩ := S
    simp only at e h
    subst e
    unfold ZonoBundle.construct
    exact Set.iInter_congr fun i => Zonotope.isequal_sound (h i)
  · simp at h

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
