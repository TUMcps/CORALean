module

public import CORALean.ContSet.Taylm.Real.Theorems.MtimesOuter
public import CORALean.ContSet.Taylm.Real.Theorems.MemConstructIff
public import Mathlib.Data.Matrix.Mul

@[expose] public section

/-!
# `Taylm.mtimes` contains the image of the range set
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Taylm.mtimes_construct_outer {k m : ℕ} (M : Mat ℝ k m) (T : Fin m → Taylm n) :
    M.mulVec '' Taylm.construct T ⊆ Taylm.construct (Taylm.mtimes M T) := by -- --- PROOF ---
  rintro _ ⟨x, hx, rfl⟩
  obtain ⟨f, hf, t, ht, hxf⟩ := (Taylm.mem_construct_iff T x).1 hx
  refine (Taylm.mem_construct_iff _ _).2 ⟨fun i s => ∑ j, M i j * f j s,
    Taylm.mtimes_outer M hf, t, ht, fun i => ?_⟩
  simp only [Matrix.mulVec, dotProduct, hxf]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
