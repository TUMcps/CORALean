module

public import CORALean.ContSet.Taylm.Float.Operations.Bounds
public import CORALean.ContSet.Taylm.Float.Theorems.BoundsMem
public import CORALean.ContSet.Taylm.Real.Theorems.MemConstructIff
public import CORALean.ContSet.Interval.Float.Interval

@[expose] public section

/-!
# An array of float Taylor models as a float box

Each coordinate's float `bounds`, outward-rounded; outer, as the exact layer's.
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}

def Taylm.interval {m : ℕ} (T : Fin m → Taylm 𝕋 n) : Interval (Vec 𝕋 m) :=
  ⟨fun i => (T i).bounds.1, fun i => (T i).bounds.2⟩


-- =======================================  MAIN THEOREM  ======================================= --

theorem Taylm.interval_contains {m : ℕ} (T : Fin m → Taylm 𝕋 n) :
    Taylm.construct T ⊆ (Taylm.interval T).construct := by -- --- PROOF ---
  intro x hx i
  obtain ⟨f, hf, t, ht, hxf⟩ := (Real.Taylm.mem_construct_iff _ x).1 hx
  have := Taylm.bounds_mem (hf i) ht
  rw [← hxf i] at this
  exact this

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
