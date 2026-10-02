import CORALean.ContSet.Taylm.Float.Operations.Bounds
import CORALean.ContSet.Taylm.Float.Operations.Mtimes
import CORALean.ContSet.Taylm.Float.Theorems.BoundsMem
import CORALean.ContSet.Taylm.Float.Theorems.MtimesOuter
import CORALean.ContSet.Taylm.Real.Theorems.MemConstructIff
import CORALean.Global.Float.FloatBound

/-!
# `Taylm.boundDot` over a floating-point scalar

CORA's `@taylm/supportFunc_` at `upper`: the float upper end of the range of `dirᵀ T`, where
`dirᵀ T` is `Taylm.mtimes` at a one-row float matrix and its range is `Taylm.bounds`. The
direction is a float vector `a` and `hc` says the functional `c` reads it, as for
`Interval.boundDot`. An upper bound only.
-/

-- Authors:       Tobias Ladner
-- Written:       02-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n m : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `supportFunc_`, `upper`: the upper end of the range of `aᵀ T`, rounded up. -/
def Taylm.boundDot {c : Vec ℝ m →ₗ[ℝ] ℝ} (a : Vec 𝕋 m) (T : Fin m → Taylm 𝕋 n)
    (hc : ∀ x : Vec ℝ m, c x = ∑ j, toReal (a j) * x j) :
    FloatBound 𝕋 (Taylm.construct T) c where
  val := (Taylm.mtimes (fun (_ : Fin 1) j => a j) T 0).bounds.2
  le x hx := by
    -- the point is the value at some `t` of functions the models enclose
    obtain ⟨f, hf, t, ht, hxf⟩ := (Real.Taylm.mem_construct_iff _ x).1 hx
    have hmem := Taylm.bounds_mem
      (Taylm.mtimes_outer (fun (_ : Fin 1) j => a j) (T := T) hf 0) ht
    rw [hc x]
    simpa [hxf] using hmem.2

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
