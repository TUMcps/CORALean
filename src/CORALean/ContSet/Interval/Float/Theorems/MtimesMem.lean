import CORALean.ContSet.Interval.Float.Theorems.MtimesOuter

/-!
# A matrix-vector product is in the `Interval.mtimes` box
`Interval.mtimes_outer` at a point: a real matrix equal to the float one read as reals, applied to a
vector of the box.
-/

-- Authors:       Tobias Ladner
-- Written:       12-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Matrix FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋]


-- =======================================  MAIN THEOREM  ======================================= --

theorem Interval.mtimes_mem {m n : ℕ} (M : Mat 𝕋 m n) (M' : Mat ℝ m n) (hM : M' = toRealMat M)
    (I : Interval (Vec 𝕋 n)) {x : Vec ℝ n} (hx : x ∈ I.construct) :
    M' *ᵥ x ∈ (Interval.mtimes M I).construct :=
  hM ▸ Interval.mtimes_outer M I ⟨x, hx, rfl⟩

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
