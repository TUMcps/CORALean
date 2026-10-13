import CORALean.ContSet.Interval.Float.Theorems.MtimesIntervalMatOuter
import CORALean.ContSet.Interval.Float.Theorems.PlusOuter
import CORALean.ContSet.Interval.Float.Theorems.SubMemMatResidual
import CORALean.ContSet.Zonotope.Float.Operations.MtimesIntervalMat
import CORALean.ContSet.Zonotope.Float.Theorems.ZeroMemMtimesError

/-!
# `mtimesIntervalMat` keeps the origin in the error box

The interval-matrix counterpart of `ZeroMemMtimesError`. The result's box is
`mid(M) E ⊕ (M - mid(M)) E`: the first brackets `0` by `zero_mem_mtimes_error`,
and the second because it holds `R 0 = 0` for any `R` in the residual box, which
is nonempty as soon as `IM` holds one matrix `A` (`A - mid(M)` is then in it).
-/

-- Authors:       Tobias Ladner
-- Written:       09-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Matrix FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {m n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- `mtimesIntervalMat` keeps `0` in the error box, given the operand has it and `IM` holds a
matrix `A`. -/
theorem Zonotope.zero_mem_mtimesIntervalMat_error {IM : Interval (Mat 𝕋 m n)}
    {Z : Zonotope (Vec 𝕋 n)}
    {A : Mat ℝ m n} (hA : A ∈ IM.construct) (h : (0 : Vec ℝ n) ∈ Z.E.construct) :
    (0 : Vec ℝ m) ∈ (Zonotope.mtimesIntervalMat IM Z).E.construct := by -- --- PROOF ---
  set C := Interval.centreMat IM
  set Rs := Interval.matResidual IM.inf IM.sup C
  have hR : (fun i j => A i j - toReal (C i j)) ∈ Rs.construct :=
    Interval.sub_mem_matResidual fun i j => hA (i, j)
  -- the residual box times the error box holds `R 0 = 0`
  have hRe : (0 : Vec ℝ m) ∈ (Interval.mtimesIntervalMat Rs Z.E).construct := by
    have := Interval.mtimesIntervalMat_outer Rs Z.E (Set.mem_biUnion hR ⟨0, h, rfl⟩)
    simpa only [Matrix.mulVec_zero] using this
  -- and so does the sum of the two boxes
  have h0 := Interval.plus_outer _ _
    (Set.add_mem_add (Zonotope.zero_mem_mtimes_error (M := C) h) hRe)
  rw [add_zero] at h0
  exact h0

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
