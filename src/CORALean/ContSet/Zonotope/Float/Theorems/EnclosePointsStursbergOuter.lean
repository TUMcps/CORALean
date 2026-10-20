module

public import CORALean.ContSet.Zonotope.Float.Operations.EnclosePointsStursberg
public import CORALean.ContSet.Zonotope.Float.Theorems.MtimesOuter
public import CORALean.ContSet.Zonotope.Float.Theorems.PlusOuter
public import CORALean.ContSet.Zonotope.Float.Theorems.ConstructPoint
public import CORALean.ContSet.Interval.Float.Theorems.MtimesOuter
public import CORALean.ContSet.Conversion.Float.Theorems.IntervalZonotopeContains
public import CORALean.ContSet.Conversion.Float.Operations.Interval_to_Zonotope
public import CORALean.ContSet.Conversion.Real.Operations.Interval_to_Zonotope
public import CORALean.ContSet.Conversion.Real.Theorems.IntervalZonotopeContains

@[expose] public section

/-!
# `Zonotope.enclosePointsStursberg` contains every point

Outer: with the stored basis orthogonal over the reals, `U Uᵀ = 1`, every input point lies in the
float result. The centered point lies in the interval of its two directed differences, so its
rotation lies in the interval `mtimes`, hence in the box of minima and maxima; the box rotates back
to the point, which `plus` moves to the mean. The mean's rounding is irrelevant.

## Inputs
* `pts` – points to enclose
* `U` – basis matrix
* `j` – point index

## Hypotheses
* `hU` – basis orthogonal over the reals

## Conclusion
* point lies in the enclosing zonotope
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open scoped Matrix Pointwise
open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n N : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zonotope.enclosePointsStursberg_outer [NeZero N] (pts : Fin N → Vec 𝕋 n) (U : Mat 𝕋 n n)
    (hU : toRealMat U * (toRealMat U)ᵀ = 1) (j : Fin N) : -- --- CONCL ---
    toRealVec (pts j) ∈ (Zonotope.enclosePointsStursberg pts U).construct := by -- --- PROOF ---
  unfold Zonotope.enclosePointsStursberg
  dsimp only
  set mean : Vec 𝕋 n := fun i => divUp (sumUp fun j => pts j i) (sumUp fun _ : Fin N => one)
    with hmean
  set sample : Fin N → Interval (Vec 𝕋 n) := fun j =>
    ⟨fun i => subDown (pts j i) (mean i), fun i => subUp (pts j i) (mean i)⟩ with hsample
  set oriented : Fin N → Interval (Vec 𝕋 n) := fun j =>
    Interval.mtimes U.transpose (sample j) with horiented
  set box : Interval (Vec 𝕋 n) :=
    ⟨fun i => minimumOver fun j => (oriented j).inf i,
     fun i => maximumOver fun j => (oriented j).sup i⟩ with hbox
  -- the centered point lies between its two directed differences
  set d : Vec ℝ n := toRealVec (pts j) - toRealVec mean with hd
  have hdmem : d ∈ (sample j).construct := fun i =>
    ⟨subDown_le_sub (pts j i) (mean i), sub_le_subUp (pts j i) (mean i)⟩
  -- its rotation lies in the interval product, then in the box
  have h1 := Interval.mtimes_outer U.transpose (sample j) ⟨d, hdmem, rfl⟩
  have h2 : toRealMat U.transpose *ᵥ d ∈ box.construct := fun i =>
    ⟨le_trans (minimumOver_le (fun j => (oriented j).inf i) j) (h1 i).1,
      le_trans (h1 i).2 (le_maximumOver (fun j => (oriented j).sup i) j)⟩
  -- rotated back it is the centered point, and `plus` moves it to the mean
  have h3 := Zonotope.mtimes_outer U box.zonotope
    (Set.mem_image_of_mem _ (Interval.zonotope_contains box h2))
  have h4 : toRealMat U *ᵥ (toRealMat U.transpose *ᵥ d) = d := by
    rw [Matrix.mulVec_mulVec]
    have : toRealMat U.transpose = (toRealMat U)ᵀ := rfl
    rw [this, hU, Matrix.one_mulVec]
  rw [h4] at h3
  have h5 := Zonotope.plus_outer (Zonotope.mtimes U box.zonotope) (Zonotope.point mean)
    ⟨d, h3, toRealVec mean, by rw [Zonotope.construct_point]; rfl, rfl⟩
  simpa only [hd, sub_add_cancel] using h5

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
