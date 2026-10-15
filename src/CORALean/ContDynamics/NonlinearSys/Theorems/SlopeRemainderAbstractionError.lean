module

public import CORALean.ContDynamics.NonlinearSys.Definitions.AbstractionError
public import CORALean.ContDynamics.NonlinearSys.Operations.SlopeRemainder
public import CORALean.ContSet.Interval.Float.Theorems.MatPlusOuter
public import CORALean.ContSet.Interval.Float.Theorems.MemPoint
public import CORALean.ContSet.Interval.Float.Theorems.MtimesIntervalMatOuter
public import CORALean.ContSet.Interval.Float.Theorems.PlusOuter

@[expose] public section

/-!
# `slopeRemainder` is an abstraction-error certificate

The real layer's notion, at the real images of the float data: wherever the
model encloses `f` and the expansion point lies in the box, `slopeRemainder` is
an `AbstractionError` for `A`, `B` over `X × U`. The slope at `(x, u)` against
`(x✱, u✱)` rewrites the remainder as `(J_x - A)(x - x✱) + (J_u - B)(u - u✱)`, and
each factor lies in the interval its operation was given.
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float FloatOps SoundFloatArithmetic Matrix

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n m : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- A matrix's negation, stored entrywise, is a point interval at the negated
real matrix. -/
theorem aux_neg_mem_point {k l : ℕ} (A : Mat 𝕋 k l) :
    -Scalar.toRealMat A ∈
      (Interval.point (α := Mat 𝕋 k l) (-A)).construct := by -- --- PROOF ---
  have h := Interval.mem_point (α := Mat 𝕋 k l) (-A)
  have he : (RealImage.realImage (α := Mat 𝕋 k l) (-A) : Mat ℝ k l)
      = -Scalar.toRealMat A := by
    funext i j
    exact toReal_neg (A i j)
  rwa [he] at h

/-- The same for a vector. -/
theorem aux_neg_mem_point_vec {k : ℕ} (v : Vec 𝕋 k) :
    -toRealVec v ∈
      (Interval.point (α := Vec 𝕋 k) (-v)).construct := by -- --- PROOF ---
  have h := Interval.mem_point (α := Vec 𝕋 k) (-v)
  have he : (RealImage.realImage (α := Vec 𝕋 k) (-v) : Vec ℝ k) = -toRealVec v := by
    funext i
    exact toReal_neg (v i)
  rwa [he] at h

/-- `(J - A)(y - ys)` lies in `([J] - A)(Y - ys)`. -/
theorem aux_mem_slopeTerm {k l : ℕ} {IJ : Interval (Mat 𝕋 k l)} {Y : Interval (Vec 𝕋 l)}
    (A : Mat 𝕋 k l) (ys : Vec 𝕋 l) {J : Mat ℝ k l} (hJ : J ∈ IJ.construct) {y : Vec ℝ l}
    (hy : y ∈ Y.construct) :
    (J - Scalar.toRealMat A) *ᵥ (y - toRealVec ys) ∈
      (Interval.mtimesIntervalMat (Interval.matPlus IJ (Interval.point (α := Mat 𝕋 k l)
        (-A))) (Interval.plus Y (Interval.point (α := Vec 𝕋 l)
          (-ys)))).construct := by -- --- PROOF ---
  have hM := Interval.matPlus_outer IJ _ hJ (aux_neg_mem_point A)
  have hd := Interval.plus_outer Y _ (Set.add_mem_add hy (aux_neg_mem_point_vec ys))
  rw [← sub_eq_add_neg] at hM hd
  exact Interval.mtimesIntervalMat_outer _ _
    (Set.mem_biUnion hM (Set.mem_image_of_mem _ hd))


-- =======================================  MAIN THEOREM  ======================================= --

/-- Where `fm` encloses `sys` and `(xs, us)` lies in `X × U`, `slopeRemainder`
certifies the linearization at `A`, `B` over `X × U`. -/
theorem NonlinearSys.FloatModel.Encloses.slopeRemainder_abstractionError
    {fm : NonlinearSys.FloatModel 𝕋 n m} {sys : NonlinearSys n m} (h : fm.Encloses sys)
    (A : Mat 𝕋 n n) (B : Mat 𝕋 n m) {xs : Vec 𝕋 n} {us : Vec 𝕋 m} {X : Interval (Vec 𝕋 n)}
    {U : Interval (Vec 𝕋 m)} (hxs : toRealVec xs ∈ X.construct)
    (hus : toRealVec us ∈ U.construct) :
    AbstractionError (S := ℐ𝒱[𝕋]) sys.f (Scalar.toRealMat A)
      (Scalar.toRealMat B) (toRealVec xs) (toRealVec us) X.construct U.construct
      (fm.slopeRemainder A B xs us X U) where
  encloses x hx u hu := by
    obtain ⟨Jx, hJx, Ju, hJu, hslope⟩ := h.slope_mem X U x hx _ hxs u hu _ hus
    -- the remainder, rewritten through the slope
    have hrem : sys.f x u - (sys.f (toRealVec xs) (toRealVec us)
        + Scalar.toRealMat A *ᵥ (x - toRealVec xs) + Scalar.toRealMat B *ᵥ (u - toRealVec us))
        = (Jx - Scalar.toRealMat A) *ᵥ (x - toRealVec xs)
          + (Ju - Scalar.toRealMat B) *ᵥ (u - toRealVec us) := by
      have hf : sys.f x u = sys.f (toRealVec xs) (toRealVec us)
          + (Jx *ᵥ (x - toRealVec xs) + Ju *ᵥ (u - toRealVec us)) := by
        rw [← hslope]; abel
      rw [Matrix.sub_mulVec, Matrix.sub_mulVec, hf]
      abel
    rw [hrem]
    exact Interval.plus_outer _ _ (Set.add_mem_add (aux_mem_slopeTerm A xs hJx hx)
      (aux_mem_slopeTerm B us hJu hu))

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
