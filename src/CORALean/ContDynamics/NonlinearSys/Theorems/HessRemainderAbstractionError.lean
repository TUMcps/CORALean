module

public import CORALean.ContDynamics.NonlinearSys.Definitions.AbstractionError
public import CORALean.ContDynamics.NonlinearSys.Operations.HessRemainder
public import CORALean.ContSet.Interval.Float.Instances
public import CORALean.ContSet.Interval.Float.Theorems.MatPlusOuter
public import CORALean.ContSet.Interval.Float.Theorems.MemPoint
public import CORALean.ContSet.Interval.Float.Theorems.MtimesIntervalMatOuter
public import CORALean.ContSet.Interval.Float.Theorems.PlusOuter

@[expose] public section

/-!
# `hessRemainder` is an abstraction-error certificate

The real layer's notion at the real images of the float data, as
`slopeRemainder_abstractionError` is for the first-order box: wherever the model
encloses `sys` to second order and the expansion point lies in the box, the
expansion `Encloses.taylor_mem` hands back rewrites the remainder as
`(J_x - A)(x - x✱) + (J_u - B)(u - u✱) + ½ dzᵀ Hᵢ dz`. The first two terms lie in
their interval products, the last in `[-l, l]` by `abs_bilin_le_bilinUp`, every
entry of `|dz|` and of `|Hᵢ|` bounded by the larger end of its box.
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float FloatOps SoundFloatArithmetic Matrix

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n m : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- A matrix's negation, stored entrywise, is a point interval at the negated real one. -/
theorem aux_hessRem_neg_mat {k l : ℕ} (A : Mat 𝕋 k l) :
    -Scalar.toRealMat A ∈
      (Interval.point (α := Mat 𝕋 k l) (-A)).construct := by -- --- PROOF ---
  have h := Interval.mem_point (α := Mat 𝕋 k l) (-A)
  have he : (RealImage.realImage (α := Mat 𝕋 k l) (-A) : Mat ℝ k l)
      = -Scalar.toRealMat A := by
    funext i j
    exact toReal_neg (A i j)
  rwa [he] at h

/-- The same for a vector. -/
theorem aux_hessRem_neg_vec {k : ℕ} (v : Vec 𝕋 k) :
    -toRealVec v ∈ (Interval.point (α := Vec 𝕋 k) (-v)).construct := by
  have h := Interval.mem_point (α := Vec 𝕋 k) (-v)
  have he : (RealImage.realImage (α := Vec 𝕋 k) (-v) : Vec ℝ k) = -toRealVec v :=
    funext fun i => toReal_neg (v i)
  rwa [he] at h

/-- `y - ys` lies in the box `Y - ys`. -/
theorem aux_hessRem_sub_mem {k : ℕ} {Y : Interval (Vec 𝕋 k)} (ys : Vec 𝕋 k) {y : Vec ℝ k}
    (hy : y ∈ Y.construct) :
    y - toRealVec ys ∈ (Interval.plus Y (Interval.point (-ys))).construct := by
  have hd := Interval.plus_outer Y _ (Set.add_mem_add hy (aux_hessRem_neg_vec ys))
  rwa [← sub_eq_add_neg] at hd

/-- `(J - A)(y - ys)` lies in `([J] - A)(Y - ys)`. -/
theorem aux_hessRem_jacTerm {k l : ℕ} {IJ : Interval (Mat 𝕋 k l)} {Y : Interval (Vec 𝕋 l)}
    (A : Mat 𝕋 k l) (ys : Vec 𝕋 l) {J : Mat ℝ k l} (hJ : J ∈ IJ.construct) {y : Vec ℝ l}
    (hy : y ∈ Y.construct) : -- --- STMT ---
    (J - Scalar.toRealMat A) *ᵥ (y - toRealVec ys) ∈
      (Interval.mtimesIntervalMat (Interval.matPlus IJ (Interval.point (α := Mat 𝕋 k l)
        (-A))) (Interval.plus Y (Interval.point (α := Vec 𝕋 l)
          (-ys)))).construct := by -- --- PROOF ---
  have hM := Interval.matPlus_outer IJ _ hJ (aux_hessRem_neg_mat A)
  rw [← sub_eq_add_neg] at hM
  exact Interval.mtimesIntervalMat_outer _ _
    (Set.mem_biUnion hM (Set.mem_image_of_mem _ (aux_hessRem_sub_mem ys hy)))

/-- A point of a box is no larger in magnitude than the box's `normMag`. -/
theorem aux_hessRem_abs_le {k : ℕ} {I : Interval (Vec 𝕋 k)} {y : Vec ℝ k} (hy : y ∈ I.construct)
    (j : Fin k) : |y j| ≤ toReal (I.normMag j) := by
  obtain ⟨h1, h2⟩ := hy j
  rw [Interval.normMag, toReal_maximum, toReal_absolute, toReal_absolute]
  exact abs_le_max_abs_abs h1 h2

/-- A matrix of a box is entrywise no larger in magnitude than the larger end. -/
theorem aux_hessRem_abs_le_mat {k : ℕ} {I : Interval (Mat 𝕋 k k)} {M : Mat ℝ k k}
    (hM : M ∈ I.construct) (j l : Fin k) :
    |M j l| ≤ toReal (maximum (absolute (I.inf j l)) (absolute (I.sup j l))) := by
  have h := hM (j, l)
  simp only [Entrywise.entry_mat] at h
  rw [toReal_maximum, toReal_absolute, toReal_absolute]
  exact abs_le_max_abs_abs h.1 h.2

/-- Bounds on two blocks bound their concatenation. -/
theorem aux_hessRem_abs_append {v : Vec ℝ n} {w : Vec ℝ m} {a : Vec 𝕋 n} {b : Vec 𝕋 m}
    (hv : ∀ j, |v j| ≤ toReal (a j)) (hw : ∀ j, |w j| ≤ toReal (b j)) :
    ∀ j, |Fin.append v w j| ≤ toReal ((Fin.append a b : Vec 𝕋 (n + m)) j) :=
  Fin.addCases (fun j => by simpa using hv j) (fun j => by simpa using hw j)

/-- What `|q| ≤ L` says of `q / 2` against the symmetric box at `½ L`. -/
theorem aux_hessRem_half_mem {q : ℝ} {L : 𝕋} (hq : |q| ≤ toReal L) :
    toReal (neg (half L)) ≤ q / 2 ∧ q / 2 ≤ toReal (half L) := by
  rw [toReal_neg, toReal_half]
  obtain ⟨h1, h2⟩ := abs_le.mp hq
  constructor <;> linarith


-- =======================================  MAIN THEOREM  ======================================= --

/-- Where `fm` encloses `sys` to second order and `(xs, us)` lies in `X × U`,
`hessRemainder` certifies the linearization at `A`, `B` over `X × U`. -/
theorem NonlinearSys.FloatHessModel.Encloses.hessRemainder_abstractionError
    {fm : NonlinearSys.FloatHessModel 𝕋 n m} {sys : NonlinearSys n m} (h : fm.Encloses sys)
    (A : Mat 𝕋 n n) (B : Mat 𝕋 n m) {xs : Vec 𝕋 n} {us : Vec 𝕋 m} {X : Interval (Vec 𝕋 n)}
    {U : Interval (Vec 𝕋 m)} (hxs : toRealVec xs ∈ X.construct)
    (hus : toRealVec us ∈ U.construct) :
    AbstractionError (S := ℐ𝒱[𝕋]) sys.f (Scalar.toRealMat A)
      (Scalar.toRealMat B) (toRealVec xs) (toRealVec us) X.construct U.construct
      (fm.hessRemainder A B xs us X U) where
  encloses x hx u hu := by
    obtain ⟨Jx, hJx, Ju, hJu, H, hH, htay⟩ := h.taylor_mem X U xs us hxs hus x hx u hu
    set dz := Fin.append (x - toRealVec xs) (u - toRealVec us)
    -- the remainder, rewritten through the expansion
    have hrem : sys.f x u - (sys.f (toRealVec xs) (toRealVec us)
        + Scalar.toRealMat A *ᵥ (x - toRealVec xs) + Scalar.toRealMat B *ᵥ (u - toRealVec us))
        = ((Jx - Scalar.toRealMat A) *ᵥ (x - toRealVec xs)
          + (Ju - Scalar.toRealMat B) *ᵥ (u - toRealVec us))
          + fun i => dz ⬝ᵥ (H i *ᵥ dz) / 2 := by
      have hf : sys.f x u = sys.f (toRealVec xs) (toRealVec us)
          + (Jx *ᵥ (x - toRealVec xs) + Ju *ᵥ (u - toRealVec us)
            + fun i => dz ⬝ᵥ (H i *ᵥ dz) / 2) := by
        rw [← htay]; abel
      rw [Matrix.sub_mulVec, Matrix.sub_mulVec, hf]
      abel
    rw [hrem]
    -- `|dz|` entrywise inside the bound it is boxed by
    have hdz := aux_hessRem_abs_append (aux_hessRem_abs_le (aux_hessRem_sub_mem xs hx))
      (aux_hessRem_abs_le (aux_hessRem_sub_mem us hu))
    refine Interval.plus_outer _ _ (Set.add_mem_add (Interval.plus_outer _ _
      (Set.add_mem_add (aux_hessRem_jacTerm A xs hJx hx) (aux_hessRem_jacTerm B us hJu hu)))
      fun i => ?_)
    -- the quadratic term, component by component
    exact aux_hessRem_half_mem (abs_bilin_le_bilinUp hdz hdz
      (aux_hessRem_abs_le_mat (hH i)))

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
