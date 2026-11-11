module

public import CORALean.ContDynamics.NonlinearSys.Definitions.FloatHessModel
public import CORALean.ContDynamics.NonlinearSys.Operations.AbstrErrAdaptiveFloat
public import CORALean.ContSet.Conversion.Float.Theorems.IntervalZonotopeContains
public import CORALean.ContSet.Conversion.Float.Theorems.ZonotopeIntervalContains
public import CORALean.ContSet.Interval.Float.Instances
public import CORALean.ContSet.Interval.Float.Theorems.MatPlusOuter
public import CORALean.ContSet.Interval.Float.Theorems.MemPoint
public import CORALean.ContSet.Interval.Float.Theorems.MtimesIntervalMatOuter
public import CORALean.ContSet.Interval.Float.Theorems.PlusOuter
public import CORALean.ContSet.Zonotope.Float.Theorems.CartProdExact
public import CORALean.ContSet.Zonotope.Float.Theorems.QuadMapOuter
public import CORALean.ContSet.Zonotope.Float.Theorems.RecenterSubMem
public import CORALean.ContSet.Zonotope.Float.Theorems.ReduceAdaptiveOuter

@[expose] public section

/-!
# `hessRemainder` holds the remainder at the model's Jacobians and Hessians

At Jacobians and Hessians from the model's boxes, `(J_x - A)(x - x✱) + (J_u - B)(u - u✱) + ½ zᵀ Hᵢ
z` for a state of `X` and an input of `U` lies in `hessRemainder`: the differences to the point are
bounded by the boxes' magnitudes, the Jacobian terms by interval products, and the quadratic form by
`bilinUp`.

## Inputs
* `fm` – float Hessian model
* `A` – state matrix
* `B` – input matrix
* `xs` – state expansion point
* `us` – input expansion point
* `X` – state box
* `U` – input box
* `Jx` – state Jacobian
* `Ju` – input Jacobian
* `H` – Hessians
* `x` – state value in the state box
* `u` – input value in the input box

## Hypotheses
* `hJx` – the state Jacobian is in its box
* `hJu` – the input Jacobian is in its box
* `hH` – the Hessians are in their boxes
* `hx` – the state is in `X`
* `hu` – the input is in `U`

## Conclusion
* the remainder form is in `hessRemainder`
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       11-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float FloatOps SoundFloatArithmetic Matrix

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n m : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- A matrix's negation, stored entrywise, is a point interval at the negated real one. -/
private theorem aux_aea_neg_mat {k l : ℕ} (A : Mat 𝕋 k l) : -- --- CONCL ---
    -Scalar.toRealMat A ∈
      (Interval.point (α := Mat 𝕋 k l) (-A)).toSet := by -- --- PROOF ---
  have h := Interval.mem_point (α := Mat 𝕋 k l) (-A)
  have he : (RealImage.realImage (α := Mat 𝕋 k l) (-A) : Mat ℝ k l)
      = -Scalar.toRealMat A := by
    funext i j
    exact toReal_neg (A i j)
  rwa [he] at h

/-- The same for a vector. -/
private theorem aux_aea_neg_vec {k : ℕ} (v : Vec 𝕋 k) :
    -toRealVec v ∈ (Interval.point (α := Vec 𝕋 k) (-v)).toSet := by
  have h := Interval.mem_point (α := Vec 𝕋 k) (-v)
  have he : (RealImage.realImage (α := Vec 𝕋 k) (-v) : Vec ℝ k) = -toRealVec v :=
    funext fun i => toReal_neg (v i)
  rwa [he] at h

/-- `y - ys` lies in the box `Y - ys`. -/
private theorem aux_aea_sub_mem {k : ℕ} {Y : Interval (Vec 𝕋 k)} (ys : Vec 𝕋 k) {y : Vec ℝ k}
    (hy : y ∈ Y.toSet) :
    y - toRealVec ys ∈ (Interval.plus Y (Interval.point (-ys))).toSet := by
  have hd := Interval.plus_outer Y _ (Set.add_mem_add hy (aux_aea_neg_vec ys))
  rwa [← sub_eq_add_neg] at hd

/-- `(J - A)(y - ys)` lies in `([J] - A)(Y - ys)`. -/
private theorem aux_aea_jacTerm {k l : ℕ} {IJ : Interval (Mat 𝕋 k l)} {Y : Interval (Vec 𝕋 l)}
    (A : Mat 𝕋 k l) (ys : Vec 𝕋 l) {J : Mat ℝ k l} (hJ : J ∈ IJ.toSet) {y : Vec ℝ l}
    (hy : y ∈ Y.toSet) : -- --- CONCL ---
    (J - Scalar.toRealMat A) *ᵥ (y - toRealVec ys) ∈
      (Interval.mtimesIntervalMat (Interval.matPlus IJ (Interval.point (α := Mat 𝕋 k l)
        (-A))) (Interval.plus Y (Interval.point (α := Vec 𝕋 l)
          (-ys)))).toSet := by -- --- PROOF ---
  have hM := Interval.matPlus_outer IJ _ hJ (aux_aea_neg_mat A)
  rw [← sub_eq_add_neg] at hM
  exact Interval.mtimesIntervalMat_outer _ _
    (Set.mem_biUnion hM (Set.mem_image_of_mem _ (aux_aea_sub_mem ys hy)))

/-- A point of a box is no larger in magnitude than the box's `normMag`. -/
private theorem aux_aea_abs_le {k : ℕ} {I : Interval (Vec 𝕋 k)} {y : Vec ℝ k}
    (hy : y ∈ I.toSet) (j : Fin k) : |y j| ≤ toReal (I.normMag j) := by
  obtain ⟨h1, h2⟩ := hy j
  rw [Interval.normMag, toReal_maximum, toReal_absolute, toReal_absolute]
  exact abs_le_max_abs_abs h1 h2

/-- A matrix of a box is entrywise no larger in magnitude than the larger end. -/
private theorem aux_aea_abs_le_mat {k : ℕ} {I : Interval (Mat 𝕋 k k)} {M : Mat ℝ k k}
    (hM : M ∈ I.toSet) (j l : Fin k) :
    |M j l| ≤ toReal (maximum (absolute (I.inf j l)) (absolute (I.sup j l))) := by
  have h := hM (j, l)
  simp only [Entrywise.entry_mat] at h
  rw [toReal_maximum, toReal_absolute, toReal_absolute]
  exact abs_le_max_abs_abs h.1 h.2

/-- Bounds on two blocks bound their concatenation. -/
private theorem aux_aea_abs_append {v : Vec ℝ n} {w : Vec ℝ m} {a : Vec 𝕋 n} {b : Vec 𝕋 m}
    (hv : ∀ j, |v j| ≤ toReal (a j)) (hw : ∀ j, |w j| ≤ toReal (b j)) :
    ∀ j, |Fin.append v w j| ≤ toReal ((Fin.append a b : Vec 𝕋 (n + m)) j) :=
  Fin.addCases (fun j => by simpa using hv j) (fun j => by simpa using hw j)

/-- What `|q| ≤ L` says of `q / 2` against the symmetric box at `½ L`. -/
private theorem aux_aea_half_mem {q : ℝ} {L : 𝕋} (hq : |q| ≤ toReal L) :
    toReal (neg (half L)) ≤ q / 2 ∧ q / 2 ≤ toReal (half L) := by
  rw [toReal_neg, toReal_half]
  obtain ⟨h1, h2⟩ := abs_le.mp hq
  constructor <;> linarith


-- =======================================  MAIN THEOREM  ======================================= --

/-- The remainder form `hessRemainder` bounds, at Jacobians and Hessians from the model's boxes:
`(J_x - A)(x - x✱) + (J_u - B)(u - u✱) + ½ zᵀ Hᵢ z` for `x ∈ X`, `u ∈ U`. -/
theorem NonlinearSys.FloatHessModel.hessRemainder_mem (fm : NonlinearSys.FloatHessModel 𝕋 n m)
    (A : Mat 𝕋 n n) (B : Mat 𝕋 n m) (xs : Vec 𝕋 n) (us : Vec 𝕋 m) (X : Interval (Vec 𝕋 n))
    (U : Interval (Vec 𝕋 m)) {Jx : Mat ℝ n n} {Ju : Mat ℝ n m} {H : Fin n → Mat ℝ (n + m) (n + m)}
    (hJx : Jx ∈ (fm.jacX (Interval.point xs) (Interval.point us)).toSet)
    (hJu : Ju ∈ (fm.jacU (Interval.point xs) (Interval.point us)).toSet)
    (hH : ∀ i, H i ∈ (fm.hess X U i).toSet) {x : Vec ℝ n} {u : Vec ℝ m} (hx : x ∈ X.toSet)
    (hu : u ∈ U.toSet) : -- --- CONCL ---
    ((Jx - Scalar.toRealMat A) *ᵥ (x - toRealVec xs) + (Ju - Scalar.toRealMat B) *ᵥ
      (u - toRealVec us)) + (fun i => Fin.append (x - toRealVec xs) (u - toRealVec us) ⬝ᵥ
        (H i *ᵥ Fin.append (x - toRealVec xs) (u - toRealVec us)) / 2) ∈
      (fm.hessRemainder A B xs us X U).toSet := by -- --- PROOF ---
  have hdz := aux_aea_abs_append (aux_aea_abs_le (aux_aea_sub_mem xs hx))
    (aux_aea_abs_le (aux_aea_sub_mem us hu))
  refine Interval.plus_outer _ _ (Set.add_mem_add (Interval.plus_outer _ _
    (Set.add_mem_add (aux_aea_jacTerm A xs hJx hx) (aux_aea_jacTerm B us hJu hu))) fun i => ?_)
  exact aux_aea_half_mem (abs_bilin_le_bilinUp hdz hdz (aux_aea_abs_le_mat (hH i)))

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
