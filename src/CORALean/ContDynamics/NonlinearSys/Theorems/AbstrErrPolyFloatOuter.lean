module

public import CORALean.ContDynamics.NonlinearSys.Operations.AbstrErrPolyFloat
public import CORALean.ContSet.Interval.Float.Instances
public import CORALean.ContSet.Interval.Float.Theorems.MatPlusOuter
public import CORALean.ContSet.Interval.Float.Theorems.MemPoint
public import CORALean.ContSet.Interval.Float.Theorems.MtimesIntervalMatOuter
public import CORALean.ContSet.Interval.Float.Theorems.PlusOuter
public import CORALean.ContSet.PolyZonotope.Float.Theorems.QuadMapOuter
public import CORALean.ContSet.Conversion.Float.Operations.ConPolyZono_to_PolyZonotope
public import CORALean.ContSet.Conversion.Float.Operations.Interval_to_Zonotope
public import CORALean.ContSet.Conversion.Float.Operations.PolyZonotope_to_Zonotope
public import CORALean.ContSet.Conversion.Float.Operations.Zonotope_to_Interval
public import CORALean.ContSet.Conversion.Float.Operations.Zonotope_to_PolyZonotope
public import CORALean.ContSet.Conversion.Real.Operations.Interval_to_Zonotope
public import CORALean.ContSet.Conversion.Real.Operations.PolyZonotope_to_Zonotope
public import CORALean.ContSet.Conversion.Real.Operations.Zonotope_to_Interval
public import CORALean.ContSet.Conversion.Float.Theorems.ConPolyZonoPolyZonotopeContains
public import CORALean.ContSet.Conversion.Float.Theorems.Basic
public import CORALean.ContSet.Conversion.Float.Theorems.IntervalZonotopeContains
public import CORALean.ContSet.Conversion.Float.Theorems.PolyZonotopeZonotopeContains
public import CORALean.ContSet.Conversion.Float.Theorems.ZonotopeIntervalContains
public import CORALean.ContSet.Conversion.Float.Theorems.ZonotopePolyZonotopeContains
public import CORALean.ContSet.Conversion.Real.Theorems.IntervalZonotopeContains
public import CORALean.ContSet.Conversion.Real.Theorems.PolyZonotopeZonotopeContains
public import CORALean.ContSet.Conversion.Real.Theorems.ZonotopeIntervalContains

@[expose] public section

/-!
# `abstrErrPolyFloat` holds the remainder at every state of the step

At a state `x = x(0) + δ` with `x(0) - x✱ ∈ Rdelta`, `δ ∈ Rdiff`, `x ∈ X`, `u ∈ U`, the
expansion `Encloses.taylor_mem` hands back leaves `(J - [A B]) dz + ½ dzᵀ Hᵢ dz`, and
with `dz = z₀ + δz` the quadratic term is `½ z₀ᵀ H(z✱)ᵢ z₀` plus
`½ (z₀ᵀ (Hᵢ - H(z✱)ᵢ) z₀ + z₀ᵀ Hᵢ δz + δzᵀ Hᵢ z₀ + δzᵀ Hᵢ δz)`. The first is the
static error at `x(0) - x✱`, a point of the start set, so `quadMap_outer` places it;
each of the other four is bounded by `abs_bilin_le_bilinUp`.
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float FloatOps SoundFloatArithmetic Matrix ContSet

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n m : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- A matrix's negation, stored entrywise, is a point interval at the negated real one. -/
theorem aux_polyErr_neg_mat {k l : ℕ} (A : Mat 𝕋 k l) :
    -Scalar.toRealMat A ∈
      (Interval.point (α := Mat 𝕋 k l) (fun i j => neg (A i j))).construct := by -- --- PROOF ---
  have h := Interval.mem_point (α := Mat 𝕋 k l) (fun i j => neg (A i j))
  have he : (RealImage.realImage (α := Mat 𝕋 k l) (fun i j => neg (A i j)) : Mat ℝ k l)
      = -Scalar.toRealMat A := by
    funext i j
    exact toReal_neg (A i j)
  rwa [he] at h

/-- `y - ys` lies in the box `Y - ys`. -/
theorem aux_polyErr_sub_mem {k : ℕ} {Y : Interval (Vec 𝕋 k)} (ys : Vec 𝕋 k) {y : Vec ℝ k}
    (hy : y ∈ Y.construct) :
    y - toRealVec ys ∈
      (Interval.plus Y (Interval.point fun i => neg (ys i))).construct := by -- --- PROOF ---
  have hn : -toRealVec ys ∈ (Interval.point (α := Vec 𝕋 k) (fun i => neg (ys i))).construct := by
    have h := Interval.mem_point (α := Vec 𝕋 k) (fun i => neg (ys i))
    rwa [show (RealImage.realImage (α := Vec 𝕋 k) (fun i => neg (ys i)) : Vec ℝ k)
      = -toRealVec ys from funext fun i => toReal_neg (ys i)] at h
  have hd := Interval.plus_outer Y _ (Set.add_mem_add hy hn)
  rwa [← sub_eq_add_neg] at hd

/-- `(J - A)(y - ys)` lies in `([J] - A)(Y - ys)`. -/
theorem aux_polyErr_jacTerm {k l : ℕ} {IJ : Interval (Mat 𝕋 k l)} {Y : Interval (Vec 𝕋 l)}
    (A : Mat 𝕋 k l) (ys : Vec 𝕋 l) {J : Mat ℝ k l} (hJ : J ∈ IJ.construct) {y : Vec ℝ l}
    (hy : y ∈ Y.construct) :
    (J - Scalar.toRealMat A) *ᵥ (y - toRealVec ys) ∈
      (Interval.mtimesIntervalMat (Interval.matPlus IJ (Interval.point (α := Mat 𝕋 k l)
        (fun i j => neg (A i j)))) (Interval.plus Y (Interval.point (α := Vec 𝕋 l)
          (fun i => neg (ys i))))).construct := by -- --- PROOF ---
  have hM := Interval.matPlus_outer IJ _ hJ (aux_polyErr_neg_mat A)
  rw [← sub_eq_add_neg] at hM
  exact Interval.mtimesIntervalMat_outer _ _
    (Set.mem_biUnion hM (Set.mem_image_of_mem _ (aux_polyErr_sub_mem ys hy)))

/-- A point of a box is no larger in magnitude than the box's `normMag`. -/
theorem aux_polyErr_abs_le {k : ℕ} {I : Interval (Vec 𝕋 k)} {y : Vec ℝ k} (hy : y ∈ I.construct)
    (j : Fin k) : |y j| ≤ toReal (I.normMag j) := by
  obtain ⟨h1, h2⟩ := hy j
  rw [Interval.normMag, toReal_maximum, toReal_absolute, toReal_absolute]
  exact abs_le_max_abs_abs h1 h2

/-- Bounds on two blocks bound their concatenation. -/
theorem aux_polyErr_abs_append {v : Vec ℝ n} {w : Vec ℝ m} {a : Vec 𝕋 n} {b : Vec 𝕋 m}
    (hv : ∀ j, |v j| ≤ toReal (a j)) (hw : ∀ j, |w j| ≤ toReal (b j)) :
    ∀ j, |Fin.append v w j| ≤ toReal ((Fin.append a b : Vec 𝕋 (n + m)) j) :=
  Fin.addCases (fun j => by simpa using hv j) (fun j => by simpa using hw j)

/-- A quadratic form at a vector padded by zeros reads only the leading block. -/
theorem aux_polyErr_append_zero (v : Vec ℝ n) (M : Mat ℝ (n + m) (n + m)) :
    Fin.append v (0 : Vec ℝ m) ⬝ᵥ (M *ᵥ Fin.append v (0 : Vec ℝ m))
      = v ⬝ᵥ (M.submatrix (Fin.castAdd m) (Fin.castAdd m) *ᵥ v) := by
  simp only [dotProduct, mulVec, Fin.sum_univ_add, Fin.append_left, Fin.append_right,
    Pi.zero_apply, mul_zero, zero_mul, Finset.sum_const_zero, add_zero, submatrix_apply]

/-- What `|q| ≤ L` says of `q / 2` against the symmetric box at `½ L`. -/
theorem aux_polyErr_half_mem {q : ℝ} {L : 𝕋} (hq : |q| ≤ toReal L) :
    toReal (neg (half L)) ≤ q / 2 ∧ q / 2 ≤ toReal (half L) := by
  rw [toReal_neg, toReal_half]
  obtain ⟨h1, h2⟩ := abs_le.mp hq
  constructor <;> linarith

/-- Four magnitudes bounded, their sum bounded by the sum rounded up. -/
theorem aux_polyErr_abs_sum4 {q₁ q₂ q₃ q₄ : ℝ} {b₁ b₂ b₃ b₄ : 𝕋} (h₁ : |q₁| ≤ toReal b₁)
    (h₂ : |q₂| ≤ toReal b₂) (h₃ : |q₃| ≤ toReal b₃) (h₄ : |q₄| ≤ toReal b₄) :
    |q₁ + q₂ + (q₃ + q₄)| ≤ toReal (addUp (addUp b₁ b₂) (addUp b₃ b₄)) := by -- --- PROOF ---
  have e₁ := add_le_addUp b₁ b₂
  have e₂ := add_le_addUp b₃ b₄
  have e₃ := add_le_addUp (addUp b₁ b₂) (addUp b₃ b₄)
  calc |q₁ + q₂ + (q₃ + q₄)| ≤ |q₁ + q₂| + |q₃ + q₄| := abs_add_le _ _
    _ ≤ (|q₁| + |q₂|) + (|q₃| + |q₄|) := add_le_add (abs_add_le _ _) (abs_add_le _ _)
    _ ≤ _ := by linarith


-- =======================================  MAIN THEOREM  ======================================= --

/-- Where `fm` encloses `sys` to second order, `(xs, us) ∈ X × U`, and a state `x ∈ X`
is `x(0) + δ` with `x(0) - x✱ ∈ Rdelta` and `δ ∈ Rdiff`, the remainder of the affine
split at `x` and any `u ∈ U` lies in `abstrErrPolyFloat`. -/
theorem NonlinearSys.FloatHessModel.Encloses.abstrErrPolyFloat_outer
    {fm : NonlinearSys.FloatHessModel 𝕋 n m} {sys : NonlinearSys n m} (h : fm.Encloses sys)
    (A : Mat 𝕋 n n) (B : Mat 𝕋 n m) {xs : Vec 𝕋 n} {us : Vec 𝕋 m} {X : Interval (Vec 𝕋 n)}
    {U : Interval (Vec 𝕋 m)} {Rdelta Rdiff : Zonotope (Vec 𝕋 n)} (hxs : toRealVec xs ∈ X.construct)
    (hus : toRealVec us ∈ U.construct) {x₀ x : Vec ℝ n} {u : Vec ℝ m} (hx : x ∈ X.construct)
    (hu : u ∈ U.construct) (hx₀ : x₀ - toRealVec xs ∈ Rdelta.construct)
    (hδ : x - x₀ ∈ Rdiff.construct) :
    sys.f x u - (sys.f (toRealVec xs) (toRealVec us)
        + Scalar.toRealMat A *ᵥ (x - toRealVec xs) + Scalar.toRealMat B *ᵥ (u - toRealVec us))
      ∈ (fm.abstrErrPolyFloat A B xs us X U Rdelta Rdiff).construct := by -- --- PROOF ---
  obtain ⟨Jx, hJx, Ju, hJu, H, hH, htay⟩ := h.taylor_mem X U xs us hxs hus x hx u hu
  set Hs := fun i => (fm.hess (Interval.point xs) (Interval.point us) i).centreMat with hHs
  set Q : Fin n → Mat 𝕋 n n := fun i j k => half (Hs i (Fin.castAdd m j) (Fin.castAdd m k))
  set dz := Fin.append (x - toRealVec xs) (u - toRealVec us)
  set z₀ : Vec ℝ (n + m) := Fin.append (x₀ - toRealVec xs) 0
  set δz : Vec ℝ (n + m) := Fin.append (x - x₀) (u - toRealVec us)
  set q : Vec ℝ n := fun i => dz ⬝ᵥ (H i *ᵥ dz) / 2
  set stat := Real.PolyZonotope.quadEval (fun k => toRealMat (Q k)) (x₀ - toRealVec xs)
  set lin := (Jx - Scalar.toRealMat A) *ᵥ (x - toRealVec xs)
    + (Ju - Scalar.toRealMat B) *ᵥ (u - toRealVec us)
  -- the remainder, rewritten through the expansion and split off its static part
  have hrem : sys.f x u - (sys.f (toRealVec xs) (toRealVec us)
      + Scalar.toRealMat A *ᵥ (x - toRealVec xs) + Scalar.toRealMat B *ᵥ (u - toRealVec us))
      = stat + (lin + (q - stat)) := by
    have hf : sys.f x u = sys.f (toRealVec xs) (toRealVec us)
        + (Jx *ᵥ (x - toRealVec xs) + Ju *ᵥ (u - toRealVec us) + q) := by
      rw [← htay]; abel
    rw [hf]
    simp only [lin, Matrix.sub_mulVec]
    abel
  rw [hrem]
  -- the static error at the start state, inside `quadMap` of the start set
  have hstat : stat ∈ (PolyZonotope.quadMap Q Rdelta.polyZonotope).zonotope.construct :=
    PolyZonotope.zonotope_contains _ (PolyZonotope.quadMap_outer Q _
      (Set.mem_image_of_mem _ (Rdelta.polyZonotope_contains hx₀)))
  refine Plus.plus_outer (PolyZonotope.quadMap Q Rdelta.polyZonotope).zonotope _
    (Set.add_mem_add hstat ?_)
  refine Interval.zonotope_contains _ (Interval.plus_outer _ _ (Set.add_mem_add
    (Interval.plus_outer _ _ (Set.add_mem_add (aux_polyErr_jacTerm A xs hJx hx)
      (aux_polyErr_jacTerm B us hJu hu))) ?_))
  intro i
  -- what is left of component `i`: four products, each carrying a bound
  have hdz : dz = z₀ + δz := by
    funext j
    refine Fin.addCases (fun j => ?_) (fun j => ?_) j <;> simp [dz, z₀, δz]
  have hsplit : q i - stat i = (z₀ ⬝ᵥ ((H i - toRealMat (Hs i)) *ᵥ z₀) + z₀ ⬝ᵥ (H i *ᵥ δz)
      + (δz ⬝ᵥ (H i *ᵥ z₀) + δz ⬝ᵥ (H i *ᵥ δz))) / 2 := by
    have hQ : toRealMat (Q i) = (2 : ℝ)⁻¹ • (toRealMat (Hs i)).submatrix (Fin.castAdd m)
        (Fin.castAdd m) := by
      funext j k
      simp only [toRealMat, Q, toReal_half, Matrix.smul_apply, submatrix_apply, smul_eq_mul]
      ring
    have hst : stat i = z₀ ⬝ᵥ (toRealMat (Hs i) *ᵥ z₀) / 2 := by
      show (x₀ - toRealVec xs) ⬝ᵥ (toRealMat (Q i) *ᵥ (x₀ - toRealVec xs)) = _
      rw [aux_polyErr_append_zero, hQ, smul_mulVec, dotProduct_smul, smul_eq_mul]
      ring
    show dz ⬝ᵥ (H i *ᵥ dz) / 2 - stat i = _
    rw [hst, hdz, Matrix.sub_mulVec]
    simp only [mulVec_add, dotProduct_add, add_dotProduct, dotProduct_sub]
    ring
  -- the magnitudes `|z₀|` and `|δz|`, and the Hessian's
  have hz₀ : ∀ j, |z₀ j| ≤ toReal ((Fin.append Rdelta.interval.normMag fun _ => zero :
      Vec 𝕋 (n + m)) j) :=
    aux_polyErr_abs_append (aux_polyErr_abs_le (Zonotope.interval_contains Rdelta hx₀))
      fun _ => by rw [toReal_zero]; simp
  have hδz : ∀ j, |δz j| ≤ toReal ((Fin.append Rdiff.interval.normMag
      (Interval.plus U (Interval.point fun i => neg (us i))).normMag : Vec 𝕋 (n + m)) j) :=
    aux_polyErr_abs_append (aux_polyErr_abs_le (Zonotope.interval_contains Rdiff hδ))
      (aux_polyErr_abs_le (aux_polyErr_sub_mem us hu))
  have hHabs : ∀ j k, |H i j k| ≤ toReal (maximum (absolute ((fm.hess X U i).inf j k))
      (absolute ((fm.hess X U i).sup j k))) := fun j k => by
    have hjk := hH i (j, k)
    simp only [Entrywise.entry_mat] at hjk
    rw [toReal_maximum, toReal_absolute, toReal_absolute]
    exact abs_le_max_abs_abs hjk.1 hjk.2
  have hHdev : ∀ j k, |(H i - toRealMat (Hs i)) j k| ≤ toReal (maximum
      (subUp ((fm.hess X U i).sup j k) (Hs i j k)) (subUp (Hs i j k) ((fm.hess X U i).inf j k))) :=
    fun j k => by
      -- `|M - c| ≤ max(sup - c, c - inf)` for `M` in the box, each difference rounded up
      have hjk := hH i (j, k)
      simp only [Entrywise.entry_mat] at hjk
      have h₁ : toReal ((fm.hess X U i).inf j k) ≤ H i j k := hjk.1
      have h₂ : H i j k ≤ toReal ((fm.hess X U i).sup j k) := hjk.2
      have e₁ := sub_le_subUp ((fm.hess X U i).sup j k) (Hs i j k)
      have e₂ := sub_le_subUp (Hs i j k) ((fm.hess X U i).inf j k)
      have m₁ := le_max_left (toReal (subUp ((fm.hess X U i).sup j k) (Hs i j k)))
        (toReal (subUp (Hs i j k) ((fm.hess X U i).inf j k)))
      have m₂ := le_max_right (toReal (subUp ((fm.hess X U i).sup j k) (Hs i j k)))
        (toReal (subUp (Hs i j k) ((fm.hess X U i).inf j k)))
      rw [toReal_maximum, abs_le]
      show _ ≤ H i j k - toReal (Hs i j k) ∧ H i j k - toReal (Hs i j k) ≤ _
      constructor <;> linarith
  -- the four products, each bounded by its `bilinUp`, halved
  have hmem := aux_polyErr_half_mem (aux_polyErr_abs_sum4 (abs_bilin_le_bilinUp hz₀ hz₀ hHdev)
    (abs_bilin_le_bilinUp hz₀ hδz hHabs) (abs_bilin_le_bilinUp hδz hz₀ hHabs)
    (abs_bilin_le_bilinUp hδz hδz hHabs))
  rw [← hsplit] at hmem
  exact hmem

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
