module

public import CORALean.ContSet.Interval.Float.Interval
public import CORALean.ContSet.Interval.Float.Operations.Basic
public import CORALean.ContSet.Interval.Float.Operations.CenterBox
public import CORALean.ContSet.Interval.Float.Operations.Ctranspose
public import CORALean.ContSet.Interval.Float.Operations.Materialise
public import CORALean.ContSet.Interval.Float.Operations.MaterialiseMat
public import CORALean.ContSet.Interval.Float.Operations.Reindex
public import CORALean.ContSet.Interval.Float.Operations.Times
public import CORALean.ContSet.Interval.Float.Theorems.CenterGe
public import CORALean.ContSet.Interval.Float.Theorems.CenterLoLe
public import CORALean.ContSet.Interval.Float.Theorems.HalveOuter
public import CORALean.ContSet.Interval.Float.Theorems.MinusOuter
public import CORALean.ContSet.Interval.Float.Theorems.MulBetweenCorners
public import CORALean.ContSet.Interval.Float.Theorems.NormNominalLe
public import CORALean.ContSet.Interval.Float.Theorems.OrOuter
public import CORALean.ContSet.Interval.Float.Theorems.PlusOuter
public import CORALean.ContSet.Interval.Real.Operations.Reindex
public import CORALean.ContSet.Interval.Real.Theorems.Basic
public import CORALean.ContSet.Interval.Real.Theorems.MemRepVecIff
public import CORALean.ContSet.Interval.Real.Theorems.Convex
public import CORALean.ContSet.Interval.Real.Theorems.CtransposeExact
public import CORALean.Global.Float.GenBlockDiag
public import Mathlib.Analysis.Convex.Hull

@[expose] public section

/-!
# `ContSet/Interval/Float/Theorems`: small declarations

One section per declaration, at most five code lines each; alphabetical, after the
sections each one uses (CONTRIBUTING, "Small declarations").
-/


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

section

open FloatOps SoundFloatArithmetic Pointwise Matrix

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {m n : ℕ}


-- =============================  `Interval.center_mem_centerBox`  ============================== --
-- Authors:       Claude Opus 5.5, Claude Sonnet 5.5
-- Written:       02-October-2026
-- Last update:   15-October-2026
-- Reviewed:      ---

/-- The real midpoint of the stored bounds lies between `centerLo` and `center`. -/
theorem Interval.center_mem_centerBox (I : Interval (Vec 𝕋 n)) :
    I.nominal.center ∈ I.centerBox.toSet :=
  fun i => ⟨I.centerLo_le i, I.center_ge i⟩


-- =================================  `Interval.convex_toSet`  ================================== --
-- Authors:       Claude Sonnet 5.5
-- Written:       26-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- The set of a float interval is the nominal one's, which is convex. -/
theorem Interval.convex_toSet {α β ι : Type} [RealImage α β] [AddCommGroup β] [Module ℝ β]
    [Entrywise β ι] (I : Interval α) : Convex ℝ I.toSet :=
  I.nominal.convex_toSet


-- ================================  `Interval.convHull_outer`  ================================= --
-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- A box is convex, so it contains the convex hull of whatever the union of two boxes lies in. -/
theorem Interval.convHull_outer (I₁ I₂ : Interval (Vec 𝕋 n)) :
    convexHull ℝ (I₁.toSet ∪ I₂.toSet) ⊆ (I₁.convHull I₂).toSet :=
  convexHull_min (Interval.or_outer I₁ I₂) (Real.Interval.convex_toSet _)


-- ===============================  `Interval.ctranspose_exact`  ================================ --
-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- The same for the conjugate transpose, which over the reals a float reads as is the transpose. -/
theorem Interval.ctranspose_exact (I : Interval (Mat 𝕋 m n)) :
    I.ctranspose.toSet = Matrix.conjTranspose '' I.toSet :=
  Real.Interval.ctranspose_exact I.nominal


-- ================================  `Interval.halve_minus_mem`  ================================ --
-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- The difference is in the `Interval.minus` box, and `Interval.halve` is exact. -/
theorem Interval.halve_minus_mem {n : ℕ} {P Q : Interval (Vec 𝕋 n)} {x y : Vec ℝ n}
    (hx : x ∈ P.toSet) (hy : y ∈ Q.toSet) :
    (1 / 2 : ℝ) • (x - y) ∈ (Interval.halve (Interval.minus P Q)).toSet :=
  Interval.halve_outer (Interval.minus_outer P Q (Set.sub_mem_sub hx hy))


-- ================================  `Interval.halve_plus_mem`  ================================= --
-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- The sum is in the `Interval.plus` box, and `Interval.halve` is exact. -/
theorem Interval.halve_plus_mem {n : ℕ} {P Q : Interval (Vec 𝕋 n)} {x y : Vec ℝ n}
    (hx : x ∈ P.toSet) (hy : y ∈ Q.toSet) :
    (1 / 2 : ℝ) • (x + y) ∈ (Interval.halve (Interval.plus P Q)).toSet :=
  Interval.halve_outer (Interval.plus_outer P Q (Set.add_mem_add hx hy))


-- ===================================  `Interval.Inf_exact`  =================================== --
-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- No bound is stored, so the box denotes all of `ℝⁿ`; nothing rounds. -/
theorem Interval.Inf_exact (n : ℕ) :
    (Interval.Inf n : Interval.EBox 𝕋 n).toSet = Set.univ := by
  ext x
  simp [Interval.Inf, Interval.EBox.toSet]


-- ===============================  `Interval.infimum_mem_toSet`  =============================== --
-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- Nonempty as the exact layer reads the stored bounds: `inf ≤ sup` coordinatewise. -/
theorem Interval.infimum_mem_toSet {α β ι : Type} [RealImage α β] [AddCommGroup β]
    [Module ℝ β] [Entrywise β ι] (I : Interval α) (h : I.nominal.IsNonempty) :
    RealImage.realImage I.infimum ∈ I.toSet :=
  Real.Interval.infimum_mem_toSet I.nominal h


-- ==================================  `Interval.mem_mat_iff`  ================================== --
-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `Real.Interval.mem_mat_iff` read through `nominal`: both bounds are the stored
floats read as reals, so the statement needs no unfolding at the use site. -/
theorem Interval.mem_mat_iff {I : Interval (Mat 𝕋 m n)} {A : Mat ℝ m n} :
    A ∈ I.toSet ↔ ∀ i j, toReal (I.inf i j) ≤ A i j ∧ A i j ≤ toReal (I.sup i j) :=
  ⟨fun h i j => h (i, j), fun h p => h p.1 p.2⟩


-- ================================  `Interval.mem_repVec_iff`  ================================= --
-- Authors:       Claude Opus 5.5
-- Written:       19-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- A point of a repeated box is one whose every block lies in the box; nothing rounds. -/
theorem Interval.mem_repVec_iff (a : ℕ) (I : Interval (Vec 𝕋 n)) (x : Vec ℝ (a * n)) :
    x ∈ (I.repVec a).toSet ↔ ∀ j, (fun k => x (finProdFinEquiv (j, k))) ∈ I.toSet :=
  Real.Interval.mem_repVec_iff a I.nominal x


-- ==================================  `Interval.mem_vec_iff`  ================================== --
-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- A box of vectors, read coordinate by coordinate: both bounds are the stored floats read as
reals, so the statement needs no unfolding at the use site. -/
theorem Interval.mem_vec_iff {I : Interval (Vec 𝕋 n)} {x : Vec ℝ n} :
    x ∈ I.toSet ↔ ∀ j, toReal (I.inf j) ≤ x j ∧ x j ≤ toReal (I.sup j) :=
  Iff.rfl


-- ================================  `Interval.nominal_append`  ================================= --
-- Authors:       Claude Opus 5.5
-- Written:       19-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- The stored boxes appended read back as the read-back boxes appended: the bounds are copied. -/
theorem Interval.nominal_append {n₁ n₂ : ℕ} (I₁ : Interval (Vec 𝕋 n₁)) (I₂ : Interval (Vec 𝕋 n₂)) :
    (I₁.append I₂).nominal = I₁.nominal.append I₂.nominal :=
  congrArg₂ Real.Interval.mk (toRealVec_append I₁.inf I₂.inf) (toRealVec_append I₁.sup I₂.sup)


-- =================================  `Interval.nominal_unit`  ================================== --
-- Authors:       Claude Opus 5.5
-- Written:       19-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- The stored unit box reads back as the exact one: `-1` and `1` round to themselves. -/
theorem Interval.nominal_unit (n : ℕ) :
    (Interval.unit n : Interval (Vec 𝕋 n)).nominal = Real.Interval.unit n :=
  congrArg₂ Real.Interval.mk (funext fun _ => (toReal_neg _).trans (by rw [toReal_one]))
    (funext fun _ => toReal_one)


-- =================================  `Interval.mem_unit_iff`  ================================== --
-- Authors:       Claude Opus 5.5
-- Written:       19-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- A point of the stored unit box is one whose every coordinate has modulus at most `1`. -/
theorem Interval.mem_unit_iff (x : Vec ℝ n) :
    x ∈ (Interval.unit n : Interval (Vec 𝕋 n)).toSet ↔ ∀ k, |x k| ≤ 1 := by
  rw [Interval.toSet, Interval.nominal_unit]
  exact Real.Interval.mem_unit_iff x


-- ====================================  `Interval.norm_le`  ==================================== --
-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- With a certificate `σ`, every member of the box has Euclidean norm at most `|σ|`. -/
theorem Interval.norm_le (I : Interval (Vec 𝕋 n)) {σ : 𝕋}
    (hσ : toReal I.normSq ≤ toReal (mulDown σ σ)) {x : Vec ℝ n} (hx : x ∈ I.toSet) :
    ‖x‖₂ ≤ toReal (absolute σ) :=
  le_trans (Real.Interval.norm_le (I := I.nominal) hx) (I.norm_nominal_le hσ)


-- ==============================  `Interval.supremum_mem_toSet`  =============================== --
-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- Nonempty as the exact layer reads the stored bounds: `inf ≤ sup` coordinatewise. -/
theorem Interval.supremum_mem_toSet {α β ι : Type} [RealImage α β] [AddCommGroup β]
    [Module ℝ β] [Entrywise β ι] (I : Interval α) (h : I.nominal.IsNonempty) :
    RealImage.realImage I.supremum ∈ I.toSet :=
  Real.Interval.supremum_mem_toSet I.nominal h


-- ==================================  `Interval.times_outer`  ================================== --
-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- Each coordinate is `Float.Interval.mul_between_corners`, which already pays the rounding. -/
theorem Interval.times_outer (I J : Interval (Vec 𝕋 n)) :
    Set.image2 (fun x y i => x i * y i) I.toSet J.toSet ⊆ (I.times J).toSet := by
  rintro _ ⟨x, hx, y, hy, rfl⟩ i
  exact Interval.mul_between_corners (hx i).1 (hx i).2 (hy i).1 (hy i).2


-- ===============================  `Interval.toReal_eq_nominal`  =============================== --
-- Authors:       Claude Opus 5.5
-- Written:       11-November-2026
-- Last update:   ---
-- Reviewed:      ---

/-- A float interval has no error box, so its real interval is its nominal. -/
theorem Interval.toReal_eq_nominal {α β : Type} [RealImage α β] (I : Interval α) :
    I.toReal = I.nominal := rfl


-- ==================================  `Interval.uplus_exact`  ================================== --
-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- The set is unchanged, definitionally. -/
theorem Interval.uplus_exact {α β ι : Type} [RealImage α β] [AddCommGroup β] [Module ℝ β]
    [Entrywise β ι] (I : Interval α) : I.uplus.toSet = I.toSet := rfl

end


section

open SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- ================================  `Interval.materialise_eq`  ================================= --
-- Authors:       Claude Opus 5
-- Written:       16-August-2026
-- Last update:   14-October-2026
-- Reviewed:      ---

omit [FloatOps 𝕋] in
/-- `materialise` is the identity: it changes only what running the definition costs. -/
@[simp] theorem Interval.materialise_eq (I : Interval (Vec 𝕋 n)) : I.materialise = I := by
  simp [Interval.materialise]


-- ===============================  `Interval.unit_append_unit`  ================================ --
-- Authors:       Claude Opus 5.5
-- Written:       19-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- Two stored unit boxes side by side are the unit box of both blocks. -/
theorem Interval.unit_append_unit (n₁ n₂ : ℕ) : (Interval.unit n₁ : Interval (Vec 𝕋 n₁)).append
    (Interval.unit n₂) = Interval.unit (n₁ + n₂) := by
  simp only [Interval.append, Interval.unit, Interval.mk.injEq]
  exact ⟨funext (Fin.addCases (by simp) (by simp)), funext (Fin.addCases (by simp) (by simp))⟩


-- ================================  `Interval.append_eq_unit`  ================================= --
-- Authors:       Claude Opus 5.5
-- Written:       19-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- Two stored boxes that are unit boxes, side by side, are the unit box of both blocks. -/
theorem Interval.append_eq_unit {n₁ n₂ : ℕ} {I₁ : Interval (Vec 𝕋 n₁)} {I₂ : Interval (Vec 𝕋 n₂)}
    (h₁ : I₁ = Interval.unit n₁) (h₂ : I₂ = Interval.unit n₂) :
    I₁.append I₂ = Interval.unit (n₁ + n₂) := by
  rw [h₁, h₂, Interval.unit_append_unit]

end


section

open SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}
variable {m : ℕ}


-- ===============================  `Interval.materialiseMat_eq`  =============================== --
-- Authors:       Claude Opus 5
-- Written:       16-August-2026
-- Last update:   14-October-2026
-- Reviewed:      ---

omit [FloatOps 𝕋] in
/-- `materialiseMat` is the identity: it changes only what running the definition costs. -/
@[simp] theorem Interval.materialiseMat_eq (I : Interval (Mat 𝕋 m n)) :
    I.materialiseMat = I := by
  simp [Interval.materialiseMat]

end


section

open SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n m : ℕ}


-- ================================  `Interval.reindex_nominal`  ================================ --
-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   05-September-2026
-- Reviewed:      ---

/-- Nothing rounds, so this is `rfl`. -/
theorem Interval.reindex_nominal (e : Fin m ≃ Fin n) (I : Interval (Vec 𝕋 n)) :
    (I.reindex e).nominal = I.nominal.reindex e := rfl

end

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
