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
public import CORALean.ContSet.Interval.Real.Theorems.Convex
public import CORALean.ContSet.Interval.Real.Theorems.CtransposeExact
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
    I.nominal.center ∈ I.centerBox.construct :=
  fun i => ⟨I.centerLo_le i, I.center_ge i⟩


-- ================================  `Interval.convHull_outer`  ================================= --
-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- A box is convex, so it contains the convex hull of whatever the union of two boxes lies in. -/
theorem Interval.convHull_outer (I₁ I₂ : Interval (Vec 𝕋 n)) :
    convexHull ℝ (I₁.construct ∪ I₂.construct) ⊆ (I₁.convHull I₂).construct :=
  convexHull_min (Interval.or_outer I₁ I₂) (Real.Interval.convex_construct _)


-- ===============================  `Interval.ctranspose_exact`  ================================ --
-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- The same for the conjugate transpose, which over the reals a float reads as is the transpose. -/
theorem Interval.ctranspose_exact (I : Interval (Mat 𝕋 m n)) :
    I.ctranspose.construct = Matrix.conjTranspose '' I.construct :=
  Real.Interval.ctranspose_exact I.nominal


-- ================================  `Interval.halve_minus_mem`  ================================ --
-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- The difference is in the `Interval.minus` box, and `Interval.halve` is exact. -/
theorem Interval.halve_minus_mem {n : ℕ} {P Q : Interval (Vec 𝕋 n)} {x y : Vec ℝ n}
    (hx : x ∈ P.construct) (hy : y ∈ Q.construct) :
    (1 / 2 : ℝ) • (x - y) ∈ (Interval.halve (Interval.minus P Q)).construct :=
  Interval.halve_outer (Interval.minus_outer P Q (Set.sub_mem_sub hx hy))


-- ================================  `Interval.halve_plus_mem`  ================================= --
-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- The sum is in the `Interval.plus` box, and `Interval.halve` is exact. -/
theorem Interval.halve_plus_mem {n : ℕ} {P Q : Interval (Vec 𝕋 n)} {x y : Vec ℝ n}
    (hx : x ∈ P.construct) (hy : y ∈ Q.construct) :
    (1 / 2 : ℝ) • (x + y) ∈ (Interval.halve (Interval.plus P Q)).construct :=
  Interval.halve_outer (Interval.plus_outer P Q (Set.add_mem_add hx hy))


-- ===================================  `Interval.Inf_exact`  =================================== --
-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- No bound is stored, so the box denotes all of `ℝⁿ`; nothing rounds. -/
theorem Interval.Inf_exact (n : ℕ) :
    (Interval.Inf n : Interval.EBox 𝕋 n).construct = Set.univ := by
  ext x
  simp [Interval.Inf, Interval.EBox.construct]


-- =============================  `Interval.infimum_mem_construct`  ============================= --
-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- Nonempty as the exact layer reads the stored bounds: `inf ≤ sup` coordinatewise. -/
theorem Interval.infimum_mem_construct {α β ι : Type} [RealImage α β] [AddCommGroup β]
    [Module ℝ β] [Entrywise β ι] (I : Interval α) (h : I.nominal.IsNonempty) :
    RealImage.realImage I.infimum ∈ I.construct :=
  Real.Interval.infimum_mem_construct I.nominal h


-- ==================================  `Interval.mem_mat_iff`  ================================== --
-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `Real.Interval.mem_mat_iff` read through `nominal`: both bounds are the stored
floats read as reals, so the statement needs no unfolding at the use site. -/
theorem Interval.mem_mat_iff {I : Interval (Mat 𝕋 m n)} {A : Mat ℝ m n} :
    A ∈ I.construct ↔ ∀ i j, toReal (I.inf i j) ≤ A i j ∧ A i j ≤ toReal (I.sup i j) :=
  ⟨fun h i j => h (i, j), fun h p => h p.1 p.2⟩


-- ==================================  `Interval.mem_vec_iff`  ================================== --
-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- A box of vectors, read coordinate by coordinate: both bounds are the stored floats read as
reals, so the statement needs no unfolding at the use site. -/
theorem Interval.mem_vec_iff {I : Interval (Vec 𝕋 n)} {x : Vec ℝ n} :
    x ∈ I.construct ↔ ∀ j, toReal (I.inf j) ≤ x j ∧ x j ≤ toReal (I.sup j) :=
  Iff.rfl


-- ====================================  `Interval.norm_le`  ==================================== --
-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- With a certificate `σ`, every member of the box has Euclidean norm at most `|σ|`. -/
theorem Interval.norm_le (I : Interval (Vec 𝕋 n)) {σ : 𝕋}
    (hσ : toReal I.normSq ≤ toReal (mulDown σ σ)) {x : Vec ℝ n} (hx : x ∈ I.construct) :
    ‖x‖₂ ≤ toReal (absolute σ) :=
  le_trans (Real.Interval.norm_le (I := I.nominal) hx) (I.norm_nominal_le hσ)


-- ============================  `Interval.supremum_mem_construct`  ============================= --
-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- Nonempty as the exact layer reads the stored bounds: `inf ≤ sup` coordinatewise. -/
theorem Interval.supremum_mem_construct {α β ι : Type} [RealImage α β] [AddCommGroup β]
    [Module ℝ β] [Entrywise β ι] (I : Interval α) (h : I.nominal.IsNonempty) :
    RealImage.realImage I.supremum ∈ I.construct :=
  Real.Interval.supremum_mem_construct I.nominal h


-- ==================================  `Interval.times_outer`  ================================== --
-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- Each coordinate is `Float.Interval.mul_between_corners`, which already pays the rounding. -/
theorem Interval.times_outer (I J : Interval (Vec 𝕋 n)) :
    Set.image2 (fun x y i => x i * y i) I.construct J.construct ⊆ (I.times J).construct := by
  rintro _ ⟨x, hx, y, hy, rfl⟩ i
  exact Interval.mul_between_corners (hx i).1 (hx i).2 (hy i).1 (hy i).2


-- ==================================  `Interval.uplus_exact`  ================================== --
-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- The set is unchanged, definitionally. -/
theorem Interval.uplus_exact {α β ι : Type} [RealImage α β] [AddCommGroup β] [Module ℝ β]
    [Entrywise β ι] (I : Interval α) : I.uplus.construct = I.construct := rfl

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
