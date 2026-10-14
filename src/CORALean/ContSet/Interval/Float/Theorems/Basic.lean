module

public import CORALean.ContSet.Interval.Float.Interval
public import CORALean.ContSet.Interval.Float.Operations.Basic
public import CORALean.ContSet.Interval.Float.Operations.CenterBox
public import CORALean.ContSet.Interval.Float.Operations.Ctranspose
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


-- =============================  `Interval.center_mem_centerBox`  ============================== --
-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}

/-- The real midpoint of the stored bounds lies between `centerLo` and `center`. -/
theorem Interval.center_mem_centerBox (I : Interval (Vec 𝕋 n)) :
    I.nominal.center ∈ I.centerBox.construct :=
  fun i => ⟨I.centerLo_le i, I.center_ge i⟩

end CORALean.Float


-- ================================  `Interval.convHull_outer`  ================================= --
-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---

namespace CORALean.Float

open Pointwise FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}

/-- A box is convex, so it contains the convex hull of whatever the union of two boxes lies in. -/
theorem Interval.convHull_outer (I₁ I₂ : Interval (Vec 𝕋 n)) :
    convexHull ℝ (I₁.construct ∪ I₂.construct) ⊆ (I₁.convHull I₂).construct :=
  convexHull_min (Interval.or_outer I₁ I₂) (Real.Interval.convex_construct _)

end CORALean.Float


-- ===============================  `Interval.ctranspose_exact`  ================================ --
-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---

namespace CORALean.Float

open Pointwise FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {m n : ℕ}

/-- The same for the conjugate transpose, which over the reals a float reads as is the transpose. -/
theorem Interval.ctranspose_exact (I : Interval (Mat 𝕋 m n)) :
    I.ctranspose.construct = Matrix.conjTranspose '' I.construct :=
  Real.Interval.ctranspose_exact I.nominal

end CORALean.Float


-- ================================  `Interval.halve_minus_mem`  ================================ --
-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---

namespace CORALean.Float

open Matrix FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋]

/-- The difference is in the `Interval.minus` box, and `Interval.halve` is exact. -/
theorem Interval.halve_minus_mem {n : ℕ} {P Q : Interval (Vec 𝕋 n)} {x y : Vec ℝ n}
    (hx : x ∈ P.construct) (hy : y ∈ Q.construct) :
    (1 / 2 : ℝ) • (x - y) ∈ (Interval.halve (Interval.minus P Q)).construct :=
  Interval.halve_outer (Interval.minus_outer P Q (Set.sub_mem_sub hx hy))

end CORALean.Float


-- ================================  `Interval.halve_plus_mem`  ================================= --
-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---

namespace CORALean.Float

open Matrix FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋]

/-- The sum is in the `Interval.plus` box, and `Interval.halve` is exact. -/
theorem Interval.halve_plus_mem {n : ℕ} {P Q : Interval (Vec 𝕋 n)} {x y : Vec ℝ n}
    (hx : x ∈ P.construct) (hy : y ∈ Q.construct) :
    (1 / 2 : ℝ) • (x + y) ∈ (Interval.halve (Interval.plus P Q)).construct :=
  Interval.halve_outer (Interval.plus_outer P Q (Set.add_mem_add hx hy))

end CORALean.Float


-- ===================================  `Interval.Inf_exact`  =================================== --
-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}

/-- No bound is stored, so the box denotes all of `ℝⁿ`; nothing rounds. -/
theorem Interval.Inf_exact (n : ℕ) :
    (Interval.Inf n : Interval.EBox 𝕋 n).construct = Set.univ := by
  ext x
  simp [Interval.Inf, Interval.EBox.construct]

end CORALean.Float


-- =============================  `Interval.infimum_mem_construct`  ============================= --
-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---

namespace CORALean.Float

/-- Nonempty as the exact layer reads the stored bounds: `inf ≤ sup` coordinatewise. -/
theorem Interval.infimum_mem_construct {α β ι : Type} [RealImage α β] [AddCommGroup β]
    [Module ℝ β] [Entrywise β ι] (I : Interval α) (h : I.nominal.IsNonempty) :
    RealImage.realImage I.infimum ∈ I.construct :=
  Real.Interval.infimum_mem_construct I.nominal h

end CORALean.Float


-- ==================================  `Interval.mem_mat_iff`  ================================== --
-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---

namespace CORALean.Float

open SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {m n : ℕ}

/-- `Real.Interval.mem_mat_iff` read through `nominal`: both bounds are the stored
floats read as reals, so the statement needs no unfolding at the use site. -/
theorem Interval.mem_mat_iff {I : Interval (Mat 𝕋 m n)} {A : Mat ℝ m n} :
    A ∈ I.construct ↔ ∀ i j, toReal (I.inf i j) ≤ A i j ∧ A i j ≤ toReal (I.sup i j) :=
  ⟨fun h i j => h (i, j), fun h p => h p.1 p.2⟩

end CORALean.Float


-- ====================================  `Interval.norm_le`  ==================================== --
-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}

/-- With a certificate `σ`, every member of the box has Euclidean norm at most `|σ|`. -/
theorem Interval.norm_le (I : Interval (Vec 𝕋 n)) {σ : 𝕋}
    (hσ : toReal I.normSq ≤ toReal (mulDown σ σ)) {x : Vec ℝ n} (hx : x ∈ I.construct) :
    ‖x‖₂ ≤ toReal (absolute σ) :=
  le_trans (Real.Interval.norm_le (I := I.nominal) hx) (I.norm_nominal_le hσ)

end CORALean.Float


-- ================================  `Interval.reindex_nominal`  ================================ --
-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   05-September-2026
-- Reviewed:      ---

namespace CORALean.Float

open SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n m : ℕ}

/-- Nothing rounds, so this is `rfl`. -/
theorem Interval.reindex_nominal (e : Fin m ≃ Fin n) (I : Interval (Vec 𝕋 n)) :
    (I.reindex e).nominal = I.nominal.reindex e := rfl

end CORALean.Float


-- ============================  `Interval.supremum_mem_construct`  ============================= --
-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---

namespace CORALean.Float

/-- Nonempty as the exact layer reads the stored bounds: `inf ≤ sup` coordinatewise. -/
theorem Interval.supremum_mem_construct {α β ι : Type} [RealImage α β] [AddCommGroup β]
    [Module ℝ β] [Entrywise β ι] (I : Interval α) (h : I.nominal.IsNonempty) :
    RealImage.realImage I.supremum ∈ I.construct :=
  Real.Interval.supremum_mem_construct I.nominal h

end CORALean.Float


-- ==================================  `Interval.times_outer`  ================================== --
-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---

namespace CORALean.Float

open Pointwise FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}

/-- Each coordinate is `Float.Interval.mul_between_corners`, which already pays the rounding. -/
theorem Interval.times_outer (I J : Interval (Vec 𝕋 n)) :
    Set.image2 (fun x y i => x i * y i) I.construct J.construct ⊆ (I.times J).construct := by
  rintro _ ⟨x, hx, y, hy, rfl⟩ i
  exact Interval.mul_between_corners (hx i).1 (hx i).2 (hy i).1 (hy i).2

end CORALean.Float


-- ==================================  `Interval.uplus_exact`  ================================== --
-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---

namespace CORALean.Float

/-- The set is unchanged, definitionally. -/
theorem Interval.uplus_exact {α β ι : Type} [RealImage α β] [AddCommGroup β] [Module ℝ β]
    [Entrywise β ι] (I : Interval α) : I.uplus.construct = I.construct := rfl

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
