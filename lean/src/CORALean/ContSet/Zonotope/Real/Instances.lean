import CORALean.ContSet.Zonotope.Real.Theorems.API

/-!
# What `Zonotope` instantiates

The class fields *are* the obligations, so there is nothing to restate. Each is a
theorem from `Theorems`: the two exact ones give their `⊆` direction, and
`reduce_outer` is already one.

Noncomputable, as `reduce` is: it ranks generators, and ordering reals cannot be
computed.
-/

-- Authors:       Tobias Ladner
-- Written:       18-August-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Real

open Matrix

variable {n : ℕ}

/-- At every ambient type, not only `Vec`: what a zonotope denotes needs no
coordinates. `OuterContSet` below stays at `Vec`, because `reduce` does. -/
instance {α : Type} [AddCommGroup α] [Module ℝ α] : ContSet (Zonotope α) α :=
  ⟨Zonotope.construct⟩

noncomputable instance : OuterContSet (Zonotope (Vec ℝ n)) (Vec ℝ n) where
  plus := Zonotope.plus
  linComb := Zonotope.linComb
  reduce := Zonotope.reduce
  plus_outer Z₁ Z₂ := (Zonotope.plus_exact Z₁ Z₂).subset
  linComb_outer := Zonotope.linComb_outer
  reduce_outer := Zonotope.reduce_outer

instance : Mtimes (Mat ℝ) (fun n => Zonotope (Vec ℝ n)) where
  mtimes := Zonotope.mtimes
  mtimes_outer M Z := by
    simp only [ContSet.construct_mat, Scalar.toRealMat_real, Set.biUnion_singleton]
    exact (Zonotope.mtimes_exact M Z).subset

set_option maxHeartbeats 400000 in
/-- Multiplication by a plain matrix at any ambient type it acts on. At `Vec`
this repeats `mtimes`; at `Mat` it is matrix multiplication of a matrix
zonotope, which needs no development of its own. -/
instance {𝕋 : Type} [Scalar 𝕋] {p q : ℕ} :
    LinMtimes (Mat 𝕋 p q) (Zonotope (Vec ℝ q)) (Zonotope (Vec ℝ p)) (Vec ℝ q) (Vec ℝ p) where
  lmtimes M Z := Zonotope.mapOf (Matrix.mulVecLin (Scalar.toRealMat M)) Z
  lmtimes_outer _M Z := Zonotope.lmtimes_singleton_outer _ Z

set_option maxHeartbeats 400000 in
instance {𝕋 : Type} [Scalar 𝕋] {p q r : ℕ} :
    LinMtimes (Mat 𝕋 p q) (Zonotope (Mat ℝ q r)) (Zonotope (Mat ℝ p r))
      (Mat ℝ q r) (Mat ℝ p r) where
  lmtimes M Z := Zonotope.mapOf (matMulLeft (Scalar.toRealMat M)) Z
  lmtimes_outer _M Z := Zonotope.lmtimes_singleton_outer _ Z

/-- The same operation at an interval matrix, which `OuterContSet` does not ask
for: a zonotope carries it, and a discretization is what wants it. -/
noncomputable instance : Mtimes IntervalMat (fun n => Zonotope (Vec ℝ n)) where
  mtimes := Zonotope.mtimesIntervalMat
  mtimes_outer IM Z := by
    simp only [IntervalMat.construct_eq]
    exact Zonotope.mtimesIntervalMat_outer IM Z

end CORALean.Real
