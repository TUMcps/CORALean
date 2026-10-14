module

public import CORALean.ContSet.ProbZonotope.Float.Operations.Enclose
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.ExpIntervalEnclosureFloat
public import CORALean.ContSet.Interval.Float.Theorems.MatPlusOuter
public import CORALean.ContSet.Interval.Float.Theorems.Basic
public import CORALean.ContSet.Interval.Float.Theorems.MemPoint
public import CORALean.ContSet.Zonotope.Float.Theorems.ConstructPoint
public import CORALean.ContSet.Zonotope.Float.Theorems.LinCombOuter
public import CORALean.ContSet.Zonotope.Float.Theorems.MtimesIntervalMatOuter
public import CORALean.ContSet.Zonotope.Float.Theorems.PlusOuter

@[expose] public section

/-!
# The float mean zonotope of `enclose` contains the segments from `μ` to `e^{Ar} μ + Rtrans`

`Real.ProbZonotope.enclose_mean_outer` for the float operation, with the real `e^{Ar}`: for every
mean `μ` of `probZ` and `a ∈ [0, 1]`, the float mean zonotope of `enclose(probZ, Ar)` contains
`a μ + (1 - a)(e^{Ar} μ + Rtrans)`, at a Taylor order `η` whose remainder bound is admissible
(`MatExp.exp_mem_expIntervalEnclosure`). Outer, for the means only; what it says of the
covariance is nothing.
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Matrix FloatOps SoundFloatArithmetic
open scoped Pointwise

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem ProbZonotope.enclose_mean_outer (P : ProbZonotope 𝕋 n) (Ar : Mat 𝕋 n n) {η : ℕ}
    (hη : toReal (MatExp.normUpperBound (Interval.point Ar)) / ((η : ℝ) + 2) ≤ 1 / 2)
    (Rtrans : Vec 𝕋 n) {μ : Vec ℝ n} (hμ : μ ∈ P.Z.construct) {a : ℝ}
    (ha : a ∈ Set.Icc (0 : ℝ) 1) :
    a • μ + (1 - a) • (NormedSpace.exp (toRealMat Ar) *ᵥ μ + toRealVec Rtrans)
      ∈ (P.enclose Ar η Rtrans).Z.construct := by -- --- PROOF ---
  -- `e^{Ar}` in its float enclosure, and `e^{Ar} - I` in the sum with the point `-I`
  have hE : NormedSpace.exp (toRealMat Ar)
      ∈ (MatExp.expIntervalEnclosure (Interval.point Ar) η).construct :=
    MatExp.exp_mem_expIntervalEnclosure _ η (Interval.mem_point Ar) hη
  have hI : (-1 : Mat ℝ n n)
      ∈ (Interval.point (diagonalBlock fun _ : Fin n => neg (one : 𝕋))).construct := by
    refine Interval.mem_mat_iff.mpr fun i j => ?_
    have e : toReal (diagonalBlock (fun _ : Fin n => neg (one : 𝕋)) i j)
        = (-1 : Mat ℝ n n) i j := by
      rw [toReal_diagonalBlock]
      by_cases hij : i = j
      · subst hij; simp [toRealVec, toReal_neg, toReal_one]
      · simp [hij, Matrix.one_apply_ne hij]
    exact ⟨e.le, e.ge⟩
  have hEI := Interval.matPlus_outer _ _ hE hI
  -- `(e^{Ar} - I) μ + Rtrans` in `Zaux`
  have hz : (NormedSpace.exp (toRealMat Ar) + -1) *ᵥ μ + toRealVec Rtrans
      ∈ ((Zonotope.mtimesIntervalMat _ P.Z).plus (Zonotope.point Rtrans)).construct :=
    Zonotope.plus_outer _ _ (Set.add_mem_add
      (Zonotope.mtimesIntervalMat_outer _ P.Z (Set.mem_biUnion hEI ⟨μ, hμ, rfl⟩))
      (by rw [Zonotope.construct_point]; rfl))
  -- the segment from `0` to it in `deltaZ`
  have h0 : (0 : Vec ℝ n) ∈ (Zonotope.point fun _ : Fin n => (zero : 𝕋)).construct := by
    rw [Zonotope.construct_point]
    funext i
    simp [toRealVec, toReal_zero]
  have hd := Zonotope.linComb_outer _ _ ⟨0, h0, _, hz, a, ha, rfl⟩
  have hsum := Zonotope.plus_outer _ _ (Set.add_mem_add hμ hd)
  -- the point is `μ` plus a point of `deltaZ`
  have e : a • μ + (1 - a) • (NormedSpace.exp (toRealMat Ar) *ᵥ μ + toRealVec Rtrans)
      = μ + (a • (0 : Vec ℝ n) + (1 - a) • ((NormedSpace.exp (toRealMat Ar) + -1) *ᵥ μ
        + toRealVec Rtrans)) := by
    rw [add_mulVec, neg_mulVec, one_mulVec, smul_zero, zero_add]
    module
  rw [e]
  exact hsum

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
