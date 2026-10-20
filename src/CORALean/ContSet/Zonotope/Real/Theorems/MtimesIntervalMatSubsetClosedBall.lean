module

public import CORALean.ContSet.Interval.Real.Operations.Basic
public import CORALean.ContSet.Zonotope.Real.Operations.MtimesIntervalMat
public import CORALean.ContSet.Zonotope.Real.Theorems.AbsLeAbsBound
public import CORALean.ContSet.Zonotope.Real.Theorems.MemConstruct
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Tactic.Positivity

@[expose] public section

/-!
# An interval matrix of small entries moves a zonotope only a little

How far the result of `mtimesIntervalMat` reaches, measured against the entries of the interval
matrix rather than against the matrices it denotes: a bound on the center and one on the radius,
each against the operand's `ℓ¹` reach `∑ⱼ absBound j`, which both the boxed generators and the
center's rows are summed over. The direction is the one an error measure needs —
`mtimesIntervalMat_outer` bounds the operation from below. The radius is what the boxed generators
carry and the center what the ordinary ones do, so the two bounds enter the total additively:
`inputRemainder` has center zero and pays only `ρr`, while `correctionMatrix` pays both.

## Inputs
* `ρc` – center entry bound
* `ρr` – radius entry bound
* `IM` – interval matrix
* `Z` – zonotope

## Hypotheses
* `hρc` – center bound nonnegative
* `hρr` – radius bound nonnegative
* `hc` – center entries bounded
* `hr` – radius entries bounded

## Conclusion
* the product lies in a ball of the stated radius
-/

-- Authors:       Claude Opus 5
-- Written:       08-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {m n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- `Fin.sum_univ_add` at this operation's generator count, stated through the
projection because that is the form the goal has. -/
theorem Zonotope.aux_sum_univ_mtimesIntervalMatBall {IM : Interval (Mat ℝ m n)}
    {Z : Zonotope (Vec ℝ n)} (f : Fin (Z.h + m) → ℝ) :
    ∑ j : Fin (Zonotope.mtimesIntervalMat IM Z).h, f j
      = ∑ j, f (Fin.castAdd m j) + ∑ j, f (Fin.natAdd Z.h j) :=
  Fin.sum_univ_add f

/-- A diagonal block read down a column, under an absolute value. -/
theorem Zonotope.aux_sum_diagonal_abs (v : Vec ℝ m) (i : Fin m) : -- --- CONCL ---
    ∑ l, |Matrix.diagonal v l i| = |v i| := by -- --- PROOF ---
  rw [Finset.sum_eq_single i, Matrix.diagonal_apply_eq]
  · intro b _ hb
    rw [Matrix.diagonal_apply_ne _ hb, abs_zero]
  · intro hi
    exact absurd (Finset.mem_univ i) hi

/-- A row of the center against a vector, in terms of that vector's `ℓ¹` size. -/
theorem Zonotope.aux_abs_center_mulVec_le {ρc : ℝ} {IM : Interval (Mat ℝ m n)}
    (hc : ∀ i j, |IM.center i j| ≤ ρc) (v : Vec ℝ n) (i : Fin m) : -- --- CONCL ---
    |(IM.center *ᵥ v) i| ≤ ρc * ∑ j, |v j| := by -- --- PROOF ---
  have hrow : (IM.center *ᵥ v) i = ∑ j, IM.center i j * v j := rfl
  calc |(IM.center *ᵥ v) i|
      = |∑ j, IM.center i j * v j| := by rw [hrow]
    _ ≤ ∑ j, |IM.center i j * v j| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j, ρc * |v j| := Finset.sum_le_sum fun j _ => by
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_right (hc i j) (abs_nonneg _)
    _ = ρc * ∑ j, |v j| := by rw [Finset.mul_sum]

/-- Every coordinate of the product reaches no further than the two entry
bounds together, against the operand's `ℓ¹` reach. -/
theorem Zonotope.aux_absBound_mtimesIntervalMat_le {ρc ρr : ℝ} {IM : Interval (Mat ℝ m n)}
    {Z : Zonotope (Vec ℝ n)}
    (hc : ∀ i j, |IM.center i j| ≤ ρc) (hr : ∀ i j, |IM.radius i j| ≤ ρr)
    (i : Fin m) : -- --- CONCL ---
    (Zonotope.mtimesIntervalMat IM Z).absBound i
      ≤ (ρc + ρr) * ∑ j, Z.absBound j := by -- --- PROOF ---
  have habs : ∀ j, (0:ℝ) ≤ Z.absBound j := fun j => by
    rw [Zonotope.absBound]
    positivity
  -- the boxed block couples coordinate `i` to its own generator and no other
  have hdiag := Zonotope.aux_sum_diagonal_abs (fun i => Zonotope.radiusReach IM Z i) i
  have hreach : |Zonotope.radiusReach IM Z i| ≤ ρr * ∑ j, Z.absBound j := by
    calc |Zonotope.radiusReach IM Z i|
        ≤ ∑ j, |IM.radius i j * Z.absBound j| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ j, ρr * Z.absBound j := Finset.sum_le_sum fun j _ => by
          rw [abs_mul, abs_of_nonneg (habs j)]
          exact mul_le_mul_of_nonneg_right (hr i j) (habs j)
      _ = ρr * ∑ j, Z.absBound j := by rw [Finset.mul_sum]
  -- the ordinary block is the center acting on the operand's own data
  have hsplit : (Zonotope.mtimesIntervalMat IM Z).absBound i
      = |(IM.center *ᵥ Z.c) i| + ((∑ l, |(IM.center *ᵥ Z.G l) i|)
        + |Zonotope.radiusReach IM Z i|) := by
    rw [Zonotope.absBound, Zonotope.aux_sum_univ_mtimesIntervalMatBall
      (fun l => |(Zonotope.mtimesIntervalMat IM Z).G l i|)]
    simp only [Zonotope.mtimesIntervalMat, Fin.append_left, Fin.append_right]
    rw [hdiag]
  have hcenter : |(IM.center *ᵥ Z.c) i| + ∑ l, |(IM.center *ᵥ Z.G l) i|
      ≤ ρc * ∑ j, Z.absBound j := by
    have hrows : ∑ l, |(IM.center *ᵥ Z.G l) i| ≤ ∑ l, ρc * ∑ j, |Z.G l j| :=
      Finset.sum_le_sum fun l _ => Zonotope.aux_abs_center_mulVec_le hc _ i
    have hsum : ρc * ∑ j, |Z.c j| + ∑ l, ρc * ∑ j, |Z.G l j| = ρc * ∑ j, Z.absBound j := by
      simp only [Zonotope.absBound, ← Finset.mul_sum, Finset.sum_add_distrib]
      rw [Finset.sum_comm]
      ring
    have h₁ := Zonotope.aux_abs_center_mulVec_le hc Z.c i
    linarith
  rw [hsplit]
  linarith


-- =======================================  MAIN THEOREM  ======================================= --

/-- The product lies in a ball whose radius is the two entry bounds against the
operand's `ℓ¹` reach. -/
theorem Zonotope.mtimesIntervalMat_subset_closedBall {ρc ρr : ℝ} (IM : Interval (Mat ℝ m n))
    (Z : Zonotope (Vec ℝ n)) (hρc : 0 ≤ ρc) (hρr : 0 ≤ ρr)
    (hc : ∀ i j, |IM.center i j| ≤ ρc) (hr : ∀ i j, |IM.radius i j| ≤ ρr) : -- --- CONCL ---
    (Zonotope.mtimesIntervalMat IM Z).construct
      ⊆ Metric.closedBall (0 : Vec ℝ m) ((ρc + ρr) * ∑ j, Z.absBound j) := by -- --- PROOF ---
  have habs : ∀ j, (0:ℝ) ≤ Z.absBound j := fun j => by
    rw [Zonotope.absBound]
    positivity
  have hB : (0:ℝ) ≤ (ρc + ρr) * ∑ j, Z.absBound j :=
    mul_nonneg (by linarith) (Finset.sum_nonneg fun j _ => habs j)
  intro y hy
  obtain ⟨β, hβ, hyeq⟩ := Zonotope.mem_construct_iff.mp hy
  rw [Metric.mem_closedBall, dist_zero_right, pi_norm_le_iff_of_nonneg hB]
  intro i
  rw [Real.norm_eq_abs]
  exact (Zonotope.abs_le_absBound hβ hyeq i).trans
    (Zonotope.aux_absBound_mtimesIntervalMat_le hc hr i)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
