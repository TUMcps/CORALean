import CORALean.ContDynamics.LinearSysDT.Theorems.BackReachExistsOuter
import CORALean.ContDynamics.LinearSysDT.Theorems.BackReachSetExistsTrajectory
import CORALean.ContSet.Interval.Real.Instances

/-!
# One backward step in the `∃` reading, at a box

`x(k+1) = 2 x(k) + u(k)` on the line, target `[-1, 1]`, inputs `[-0.2, 0.2]` —
`BackwardReach`'s system, read the other way. Some input reaches the target from
`x` exactly when `2x` is within `0.2` of it, so the set is `[-0.6, 0.6]`, and
that is what the run returns.

At `Interval`, which the `∀` reading cannot use: there the step is a Minkowski
difference and the preimage wants an exact `mtimes`, and `Interval` carries no
exactness theorem for one. Here both steps are the outer half — `plus_outer`
and `mtimes_outer` — so the representation needs nothing else.

What an outer backward set buys is the negative: `0.7` is outside it, so *no*
admissible input drives `0.7` into the target, which is the second example. The
third spends the set the other way, turning a point of it into a run.
-/

-- Authors:       Tobias Ladner
-- Written:       07-September-2026
-- Last update:   30-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix Pointwise ContSet Scalar Plus Mtimes


-- =====================================  MAIN DEFINITION  ====================================== --

def BReachE.sys : LinearSysDT ℝ 1 := ⟨!![(2:ℝ)]⟩

/-- The left inverse the backward step travels along: `Ainv A = 1`, where the
`∀` reading asks for `A Ainv = 1`. At a square matrix the same one serves. -/
def BReachE.Ainv : Mat ℝ 1 1 := !![(0.5:ℝ)]

def BReachE.T : Interval (Vec ℝ 1) := ⟨![(-1:ℝ)], ![(1:ℝ)]⟩

def BReachE.U : Interval (Vec ℝ 1) := ⟨![(-0.2:ℝ)], ![(0.2:ℝ)]⟩

theorem BReachE.hA : toRealMat BReachE.Ainv * toRealMat BReachE.sys.A = 1 := by -- --- PROOF ---
  ext i j
  fin_cases i
  fin_cases j
  simp [BReachE.sys, BReachE.Ainv, Matrix.mul_apply]
  norm_num

/-- The input set is symmetric about the origin, so it encloses its own
negation and serves as `negU` unchanged. -/
theorem BReachE.hneg : -construct BReachE.U ⊆ construct BReachE.U := by -- --- PROOF ---
  intro x hx
  have h := Set.mem_neg.mp hx
  intro i
  show (![(-0.2:ℝ)] : Vec ℝ 1) i ≤ x i ∧ x i ≤ (![(0.2:ℝ)] : Vec ℝ 1) i
  -- the same two bounds on `-x`, read back onto `x`
  have hlo : (![(-0.2:ℝ)] : Vec ℝ 1) i ≤ -(x i) := (h i).1
  have hhi : -(x i) ≤ (![(0.2:ℝ)] : Vec ℝ 1) i := (h i).2
  simp only [Matrix.cons_val_fin_one] at hlo hhi ⊢
  constructor <;> linarith

/-- `0.7` is outside the computed set: one `plus` and one `mtimes` give
`[-0.6, 0.6]`, and the box excludes the point on its own. -/
theorem BReachE.not_mem :
    (![(0.7:ℝ)] : Vec ℝ 1) ∉ construct (BReachE.sys.backReachExists (S := ℐ𝒱)
      ⟨BReachE.T, BReachE.U, 0, 1⟩ ⟨BReachE.Ainv⟩) := by -- --- PROOF ---
  intro h
  have hhi : (![(0.7:ℝ)] : Vec ℝ 1) 0 ≤
      ∑ k : Fin 1, max (BReachE.Ainv 0 k * (BReachE.T.inf k + BReachE.U.inf k))
        (BReachE.Ainv 0 k * (BReachE.T.sup k + BReachE.U.sup k)) := (h 0).2
  norm_num [BReachE.Ainv, BReachE.T, BReachE.U, Fin.sum_univ_one] at hhi

/-- So no admissible input drives `0.7` into the target in one step — the
guarantee an *outer* backward set gives, which is a negative one. -/
example (u : Vec ℝ 1) (hu : u ∈ construct BReachE.U) :
    BReachE.sys.simulate ![(0.7:ℝ)] (fun _ => u) 1 ∉ construct BReachE.T := fun hT =>
  BReachE.not_mem (BReachE.sys.backReachExists_outer (S := ℐ𝒱) BReachE.hA BReachE.T
    BReachE.U BReachE.U BReachE.hneg 1 ⟨u, hu, hT⟩)

/-- `0.3` is in the exact set, witnessed by the zero input: `2 · 0.3 = 0.6`,
which is in `[-1, 1]`. -/
theorem BReachE.mem :
    (![(0.3:ℝ)] : Vec ℝ 1) ∈ BReachE.sys.backReachSetExists (S := ℐ𝒱)
      BReachE.T BReachE.U 1 := by -- --- PROOF ---
  refine ⟨0, fun i => ?_, fun i => ?_⟩
  · show (![(-0.2:ℝ)] : Vec ℝ 1) i ≤ (0 : Vec ℝ 1) i ∧ (0 : Vec ℝ 1) i ≤ (![(0.2:ℝ)] : Vec ℝ 1) i
    norm_num
  · show (![(-1:ℝ)] : Vec ℝ 1) i ≤ (toRealMat BReachE.sys.A *ᵥ ![(0.3:ℝ)] + 0) i ∧
      (toRealMat BReachE.sys.A *ᵥ ![(0.3:ℝ)] + 0) i ≤ (![(1:ℝ)] : Vec ℝ 1) i
    norm_num [BReachE.sys, Matrix.mulVec, dotProduct]

/-- `0.3` is in the target as well, which is what lets a run start there:
`backReachSetExists_trajectory` asks for a set the start lies in. -/
theorem BReachE.memT : (![(0.3:ℝ)] : Vec ℝ 1) ∈ construct BReachE.T := by
  intro i
  show (![(-1:ℝ)] : Vec ℝ 1) i ≤ (![(0.3:ℝ)] : Vec ℝ 1) i ∧
    (![(0.3:ℝ)] : Vec ℝ 1) i ≤ (![(1:ℝ)] : Vec ℝ 1) i
  norm_num

/-- And the set spent the other way: from `0.3` there *is* an admissible signal
whose run is in the target one step on. -/
example : ∃ u : ℕ → Vec ℝ 1,
    BReachE.sys.TrajectoryOn (S := ℐ𝒱) BReachE.T BReachE.U 1
      (BReachE.sys.simulate ![(0.3:ℝ)] u) u ∧
    BReachE.sys.simulate ![(0.3:ℝ)] u 1 ∈ construct BReachE.T :=
  BReachE.sys.backReachSetExists_trajectory (S := ℐ𝒱) BReachE.T BReachE.U
    BReachE.memT 1 BReachE.mem

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
