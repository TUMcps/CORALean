import CORALean.ContDynamics.LinearSysDT.Theorems.Real.BackReachForallInnerZonotope
import CORALean.ContDynamics.LinearSysDT.Theorems.BackReachSetForallExactIsTrajectory
import CORALean.ContDynamics.LinearSysDT.Theorems.SimulateIsTrajectory
import CORALean.ContDynamics.LinearSysDT.Operations.Canonical

/-!
# One backward step, computed and then believed

`x(k+1) = 2 x(k) + u(k)` on the line, target `[-1, 1]`, inputs `[-0.2, 0.2]`. Every input costs
`0.2` of the target, so the states that every input keeps inside are `[-0.4, 0.4]`, which the run
returns exactly, the two generators being aligned. The file is for the hypotheses, not the number:
`hA` is a right inverse, `M` is the generator representation `minkDiffRep` checks, and
`backReachForall_inner_zonotope` supplies the rest; a caller has all three, which a theorem
quantifying over them cannot show. The second example is the guarantee spent: one run, one
arbitrary input signal, and a state in `T` afterwards.

## Inputs
* none

## Output
* one-dimensional discrete system
-/

-- Authors:       Claude Opus 5
-- Written:       07-September-2026
-- Last update:   30-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix ContSet Scalar Mtimes


-- =====================================  MAIN DEFINITION  ====================================== --

def BReach.sys : LinearSysDT ℝ 1 := LinearSysDT.canonical !![(2:ℝ)]

/-- The right inverse the backward step travels along, handed in rather than
computed: `A⁻¹` is no set operation. -/
def BReach.Ainv : Mat ℝ 1 1 := !![(0.5:ℝ)]

/-- The target set, the zonotope `[-1, 1]` on the line. -/
def BReach.T : Zonotope (Vec ℝ 1) := ⟨1, ![(0:ℝ)], fun _ => ![(1:ℝ)]⟩

/-- The input set, the zonotope `[-0.2, 0.2]` on the line. -/
def BReach.U : Zonotope (Vec ℝ 1) := ⟨1, ![(0:ℝ)], fun _ => ![(0.2:ℝ)]⟩

/-- Each input generator in the target's own, which is what `minkDiffRep`
checks: `0.2 = 0.2 · 1`, at every pair it is handed. -/
def BReach.M (Z₁ Z₂ : Zonotope (Vec ℝ 1)) : Fin Z₁.h → Fin Z₂.h → ℝ := fun _ _ => 0.2

/-- The doubling matrix times the right inverse `Ainv` is the identity. -/
theorem BReach.hA : -- --- CONCL ---
    BReach.sys.A * BReach.Ainv = 1 := by -- --- PROOF ---
  ext i j
  fin_cases i
  fin_cases j
  simp [BReach.sys, BReach.Ainv, Matrix.mul_apply]
  norm_num

/-- The difference `minkDiffRep` returns, written in its own terms so that the
step below is the check and nothing else. -/
noncomputable def BReach.D : Zonotope (Vec ℝ 1) :=
  { h := BReach.T.h, c := BReach.T.c - BReach.U.c,
    G := fun i => (1 - ∑ j : Fin BReach.U.h, |BReach.M BReach.T BReach.U i j|) • BReach.T.G i }

/-- `minkDiffRep` accepts the generator representation `M` and returns the difference `D`. -/
theorem BReach.step : -- --- CONCL ---
    BReach.T.minkDiffRep BReach.U (BReach.M BReach.T BReach.U) =
    some BReach.D := by -- --- PROOF ---
  -- the two halves of the check, at the one generator each set has
  have hcond : (∀ j, BReach.U.G j = ∑ i, BReach.M BReach.T BReach.U i j • BReach.T.G i) ∧
      ∀ i, ∑ j, |BReach.M BReach.T BReach.U i j| ≤ 1 := by
    constructor
    · intro j
      show (![(0.2:ℝ)] : Vec ℝ 1) = ∑ _i : Fin 1, (0.2:ℝ) • (![(1:ℝ)] : Vec ℝ 1)
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, one_smul]
      funext i
      fin_cases i
      norm_num
    · intro i
      show ∑ _j : Fin 1, |(0.2:ℝ)| ≤ 1
      norm_num
  rw [Zonotope.minkDiffRep, if_pos hcond]
  rfl

/-- One step of the run, which is the difference and then the image under the
inverse — `some`, so the check passed. -/
theorem BReach.run : BReach.sys.backReachForall (S := 𝒵)
    ⟨BReach.T, BReach.U, 0, 1⟩ ⟨BReach.Ainv, fun Z₁ Z₂ => Z₁.minkDiffRep Z₂ (BReach.M Z₁ Z₂)⟩ =
      some (Zonotope.mtimes BReach.Ainv BReach.D) := by
  show (BReach.T.minkDiffRep BReach.U (BReach.M BReach.T BReach.U)).map
      (Zonotope.mtimes BReach.Ainv) = _
  rw [BReach.step]
  rfl

/-- `0.3` is in the computed set: `0.75` of its one generator, which is `0.4`
long — half of what the difference left, the inverse having halved it. -/
theorem BReach.mem : -- --- CONCL ---
    (![(0.3:ℝ)] : Vec ℝ 1) ∈ (Zonotope.mtimes BReach.Ainv BReach.D).construct := by -- --- PROOF ---
  refine ⟨fun _ => 0.75, fun j => by norm_num, ?_⟩
  show (![(0.3:ℝ)] : Vec ℝ 1) =
    BReach.Ainv *ᵥ (![(0:ℝ)] - ![(0:ℝ)]) + ∑ _j : Fin 1,
      (0.75:ℝ) • (BReach.Ainv *ᵥ ((1 - ∑ _j : Fin 1, |(0.2:ℝ)|) • (![(1:ℝ)] : Vec ℝ 1)))
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, one_smul]
  funext i
  fin_cases i
  norm_num [BReach.Ainv, Matrix.mulVec, dotProduct]

/-- So `0.3` is in the exact backward reachable set — the computed set is
inside it, and that is the only direction an implementation may claim. -/
theorem BReach.backOne :
    (![(0.3:ℝ)] : Vec ℝ 1) ∈ BReach.sys.backReachSetForallExact (S := 𝒵) BReach.T BReach.U 1 :=
  BReach.sys.backReachForall_inner_zonotope BReach.hA BReach.M BReach.T BReach.U 1 _
    BReach.run BReach.mem

/-- `0.3` is in the target itself as well, which is what lets one run start
there: `simulate_isTrajectory` asks for a set the start lies in. -/
theorem BReach.memT : -- --- CONCL ---
    (![(0.3:ℝ)] : Vec ℝ 1) ∈ BReach.T.construct := by -- --- PROOF ---
  refine ⟨fun _ => 0.3, fun j => by norm_num, ?_⟩
  show (![(0.3:ℝ)] : Vec ℝ 1) = ![(0:ℝ)] + ∑ _i : Fin 1, (0.3:ℝ) • (![(1:ℝ)] : Vec ℝ 1)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, one_smul]
  funext i
  fin_cases i
  norm_num

/-- The guarantee spent: whatever input signal `U` admits, the run from `0.3`
is inside the target one step later. -/
example (u : ℕ → Vec ℝ 1) (hu : ∀ k, u k ∈ construct BReach.U) :
    BReach.sys.simulate ![(0.3:ℝ)] u 1 ∈ construct BReach.T :=
  BReach.sys.backReachSetForallExact_isTrajectory (S := 𝒵) BReach.T BReach.U
    (BReach.sys.simulate_isTrajectory (S := 𝒵) (R₀ := BReach.T) BReach.memT hu) 1 BReach.backOne

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
