module

public import CORALean.ContSet.Conversion.Real.Operations.Zonotope_to_Interval
public import CORALean.ContSet.Interval.Real.Operations.AbsMax
public import CORALean.ContSet.Zonotope.Real.Operations.OfPoint
public import Mathlib.Analysis.Matrix.Normed

@[expose] public section

/-!
# A point matrix zonotope is dominated by the matrix itself

`ofPoint A` has no generators, so the box it encloses is `[A, A]` and its
`absMax` is `|A|` entrywise. The `l∞` operator norm is a supremum of row sums
of absolute values, which absolute values leave alone, so the two norms agree.

What it is for: `expMatZonoEnclosure` states its tail condition at
`M.interval.absMax`, since that is the only matrix a whole zonotope answers
for. Where the zonotope is a point the condition is about that point, and this
is what says so — so a discretization of a `LinearSys`, whose matrix is a
single matrix, states the same `‖Δt • A‖ / (η + 2) < 1` the interval-matrix
enclosure already asks its callers for.
-/

-- Authors:       Claude Opus 5
-- Written:       07-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {m n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- The dominating matrix of a generator-free matrix zonotope has the norm of
its centre. -/
theorem Zonotope.norm_absMax_ofPoint (A : Mat ℝ m n) :
    ‖(Zonotope.ofPoint A).interval.absMax‖ = ‖A‖ := by -- --- PROOF ---
  have hentry : ∀ i j, (Zonotope.ofPoint A).interval.absMax i j = |A i j| := by
    intro i j
    have hof : ∀ f : Fin m × Fin n → ℝ, (Entrywise.ofEntry f : Mat ℝ m n) i j = f (i, j) :=
      fun f => (Entrywise.entry_mat _ (i, j)).symm.trans (Entrywise.entry_ofEntry f (i, j))
    simp [Zonotope.interval, Zonotope.ofPoint, Interval.absMax, hof]
  -- equal row sum by row sum, since `‖|x|‖₊ = ‖x‖₊` entry by entry
  have h : ‖(Zonotope.ofPoint A).interval.absMax‖₊ = ‖A‖₊ := by
    rw [Matrix.linfty_opNNNorm_def, Matrix.linfty_opNNNorm_def]
    exact Finset.sup_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by
      rw [hentry i j]
      simp
  rw [← coe_nnnorm, ← coe_nnnorm, h]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
