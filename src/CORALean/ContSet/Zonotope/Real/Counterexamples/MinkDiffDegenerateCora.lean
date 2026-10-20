module

public import CORALean.ContSet.Zonotope.Real.Operations.Mtimes
public import CORALean.ContSet.ContSet.ContSet
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.Tactic.FinCases

@[expose] public section

/-!
# `Zonotope.minkDiffDegenerateCora`, CORA's `minkDiff` at a degenerate minuend

CORA's `@zonotope/minkDiff.m` for a minuend and a subtrahend that are not full-dimensional and
have generator matrices of equal rank (l. 153-161): `[U, S] = svd(generators(minuend))`, `newDim`
the number of nonzero columns of `S`, `P_minuend = U(1:newDim, :)` (l. 168), the same for the
subtrahend only to check that both projections agree, then the difference of the projected sets in
`ℝ^newDim` mapped back by `pinv(P_minuend)` (l. 186).

Two slips: `U(1:newDim, :)` takes the first rows of `U` where the range of the generators is
spanned by its first columns, and the projection forgets the component of the minuend's center
outside that range, which `pinv` cannot bring back: every result lies in the row space of
`P_minuend`, a subspace through the origin, wherever the minuend lies. The recursive call and the
SVD factor `U` are parameters the theorems constrain; for orthogonal `U`,
`pinv(P_minuend) = P_minuendᵀ`. Read from the source, not run.

# CORA's `minkDiff` at a degenerate minuend misses the difference entirely

The minuend is the segment `{(t, 1) | |t| ≤ 1}`, the subtrahend `{(t, 0) | |t| ≤ ½}`; both are
of rank one, so `@zonotope/minkDiff.m` takes the SVD branch. Whatever SVD the solver returns,
`P_minuend = U(1, :) = ±e₁ᵀ`, so the result lies on the line `x₂ = 0`, whatever the recursive 1-D
call returns. The difference is the segment `{(t, 1) | |t| ≤ ½}`, nonempty and on `x₂ = 1`.

## Inputs
* none

## Hypotheses
* none

## Conclusion
* CORA's result misses the true Minkowski difference entirely

## References

* [1] `contSet/@zonotope/minkDiff.m`, CORA, ll. 113-114, 153-193.
-/

-- Authors:       Claude Opus 5.5
-- Written:       13-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {n : ℕ}


-- The model: CORA's code as printed, kept only to be refuted.
/-- [1]'s degenerate branch past its guards: project with the first `newDim` rows of the SVD
factor `U`, take the difference there (`minkDiffRec`), map back with `pinv = ᵀ`. -/
def Zonotope.minkDiffDegenerateCora (minuend subtrahend : Zonotope (Vec ℝ n)) (U : Mat ℝ n n)
    (newDim : ℕ) (hk : newDim ≤ n)
    (minkDiffRec : Zonotope (Vec ℝ newDim) → Zonotope (Vec ℝ newDim) → Zonotope (Vec ℝ newDim)) :
    Zonotope (Vec ℝ n) :=
  -- l. 168: `P_minuend = U(1:newDim, :)`
  let P_minuend : Mat ℝ newDim n := fun i j => U (Fin.castLE hk i) j
  -- l. 179: `minuend_proj = P_minuend * minuend`
  let minuend_proj : Zonotope (Vec ℝ newDim) := minuend.mtimes P_minuend
  -- l. 180: `subtrahend_proj = P_minuend * subtrahend`
  let subtrahend_proj : Zonotope (Vec ℝ newDim) := subtrahend.mtimes P_minuend
  -- l. 183: `Z_proj = minkDiff(minuend_proj, subtrahend_proj, method)`
  let Z_proj : Zonotope (Vec ℝ newDim) := minkDiffRec minuend_proj subtrahend_proj
  -- l. 186: `Z = pinv(P_minuend) * Z_proj`
  Z_proj.mtimes P_minuendᵀ

end CORALean.Real

namespace CORALean.Real

open Matrix


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zonotope.minkDiffDegenerateCora_counterexample : -- --- CONCL ---
    let minuend : Zonotope (Vec ℝ 2) := ⟨1, ![0, 1], fun _ => ![1, 0]⟩
    let subtrahend : Zonotope (Vec ℝ 2) := ⟨1, 0, fun _ => ![1 / 2, 0]⟩
    ∀ (U : Mat ℝ 2 2) (S : Mat ℝ 2 1) (V : Mat ℝ 1 1), Uᵀ * U = 1 → S 1 0 = 0 →
      (!![1; 0] : Mat ℝ 2 1) = U * S * Vᵀ →
      ∀ minkDiffRec : Zonotope (Vec ℝ 1) → Zonotope (Vec ℝ 1) → Zonotope (Vec ℝ 1),
        (minkowskiDiff minuend.construct subtrahend.construct).Nonempty ∧
        Disjoint (minuend.minkDiffDegenerateCora subtrahend U 1 (by norm_num) minkDiffRec).construct
          (minkowskiDiff minuend.construct subtrahend.construct) := by -- --- PROOF ---
  intro M Sb U S V hU hS hsvd rec
  -- the SVD forces `U 1 0 = 0`, orthogonality then `U 0 1 = 0`
  have h00 := congrFun (congrFun hsvd 0) 0
  have h10 := congrFun (congrFun hsvd 1) 0
  simp only [Matrix.mul_apply, Fin.sum_univ_two, Fin.sum_univ_one, Matrix.transpose_apply,
    hS] at h00 h10
  norm_num at h00 h10
  have hU10 : U 1 0 = 0 := by
    rcases h10 with (h | h) | h
    · exact h
    · simp [h] at h00
    · simp [h] at h00
  have hc := congrFun (congrFun hU 0) 0
  have hUU : U * Uᵀ = 1 := mul_eq_one_comm.mp hU
  have hr := congrFun (congrFun hUU 0) 0
  simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.transpose_apply, Matrix.one_apply_eq,
    hU10] at hc hr
  have hU01 : U 0 1 = 0 := by nlinarith [sq_nonneg (U 0 1)]
  -- every point of the difference has second coordinate `1` (take `y = 0`)
  have hdiff : ∀ x ∈ minkowskiDiff M.construct Sb.construct, x 1 = 1 := by
    intro x hx
    obtain ⟨β, -, hβ⟩ := hx 0 ⟨fun _ => 0, fun _ => by simp, by simp [Sb]⟩
    have := congrFun hβ 1
    simpa [M] using this
  refine ⟨⟨![0, 1], fun y hy => ?_⟩, Set.disjoint_left.mpr fun x hx hd => ?_⟩
  · obtain ⟨β, hβ, rfl⟩ := hy
    refine ⟨fun j => β j / 2, fun j => ?_, ?_⟩
    · have := hβ j
      rw [abs_div, abs_two]
      linarith
    · funext i
      fin_cases i <;> simp [M, Sb, div_eq_mul_inv]
  · -- every point of the result has second coordinate `0`
    have h1 := hdiff x hd
    obtain ⟨β, -, rfl⟩ := hx
    simp [Zonotope.minkDiffDegenerateCora, Zonotope.mtimes, Matrix.mulVec, dotProduct,
      Finset.sum_apply, hU01] at h1

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
