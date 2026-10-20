module

public import Mathlib.Data.Matrix.Basic
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.Tactic.Linarith
public import Mathlib.Data.Real.Basic
public import Mathlib.Tactic.NormNum

@[expose] public section

/-!
# CORA's `M * fullspace(n)` is the plane for `[1 1; 1 1]`, the image is a line

`@fullspace/mtimes.m` (l. 53-63) documents `mtimes` as "the set `{ M s | s ∈ S }`", but for a
numeric `M` it recognises only entirely zero rows (`zerorows = ~any(M,2)`, the box
`interval(-Inf..Inf)` with those rows set to 0); otherwise it returns `fullspace(size(M,1))` or `fs`
itself. So any `M` without a zero row gives the whole space, though `{M x}` is the whole space only
for full row rank. `M = [1 1; 1 1]` is square with no zero row, so CORA returns `R^2`; the image is
the line `{(t, t)}` and `(1, 0)` is not on it; likewise `[1; 1] * fullspace(1)`. `isFullDim`,
`representsa(.., 'fullspace')` and `volume` then answer for the plane. Read from the source, not
run.

## Inputs
* none

## Hypotheses
* none

## Conclusion
* CORA's `mtimes` of a singular matrix and the full space contains a point outside the range
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- The model: CORA's code as printed, kept only to be refuted.
/-- CORA's `M * fullspace(n)` for an `m x n` matrix, as a set of points of `R^m`. -/
def Fullspace.mtimesRankCora {m n : ℕ} (M : Matrix (Fin m) (Fin n) ℝ) : Set (Fin m → ℝ) :=
  -- zerorows = ~any(M,2); if any(zerorows): `[-Inf, Inf]` with the zero rows set to 0
  if ∃ i, ∀ j, M i j = 0 then {y | ∀ i, (∀ j, M i j = 0) → y i = 0}
  -- all other matrices: `fullspace(size(M,1))`
  else Set.univ


-- =======================================  MAIN THEOREM  ======================================= --

/-- For `M = [1 1; 1 1]` CORA's result contains `(1, 0)`, which the image `{M x}` does not. -/
theorem Fullspace.mtimesRank_cora_counterexample :
    (![1, 0] : Fin 2 → ℝ) ∈ Fullspace.mtimesRankCora !![(1 : ℝ), 1; 1, 1] ∧
      (![1, 0] : Fin 2 → ℝ) ∉ Set.range (Matrix.mulVec !![(1 : ℝ), 1; 1, 1]) := by -- --- PROOF ---
  constructor
  · simp [Fullspace.mtimesRankCora]
  · rintro ⟨x, hx⟩
    have h0 := congrFun hx 0
    have h1 := congrFun hx 1
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two] at h0 h1
    linarith

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
