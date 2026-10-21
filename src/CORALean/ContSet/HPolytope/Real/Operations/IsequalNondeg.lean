module

public import CORALean.ContSet.HPolytope.Real.Operations.Ineqs
public import CORALean.ContSet.ContSet.Definitions.SupportFunc
public import CORALean.Global.DropIdx
public import CORALean.Global.EuclideanNorm

@[expose] public section

/-!
# `HPolytope.isequalNondeg`

[1, Alg. 1], set equality of two non-degenerate H-polytopes in minimal representation: after
normalizing every row (line 1), every row of either polytope must have an equal row in the other
or be redundant in its own (lines 2-8). Line 4 is read as the text explains it — "the constraint
must be redundant for set equality to hold, which can be checked using the support function as
in (1)" — and as CORA's `aux_isNonredundantConstraint` computes it: the row fails the test when
the support function without it exceeds its offset. The printed line 4, `ρ(…) = b₁(j)`, fails
nowhere on minimal input (`isequalNondeg_printed_counterexample`).

## Inputs
* `A₁` – `q₁ × n` matrix
* `b₁` – offset vector of length `q₁`
* `A₂` – `q₂ × n` matrix
* `b₂` – offset vector of length `q₂`

## Output
* `true` when every row of either polytope has an equal row in the other or is redundant

## References

* [1] M. Wetzlinger, V. Kotsev, A. Kulmburg and M. Althoff. "Implementation of Polyhedral
      Operations in CORA 2024". In Proc. of the 11th International Workshop on Applied
      Verification of Continuous and Hybrid Systems (ARCH24), EPiC Series in Computing,
      vol. 103, pp. 163-181, 2024.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Classical

variable {q₁ q₂ n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

noncomputable def HPolytope.isequalNondeg (A₁ : Mat ℝ q₁ n) (b₁ : Vec ℝ q₁) (A₂ : Mat ℝ q₂ n)
    (b₂ : Vec ℝ q₂) : Bool :=
  -- line 1: every row and its offset divided by the row's Euclidean length
  let nA₁ : Mat ℝ q₁ n := Matrix.of fun j => ‖A₁ j‖₂⁻¹ • A₁ j
  let nb₁ : Vec ℝ q₁ := fun j => b₁ j / ‖A₁ j‖₂
  let nA₂ : Mat ℝ q₂ n := Matrix.of fun k => ‖A₂ k‖₂⁻¹ • A₂ k
  let nb₂ : Vec ℝ q₂ := fun k => b₂ k / ‖A₂ k‖₂
  -- lines 2-7: a row of `P₁` with no equal row in `P₂` has to be redundant in `P₁`
  let pass₁ : Prop := ∀ j, (∃ k, nA₁ j = nA₂ k ∧ nb₁ j = nb₂ k) ∨
    supportFunc
      (HPolytope.ineqs (nA₁.submatrix (dropIdx j) id) fun i => nb₁ (dropIdx j i)).construct
      (HPolytope.rowLin nA₁ j) ≤ (nb₁ j : EReal)
  -- line 8: the same with the indices 1 and 2 switched
  let pass₂ : Prop := ∀ k, (∃ j, nA₂ k = nA₁ j ∧ nb₂ k = nb₁ j) ∨
    supportFunc
      (HPolytope.ineqs (nA₂.submatrix (dropIdx k) id) fun i => nb₂ (dropIdx k i)).construct
      (HPolytope.rowLin nA₂ k) ≤ (nb₂ k : EReal)
  -- line 9: both passes, `⊤`
  if pass₁ ∧ pass₂ then true else false

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
