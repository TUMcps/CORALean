module

public import CORALean.Global.Tensor
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Data.Fin.Tuple.Basic

@[expose] public section

/-!
# `HPolytope.affineHullBasis`

[1, Alg. 2], the loop of lines 3-9: append the maximizer `x_iter` of [1, Eq. 22] — the longest
vector, in `‖·‖∞`, perpendicular to the columns found so far and completing a point of the shifted
polytope — until it is no longer than `ε`, at most `n` times. The maximizer is an argument: the
paper solves `2n` linear programs per step, and `affineHullBasis_spec` states what it has to
return. The Chebyshev center of line 1 is the shift, a point of the polytope, which the
specification takes as `c`. Called as `affineHullBasis ε xiter n 0 Fin.elim0`: `n` iterations
left, no columns yet.

## Inputs
* `ε` – tolerance
* `xiter` – maximizer of [1, Eq. 22] given the columns found so far

## Output
* the columns found (their number and the family), appended until `x_iter` is at most `ε`

## References

* [1] M. Wetzlinger, V. Kotsev, A. Kulmburg and M. Althoff. "Implementation of Polyhedral Operations
      in CORA 2024". Proceedings of the 11th Int. Workshop on Applied Verification for Continuous
      and Hybrid Systems, 2024.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      16-October-2026 (Tobias Ladner)


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

noncomputable def HPolytope.affineHullBasis (ε : ℝ)
    (xiter : (r : ℕ) → (Fin r → Vec ℝ n) → Vec ℝ n) :
    (fuel r : ℕ) → (Fin r → Vec ℝ n) → Σ r, (Fin r → Vec ℝ n)
  | 0, r, B => ⟨r, B⟩
  | fuel + 1, r, B =>
    -- line 4: the maximizer of [1, Eq. 22], perpendicular to `B`
    let x := xiter r B
    -- lines 5-7: no non-trivial perpendicular direction left
    if ‖x‖ ≤ ε then ⟨r, B⟩
    -- line 8: append it and go round again
    else HPolytope.affineHullBasis ε xiter fuel (r + 1) (Fin.snoc (α := fun _ => Vec ℝ n) B x)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
