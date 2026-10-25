module

public import CORALean.ContSet.Taylm.Real.Definitions.TaylorModelOn

@[expose] public section

/-!
# `intersect(I, LS)`: a box cut by a level set solved for one variable

[1, Thm. 1, eq. (3)]: the box `I` cut by `LS = {x | x(k) = p_k(x)}` as the Taylor model
`⟨h(x), ∅, I⟩` over the box itself, where `h` is the identity with its `k`-th coordinate
replaced by `p_k(x)`. [1]'s `∅` remainder is the zero box (`TaylorModelOn`).
`Theorems.IntersectLevelSetBoxSubset` and `…Exact` say what it encloses.

## Inputs
* `I` – box
* `k` – solved coordinate
* `p` – polynomial for the solved coordinate

## Output
* Taylor model of the box cut by `x(k) = p(x)`

## References

* [1] N. Kochdumper and M. Althoff. "Reachability Analysis for Hybrid Systems with Nonlinear Guard
      Sets". Proceedings of the 23rd International Conference on Hybrid Systems: Computation and
      Control, 2020.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def intersectLevelSetBox (I : Interval (Vec ℝ n)) (k : Fin n) (p : Vec ℝ n → ℝ) :
    TaylorModelOn n :=
  -- (3): h(x) = [x(1) … x(k-1) p_k(x) x(k+1) … x(n)]ᵀ
  let h : Vec ℝ n → Vec ℝ n := fun x => Function.update x k (p x)
  ⟨h, ⟨0, 0⟩, I⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
