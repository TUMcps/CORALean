module

public import CORALean.ContSet.LevelSet.Real.Operations.IntersectLevelSetBox

@[expose] public section

/-!
# Guard intersection for a constraint solvable for one variable

[1, Prop. 1]: for a guard `{x | x(k) = D_g(x)}` and a Taylor series `a, b, c, v, l, u` of
`D_g` on the box `I` (eq. (6)), the polynomial part `p_k(x) = b + aᵀ(x - c) + v(x)` is cut
with the box by `intersect` (eq. (7)), and the remainder `[l, u]` is put in the `k`-th
coordinate of the model's box remainder (eq. (8)). The expansion is passed in as its parts, so
any expansion that encloses `D_g` will do; `TaylorSeries` is [1, Def. 7]'s.
`Theorems.GuardIntersectSolvableSubset` is the enclosure.

## Inputs
* `I` – box
* `k` – solved coordinate
* `b` – constant term
* `a` – linear coefficients
* `c` – expansion center
* `v` – higher-order terms
* `l` – lower remainder bound
* `u` – upper remainder bound

## Output
* Taylor model of the box cut by the guard with remainder `[l, u]`

## References

* [1] [N. Kochdumper and M. Althoff. "Reachability Analysis for Hybrid Systems with Nonlinear Guard
      Sets". Proceedings of the 23rd International Conference on Hybrid Systems: Computation and
      Control, 2020.](../../../../../../references/2020/kochdumper-hscc-nonlinear-guards.md)
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def guardIntersectSolvable (I : Interval (Vec ℝ n)) (k : Fin n) (b : ℝ) (a c : Vec ℝ n)
    (v : Vec ℝ n → ℝ) (l u : ℝ) : TaylorModelOn n :=
  -- (7): the polynomial part of the expansion (6)
  let pk : Vec ℝ n → ℝ := fun x => b + ∑ i, a i * (x i - c i) + v x
  let h := (intersectLevelSetBox I k pk).p
  -- (8): B = [[0_{k-1}; l; 0_{n-k}], [0_{k-1}; u; 0_{n-k}]]
  let B : Interval (Vec ℝ n) := ⟨Pi.single k l, Pi.single k u⟩
  ⟨h, B, I⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
