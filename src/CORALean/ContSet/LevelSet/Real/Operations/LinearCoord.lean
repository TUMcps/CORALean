import CORALean.ContSet.LevelSet.Real.Definitions.GradEnclosure
import CORALean.ContSet.Interval.Real.Operations.MulHi
import CORALean.ContSet.Interval.Real.Operations.MulLo

/-!
# `LevelSet.linearCoord`

One step of the `'linear'` contractor of CORA's `@levelSet/tightenDomain` (`aux_contractorLinear`),
the body of its loop over the coordinates `j`: when the `j`-th entry `k(j)` of the interval
gradient has one sign, the equation `f(m) + kᵀ(x - m) = 0` is solved for `x(j)`,

    tightenedRange = (-f + kᵀ m - k_ᵀ int) / k(j),    int(j) = int(j) ∩ tightenedRange,

with `k_` equal to `k` but for `0` at `j`. The interval operations are written out on their
bounds, with the corner products `Interval.mulLo` and `Interval.mulHi`; `kᵀ m` multiplies each
`k(i)` by the point `m(i)`, `k_ᵀ int` by the current box (which earlier coordinates have already
tightened), and the division is the product with the reciprocal `[1/k̄(j), 1/k̲(j)]`.

CORA enters the branch when `sign(sup k(j)) == sign(inf k(j))`, which also holds for
`k(j) = [0, 0]`, a division by zero; here the branch needs `0 ∉ k(j)`, and the box is left
as it is otherwise.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       10-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

noncomputable def LevelSet.linearCoord (fm : ℝ) (m : Vec ℝ n) (k : Interval (Vec ℝ n)) (j : Fin n)
    (int : Interval (Vec ℝ n)) : Interval (Vec ℝ n) :=
  if 0 < k.inf j ∨ k.sup j < 0 then
    -- the numerator `-f + kᵀ m - k_ᵀ int`, as an interval `[sLo, sHi]`
    let sLo := -fm + ∑ i, Interval.mulLo (k.inf i) (k.sup i) (m i) (m i)
      - ∑ i ∈ Finset.univ.erase j, Interval.mulHi (k.inf i) (k.sup i) (int.inf i) (int.sup i)
    let sHi := -fm + ∑ i, Interval.mulHi (k.inf i) (k.sup i) (m i) (m i)
      - ∑ i ∈ Finset.univ.erase j, Interval.mulLo (k.inf i) (k.sup i) (int.inf i) (int.sup i)
    -- tightenedRange = numerator / k(j)
    let lo := Interval.mulLo sLo sHi (k.sup j)⁻¹ (k.inf j)⁻¹
    let hi := Interval.mulHi sLo sHi (k.sup j)⁻¹ (k.inf j)⁻¹
    -- int(j) = and_(int(j), tightenedRange, 'exact')
    { inf := Function.update int.inf j (max (int.inf j) lo)
      sup := Function.update int.sup j (min (int.sup j) hi) }
  else int

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
