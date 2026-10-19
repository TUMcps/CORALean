module

public import CORALean.ContSet.Interval.Real.Operations.Basic
public import CORALean.ContSet.LevelSet.Real.Definitions.GradEnclosure

@[expose] public section

/-!
# `LevelSet.tightenDomainLinear`

CORA's `@levelSet/tightenDomain` with the contractor `'linear'`: `aux_contractorLinear` runs its
sweep `maxIter` times (CORA fixes `maxIter = 8`), the interval gradient being recomputed on the box
each sweep starts from. The equation is the scalar function `f` (CORA requires a single `'=='`
equation), and `grad` is the handle `der.grad`, passed in with the property
`IsGradEnclosure` that the contractor's soundness needs of it. The other contractors
(`'forwardBackward'`, the default, runs `backpropagation` on the symbolic syntax tree; `'taylor'`
and `'split'` use the solved-variable tables) need symbolic data a `LevelSet` does not carry.

## Inputs
* `f` – equation function
* `grad` – interval gradient of `f`
* `maxIter` – number of sweeps
* `int` – initial box

## Output
* the box contracted by the linear contractor
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       10-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

noncomputable def LevelSet.aux_linearCoord (fm : ℝ) (m : Vec ℝ n) (k : Interval (Vec ℝ n))
  (j : Fin n)
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

noncomputable def LevelSet.aux_linearSweep (f : Vec ℝ n → ℝ)
    (grad : Interval (Vec ℝ n) → Interval (Vec ℝ n)) (int : Interval (Vec ℝ n)) :
    Interval (Vec ℝ n) :=
  let m := int.center             -- m = center(int)
  let k := grad int               -- k = obj.der.grad(int)
  let fm := f m                   -- f = obj.funHan(m)
  (List.finRange n).foldl (fun X j => LevelSet.aux_linearCoord fm m k j X) int


-- =====================================  MAIN DEFINITION  ====================================== --

noncomputable def LevelSet.tightenDomainLinear (f : Vec ℝ n → ℝ)
    (grad : Interval (Vec ℝ n) → Interval (Vec ℝ n)) (maxIter : ℕ) (int : Interval (Vec ℝ n)) :
    Interval (Vec ℝ n) :=
  (LevelSet.aux_linearSweep f grad)^[maxIter] int

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
