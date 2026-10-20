module

public import CORALean.ContSet.Interval.Real.Interval
public import Mathlib.Algebra.Order.Archimedean.Real.Basic

@[expose] public section

/-!
# The interval hull of a set

[1, Def. 2]: `Box(S)`, the smallest interval vector containing `S`, coordinate by coordinate
`[inf_{s ∈ S} sᵢ, sup_{s ∈ S} sᵢ]`. Defined for every set, as `sInf`/`sSup` are; it is the
smallest box only for a nonempty bounded `S`, which `hull_isLeast` assumes.

## Inputs
* `S` – set of points

## Output
* the smallest box containing `S`

## References

* [1] W. Tang, Z. Wang, Y. Wang, T. Raïssi and Y. Shen. "Interval estimation methods for
      discrete-time linear time-invariant systems". IEEE Transactions on Automatic Control,
      64(11):4717-4724, 2019.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `Box(S)`, coordinate by coordinate. -/
noncomputable def Interval.hull (S : Set (Vec ℝ n)) : Interval (Vec ℝ n) where
  inf := fun i => sInf ((fun x : Vec ℝ n => x i) '' S)
  sup := fun i => sSup ((fun x : Vec ℝ n => x i) '' S)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
