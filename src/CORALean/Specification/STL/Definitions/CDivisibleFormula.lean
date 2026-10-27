module

public import CORALean.Specification.STL.STL

@[expose] public section

/-!
# STL formulas, and the c-divisible ones

`IsStl φ`: `φ` is built from [1, Sec. 2.2]'s `p | ¬ϕ | ϕ₁ ∨ ϕ₂ | ϕ₁ U[a,b] ϕ₂` alone, without the
window operators of `Sec. 4.1`. `IsCDivisible c φ` is [1, Lemma 4]'s "`c` divides all bounds of
temporal operators of `ϕ`": every bound is a natural multiple of `c`.

## Inputs
* none

## Output
* the formula uses only the operators of STL

## References

* [1] [H. Roehm, J. Oehlerking, T. Heinz and M. Althoff. "STL Model Checking of Continuous and
      Hybrid Systems". Automated Technology for Verification and Analysis,
      2016.](../../../../../references/2016/roehm-atva-stl-model-checking.md)
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open scoped NNReal

variable {X : Type}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `φ` uses only the operators of [1, Sec. 2.2]. -/
def STL.Formula.IsStl : STL.Formula X → Prop
  | .atom _ => True
  | .not φ => φ.IsStl
  | .or φ ψ => φ.IsStl ∧ ψ.IsStl
  | .until _ _ φ ψ => φ.IsStl ∧ ψ.IsStl
  | .finOpen _ _ => False
  | .globOpen _ _ => False

/-- Every bound of a temporal operator of `φ` is a multiple of `c`. -/
def STL.Formula.IsCDivisible (c : ℝ≥0) : STL.Formula X → Prop
  | .atom _ => True
  | .not φ => φ.IsCDivisible c
  | .or φ ψ => φ.IsCDivisible c ∧ ψ.IsCDivisible c
  | .until a b φ ψ => (∃ i : ℕ, a = i * c) ∧ (∃ j : ℕ, b = j * c) ∧ φ.IsCDivisible c ∧
      ψ.IsCDivisible c
  | .finOpen d φ => (∃ k : ℕ, d = k * c) ∧ φ.IsCDivisible c
  | .globOpen d φ => (∃ k : ℕ, d = k * c) ∧ φ.IsCDivisible c


end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
