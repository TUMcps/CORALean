import CORALean.Specification.STL.STL

/-!
# STL formulas, and the c-divisible ones

`IsStl φ`: `φ` is built from [1, Sec. 2.2]'s `p | ¬ϕ | ϕ₁ ∨ ϕ₂ | ϕ₁ U[a,b] ϕ₂` alone, without the
window operators of `Sec. 4.1`. `CDivisible c φ` is [1, Lemma 4]'s "`c` divides all bounds of
temporal operators of `ϕ`": every bound is a natural multiple of `c`.

## References

* [1] H. Roehm, J. Oehlerking, T. Heinz and M. Althoff. "STL Model Checking of Continuous and
      Hybrid Systems". ATVA, LNCS 9938, pp. 412-427, 2016.
-/

-- Authors:       Tobias Ladner
-- Written:       04-October-2026
-- Last update:   ---
-- Last revision: ---


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
def STL.Formula.CDivisible (c : ℝ≥0) : STL.Formula X → Prop
  | .atom _ => True
  | .not φ => φ.CDivisible c
  | .or φ ψ => φ.CDivisible c ∧ ψ.CDivisible c
  | .until a b φ ψ => (∃ i : ℕ, a = i * c) ∧ (∃ j : ℕ, b = j * c) ∧ φ.CDivisible c ∧ ψ.CDivisible c
  | .finOpen d φ => (∃ k : ℕ, d = k * c) ∧ φ.CDivisible c
  | .globOpen d φ => (∃ k : ℕ, d = k * c) ∧ φ.CDivisible c


end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
