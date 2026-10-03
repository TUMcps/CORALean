import CORALean.ContSet.Interval.Real.Interval

/-!
# Contractors

[1, Def. 6]: for the constraint `c(x) = 0`, an operation on boxes is a contractor if the box it
returns lies in the box it was given and keeps every solution of the constraint in it.
[1]'s Sec. 4.2 names implementations (the Box algorithm, HC4revise) without fixing one, so this
is the specification an implementation meets.

## References

* [1] N. Kochdumper and M. Althoff. "Reachability Analysis for Hybrid Systems with Nonlinear
      Guard Sets". In Proc. of the 23rd ACM International Conference on Hybrid Systems:
      Computation and Control (HSCC), 2020.
-/

-- Authors:       Tobias Ladner
-- Written:       03-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `contract(I) ⊆ I` and `∀ x ∈ I, c(x) = 0 ⇒ x ∈ contract(I)`, at every box `I`. -/
def IsContractor (c : Vec ℝ n → ℝ) (contract : Interval (Vec ℝ n) → Interval (Vec ℝ n)) :
    Prop :=
  ∀ I : Interval (Vec ℝ n), (contract I).construct ⊆ I.construct ∧
    ∀ x ∈ I.construct, c x = 0 → x ∈ (contract I).construct

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
