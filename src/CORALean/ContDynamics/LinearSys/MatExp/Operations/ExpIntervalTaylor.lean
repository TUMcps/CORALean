module

public import CORALean.ContSet.Interval.Real.Operations.MatPow
public import CORALean.ContSet.Interval.Real.Operations.Smul

@[expose] public section

/-!
# Interval matrices: the Taylor truncation

`expIntervalTaylor`: [1, Thm. 1]'s Taylor truncation as an interval matrix, every order by interval
arithmetic, `i = 0 … η` matching `MatExp.expTaylor`'s `Finset.range (η + 1)` exactly.

Not exact: `matPow A k` admits products of *different* members of `A` at different factors, so the
Taylor terms are bounded independently of each other and of any one `M` they might come from —
ordinary interval-arithmetic dependency loss, which [2, Sec. 3.1] limits by evaluating the low
orders dependently.

## Inputs
* `A` – interval matrix

## Output
* interval matrix of the Taylor truncation up to the given order

## References

* [1] M. Althoff, O. Stursberg and M. Buss. "Reachability Analysis of Linear Systems with Uncertain
      Parameters and Inputs". 2007 46th IEEE Conference on Decision and Control, 2007.
* [2] M. Althoff, B. H. Krogh and O. Stursberg. "Analyzing Reachability of Linear Dynamic Systems
      with Parametric Uncertainties". Modeling, Design, and Simulation of Systems with
      Uncertainties, 2011.
-/

-- Authors:       Claude Sonnet 5
-- Written:       06-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The Taylor truncation as an interval matrix, `i = 0 … η` matching
`MatExp.expTaylor`'s `Finset.range (η + 1)` exactly. -/
noncomputable def MatExp.expIntervalTaylor (A : Interval (Mat ℝ n n)) :
    ℕ → Interval (Mat ℝ n n)
  | 0 => Interval.smul ((Nat.factorial 0 : ℝ)⁻¹) (Interval.matPow A 0)
  | k + 1 => Interval.plus
      (Interval.smul ((Nat.factorial (k + 1) : ℝ)⁻¹) (Interval.matPow A (k + 1)))
      (MatExp.expIntervalTaylor A k)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
