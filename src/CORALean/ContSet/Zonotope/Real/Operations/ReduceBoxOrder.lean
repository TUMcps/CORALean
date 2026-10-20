module

public import CORALean.ContSet.Zonotope.Real.Definitions.ReduceBoxAdmissible
public import Mathlib.Order.Lattice.Nat

@[expose] public section

/-!
# Choosing the reduction order from an admissible error

[1] tunes a reachability run's parameters to an error the caller states rather than to numbers
the caller guesses. This is that choice for the third knob: given a bound `B`, `reduceBoxOrder`
names the least order whose reduction box fits inside it — the shape `MatExp.expRemainderOrder`
gives the truncation order, but against a *set* rather than a scalar `ε`, since that is what a
reduction throws away. `sInf` over ℕ is `Nat.find` under classical decidability, which is what
makes this noncomputable: no `Decidable` instance for set inclusion exists here either.

## Inputs
* `Z` – zonotope
* `B` – admissible bound

## Output
* least order whose box meets the bound

## References

* [1] M. Wetzlinger, N. Kochdumper and M. Althoff. "Adaptive parameter tuning
      for reachability analysis of linear systems". CDC, 2020, pp. 5145–5152.
-/

-- Authors:       Claude Sonnet 5
-- Written:       08-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The least order meeting `B`, and `0` where none does — which `0 ∈ B` rules
out, `reduceBoxOrder_spec` being stated under exactly that. -/
noncomputable def Zonotope.reduceBoxOrder (Z : Zonotope (Vec ℝ n)) (B : Set (Vec ℝ n)) : ℕ :=
  sInf {o : ℕ | Z.ReduceBoxAdmissible B o}

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
