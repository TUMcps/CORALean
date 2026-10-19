module

public import CORALean.ContSet.ConPolyZono.Real.Operations.ConvHullA
public import CORALean.ContSet.ConPolyZono.Real.Operations.ConvHullB
public import CORALean.ContSet.ConPolyZono.Real.Operations.ConvHullR
public import CORALean.ContSet.PolyLevelSet.Real.PolyLevelSet

@[expose] public section

/-!
# `ConPolyZono.convHullCons`

The constraint of [1, Prop. 9]'s weighted copies as a polynomial level set: one copy of the
equations per block of factors, then the row fixing the weights' sum, all equations
(`convHullA`, `convHullR`, `convHullB`).

## References

* [1] N. Kochdumper and M. Althoff. "Constrained Polynomial Zonotopes". Acta
      Informatica, 2023.
-/

-- Authors:       Claude Opus 5.5
-- Written:       18-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {p : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `a` copies of the equations `P`, each on its own factors, and the weight row. -/
def ConPolyZono.convHullCons (a : ℕ) (P : PolyLevelSet p) : PolyLevelSet (a * p + a) :=
  ⟨a * P.m + 1, a * P.q + a, ConPolyZono.convHullA a P.A, ConPolyZono.convHullR a P.R,
    ConPolyZono.convHullB a P.b, fun _ => .eq⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
