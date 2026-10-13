import CORALean.ContDynamics.NonlinDASys.NonlinDASys
import CORALean.ContSet.Zonotope.Real.Operations.Plus
import CORALean.ContSet.Zonotope.Real.Operations.Mtimes
import CORALean.ContSet.Zonotope.Real.Operations.OfPoint

/-!
# `NonlinDASys.enlargeInterfaceInput`

[1, Eq. 14]: the assumed input set of a subsystem, its input set `U⁽ⁱ⁾` enlarged by the factor
`λ_U` about its centre `ĉ_U⁽ⁱ⁾` in the interface coordinates only:

`Û⁽ⁱ⁾ = ĉ_U⁽ⁱ⁾ ⊕ ((λ_U - 1) Λ⁽ⁱ⁾ + I) (U⁽ⁱ⁾ ⊕ (-ĉ_U⁽ⁱ⁾))`,

`Λ⁽ⁱ⁾` the diagonal matrix of ones at the interface inputs and zeros elsewhere (here any
matrix; [1] means a diagonal one). With `Λ = I` it is the enlargement of [1, Eq. 12].

## References

* [1] M. Althoff. "Formal and Compositional Analysis of Power Systems using Reachable Sets".
      IEEE Transactions on Power Systems, 29(5):2270-2280, 2014.
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real Matrix

variable {m : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- [1, Eq. 14]: `Û = ĉ ⊕ ((λ_U - 1) Λ + I)(U ⊕ (-ĉ))`. -/
def NonlinDASys.enlargeInterfaceInput (lamU : ℝ) (Λ : Mat ℝ m m) (c : Vec ℝ m)
    (U : Zonotope (Vec ℝ m)) : Zonotope (Vec ℝ m) :=
  let shifted : Zonotope (Vec ℝ m) := U.plus (Zonotope.ofPoint (-c))        -- U ⊕ (-ĉ)
  let scaled : Zonotope (Vec ℝ m) :=                                        -- ((λ_U - 1)Λ + I)(·)
    Zonotope.mtimes ((lamU - 1) • Λ + 1) shifted
  scaled.plus (Zonotope.ofPoint c)                                          -- ĉ ⊕ (·)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
