module

public import CORALean.ContSet.Zonotope.Real.Zonotope
public import CORALean.Global.Tensor
public import Mathlib.Data.Matrix.Mul

@[expose] public section

/-!
# `Zonotope.faultResidual`

The residual zonotope of [1, Eq. 11]: from the state zonotope `X̂_{k+1} = ⟨p_{k+1}, H_{k+1}⟩`,
the output `y_{k+1}` and the weighting matrix `M`, `R_{k+1} = ⟨p^r_{k+1}, H^r_{k+1}⟩` with
`p^r_{k+1} = M(y_{k+1} - C p_{k+1})` (11a) and `H^r_{k+1} = [M C H_{k+1}  M D_y H_v]` (11b), the
residuals `M(y_{k+1} - C x)` the fault-free outputs of the states in `X̂_{k+1}` can give, about
the estimate `p_{k+1}`. The fault test [1, Eq. 31] asks whether `0` lies in it.

## Inputs
* `M` – weighting matrix
* `C` – output matrix
* `Dy` – noise matrix
* `Hv` – noise generator matrix
* `y` – measured output
* `X` – state zonotope

## Output
* residual zonotope of the fault-free outputs

## References

* [1] Y. Wang, M. Zhou, V. Puig, G. Cembrano and Z. Wang. "Zonotopic Fault Detection Observer with
      H₋ Performance". 2017 36th Chinese Control Conference (CCC), 2017.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {n ny nv rv : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def Zonotope.faultResidual (M : Mat ℝ ny ny) (C : Mat ℝ ny n) (Dy : Mat ℝ ny nv)
    (Hv : Mat ℝ nv rv) (y : Vec ℝ ny) (X : Zonotope (Vec ℝ n)) : Zonotope (Vec ℝ ny) :=
  let p_r := M *ᵥ (y - C *ᵥ X.c)                                         -- Eq. 11a
  let H_X : Fin X.h → Vec ℝ ny := fun j => M *ᵥ (C *ᵥ X.G j)             -- M C H_{k+1}
  let H_V : Fin rv → Vec ℝ ny := fun j i => (M * Dy * Hv) i j           -- M D_y H_v
  { h := X.h + rv
    c := p_r
    G := Fin.append H_X H_V }                                            -- Eq. 11b

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
