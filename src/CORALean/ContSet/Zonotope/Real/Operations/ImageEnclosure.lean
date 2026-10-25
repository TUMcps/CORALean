module

public import CORALean.ContSet.Zonotope.Real.Operations.Row
public import Mathlib.Data.Fin.Tuple.Basic
public import Mathlib.Algebra.Group.Pi.Basic

@[expose] public section

/-!
# `Zonotope.imageEnclosure`

The image enclosure of a nonlinear layer, [1, Alg. 1] lines 6 and 7 as [1, Prop. 12]'s proof
reads them: per dimension a slope `m(i)` and approximation errors `e(i) ≤ ē(i)` (Def. 7 and
Prop. 10), each a function of that dimension's row `H(i)` (`Zonotope.row`) through its bounds,
give `Diag(m) H ⊕ [e, ē]`: center `m(i) c(i) + ½(e(i) + ē(i))`, the generators `m(i) G(i, j)`
and after them `n` axis-aligned ones `½(ē(i) - e(i)) eᵢ`. The midpoint is added once (the
printed line 6 adds it before line 7 adds the interval, center and all; see the `Alg. 1` row).
The slope and errors are parameters, so the enclosure is that of whichever activation and
linear approximation supply them.

## Inputs
* `m` – slope function
* `eLo` – lower error function
* `eUp` – upper error function
* `H` – input zonotope

## Output
* zonotope enclosing the neuron image

## References

* [1] L. Koller, T. Ladner and M. Althoff. "Set-Based Training for Neural Network Verification".
      Transactions on Machine Learning Research, 2025.
-/

-- Authors:       Claude Opus 5.5
-- Written:       11-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `Diag(m) H ⊕ [e, ē]`, with `m(i)`, `e(i)`, `ē(i)` read off the row `H(i)`. -/
noncomputable def Zonotope.imageEnclosure (m eLo eUp : Zonotope (Vec ℝ 1) → ℝ)
    (H : Zonotope (Vec ℝ n)) :
    Zonotope (Vec ℝ n) where
  h := H.h + n
  c := fun i => m (H.row i) * H.c i + (eLo (H.row i) + eUp (H.row i)) / 2
  G := Fin.append (fun j i => m (H.row i) * H.G j i)
    (fun i => Pi.single i ((eUp (H.row i) - eLo (H.row i)) / 2))

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
