module

public import CORALean.Global.Float.PowUp

@[expose] public section

/-!
# Eq. (54): the interpolated gain, in floats

`interpGain` in `𝕋`. Tuning only: the value picks a step size, an order or a gain and no soundness
statement reads it, so every rounding is upward and no theorem is owed. What a run guarantees
holds for whatever this returns. See [1].

## Inputs
* `ζδ` – limit gain
* `φ1` – gain at the horizon
* `j` – interpolation index

## Output
* the interpolated gain in floats

## References

* [1] M. Wetzlinger, A. Kulmburg, A. Le Penven and M. Althoff. "Adaptive Reachability Algorithms for
      Nonlinear Systems Using Abstraction Error Analysis". Nonlinear Analysis: Hybrid Systems, 2022.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       08-October-2026
-- Last update:   ---
-- Reviewed:      15-October-2026 (Tobias Ladner)


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float FloatOps

variable {𝕋 : Type} [FloatOps 𝕋]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `φ(j+1)` of eq. (54): the gain interpolated between `φ⁽¹⁾` at the horizon
and the limit gain `ζ_δ`. -/
def interpGainFloat (ζδ φ1 : 𝕋) (j : ℕ) : 𝕋 :=
  addUp ζδ (mulUp (subUp φ1 ζδ) (powUp ζδ j))

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
