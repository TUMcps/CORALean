import CORALean.Global.Float.PowUp

/-!
# Eq. (54): the interpolated gain, in floats

`interpGain` in `𝕋`. Tuning only: the value picks a step size, an order or a gain and no soundness
statement reads it, so every rounding is upward and no theorem is owed. What a run guarantees
holds for whatever this returns. See [1].

## References

* [1] M. Wetzlinger, A. Kulmburg, A. Le Penven and M. Althoff. "Adaptive
      Reachability Algorithms for Nonlinear Systems Using Abstraction Error
      Analysis". Nonlinear Analysis: Hybrid Systems, vol. 46, 2022, p. 101252.
-/

-- Authors:       Tobias Ladner
-- Written:       08-October-2026
-- Last update:   ---
-- Last revision: ---


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
