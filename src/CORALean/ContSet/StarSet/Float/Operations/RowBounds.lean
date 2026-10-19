module

public import CORALean.ContSet.Interval.Float.Operations.MulHi
public import CORALean.ContSet.Interval.Float.Operations.MulLo
public import CORALean.ContSet.StarSet.Float.StarSet

@[expose] public section

/-!
# The bounds of one neuron of a float star set

The neuron `j` is `c_j + Σ_k G_jk α_k` with each factor in `[l_k, u_k]`. Each term is bounded by
the corner hull of `G_jk` against `[l_k, u_k]`, the lower bounds summed rounding down and the
upper ones rounding up. These bounds are certified by the rounding alone, not by CORA's center and
radius formula (`Real.StarSet.rowBounds`), whose center is not the one CORA computes.

## Inputs
* `s` – float star set
* `j` – neuron index

## Output
* certified interval bounds of neuron `j`
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   19-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Float Float.FloatOps

variable {𝕋 : Type} [Float.FloatOps 𝕋] [Float.SoundFloatArithmetic 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The lower and the upper bound of neuron `j`, each rounded outward. -/
def StarSet.rowBounds (s : StarSet 𝕋 n) (j : Fin n) : Interval 𝕋 :=
  ⟨addDown (s.c j)
      (sumDown fun k => Interval.mulLo (s.G j k) (s.G j k) (s.dom.inf k) (s.dom.sup k)),
   addUp (s.c j) (sumUp fun k => Interval.mulHi (s.G j k) (s.G j k) (s.dom.inf k) (s.dom.sup k))⟩

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
