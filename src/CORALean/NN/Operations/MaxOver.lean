module

public import CORALean.Global.Float.FloatOps

@[expose] public section

/-!
# `max(u_k)`: the largest of a layer's upper bounds

[1, Alg. 1, line 1] starts `δmax` at the spread of the layer's bounds, `max(u_k) - min(l_k)`.
A fold of `maximum`, which is exact, so no direction is chosen; a layer with no neurons gives
`zero`, where [1] leaves the maximum of nothing unsaid.

## Inputs
* none

## Output
* largest entry, zero for an empty layer

## References

* [1] T. Ladner and M. Althoff. "Fully Automatic Neural Network Reduction for
      Formal Verification". TMLR. arXiv:2305.01932.
-/

-- Authors:       Claude Opus 5.5
-- Written:       23-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Float Float.FloatOps

variable {𝕋 : Type} [FloatOps 𝕋]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `max(u_k)`, exact, and `zero` over a layer with no neurons. -/
def maxOver : {n : ℕ} → Vec 𝕋 n → 𝕋
  | 0, _ => zero
  | _ + 1, v => Fin.foldl _ (fun a i => maximum a (v i)) (v 0)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
