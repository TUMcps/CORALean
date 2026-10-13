module

public import CORALean.Global.Float.FloatOps

@[expose] public section

/-!
# `min(l_k)`: the smallest of a layer's lower bounds

The other end of [1, Alg. 1, line 1]'s spread, and `maxOver` reflected: a fold of `minimum`,
exact, and `zero` over a layer with no neurons.

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

/-- `min(l_k)`, exact, and `zero` over a layer with no neurons. -/
def minOver : {n : ℕ} → Vec 𝕋 n → 𝕋
  | 0, _ => zero
  | _ + 1, v => Fin.foldl _ (fun a i => minimum a (v i)) (v 0)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
