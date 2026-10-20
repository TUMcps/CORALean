module

public import CORALean.HybridDynamics.Definitions.IdentHA

@[expose] public section

/-!
# The guard of Prop. 1

[1, Prop. 1]: the guard on the surface `aᵀx = b` into the invariant `⟨C, d⟩_P` under the reset
`r(x) = H x + k` is `⟨a, b, C H, d - C k⟩_H`; `identGuard` gives its rows `(Hᵀcᵢ, dᵢ - cᵢᵀk)`.
Over ℝ, with no float layer: it states the guard for [1, Prop. 1], as CORA's
`priv_identify_decisionTree2automaton` builds it before its emptiness check.

## Inputs
* `H` – reset matrix
* `k` – reset offset
* `cs` – invariant rows

## Output
* guard rows in the source coordinates

## References

* [1] N. Kochdumper, M. A. Foughali, P. Habermehl and E. Asarin. "Robust Identification of
      Hybrid Automata from Noisy Data". In Proc. of the 28th ACM International Conference on
      Hybrid Systems: Computation and Control (HSCC), pp. 1-11, 2025.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- [1, Prop. 1]: the rows `C H`, `d - C k` of the guard into `⟨C, d⟩_P` under `H x + k`. -/
def IdentHA.identGuard (H : Mat ℝ n n) (k : Vec ℝ n) (cs : List (Vec ℝ n × ℝ)) :
    List (Vec ℝ n × ℝ) :=
  cs.map fun q => (Hᵀ *ᵥ q.1, q.2 - q.1 ⬝ᵥ k)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
