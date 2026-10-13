module

public import CORALean.Global.DiscardTree
public import Mathlib.Data.List.MinMax

@[expose] public section

/-!
# `optimalDiscard`

[1, Alg. A*], which discards `k` constraints optimally: Step 2, after `k` levels of `discardTree`,
returns a problem `D^r_{N-k}` of least `w(D^r_{N-k}) ≤ w(D^j_{N-k})`, `j = 1, …, M_k`. The first of
the least, `List.argmin`, and `none` where level `k` is empty: a problem with no support constraint
has no child, and the pseudo-code then has nothing to return.
## References

* [1] M. C. Campi, G. Calafiore and S. Garatti. "Interval predictor models: Identification and
      reliability". Automatica, 45(2):382-392, 2009.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       11-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {N : ℕ} {β : Type} [LinearOrder β]


-- =====================================  MAIN DEFINITION  ====================================== --

def optimalDiscard (w : Finset (Fin N) → β) (D : Finset (Fin N)) (k : ℕ) :
    Option (Finset (Fin N)) :=
  (discardTree w D k).argmin w                                            -- w(D^r_{N-k}) least

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
