import CORALean.ContSet.ConPolyZono.Real.Operations.RepVec
import CORALean.ContSet.ConPolyZono.Real.ConPolyZono

/-!
# `ConPolyZono.convHullB`

The constraint bound of [1, Prop. 9]: the linear combination's, once per copy,
and `1 - a` for the weight row. Each weight enters shifted — the factor `λ` of a
copy stands for the weight `1 + λ` — so the `a` weights sum to `1` exactly when
the factors sum to `1 - a`, which is [1]'s `-n` at `a = n + 1`.

The bound stays an `Interval`, as the representation's `b` is throughout; the
weight row is a point interval, an equality having no direction to round in.

## References

* [1] N. Kochdumper and M. Althoff. "Constrained Polynomial Zonotopes". Acta
      Informatica, 2023.
-/

-- Authors:       Claude Opus 5
-- Written:       13-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

/-- One copy of `b` per block, then the weight row's `1 - a`. -/
def ConPolyZono.convHullB (a : ℕ) {m : ℕ} (b : Interval (Vec ℝ m)) :
    Interval (Vec ℝ (a * m + 1)) :=
  ⟨Fin.append (ConPolyZono.repVec a b.inf) (fun _ => 1 - (a : ℝ)),
    Fin.append (ConPolyZono.repVec a b.sup) (fun _ => 1 - (a : ℝ))⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
