module

public import CORALean.ContSet.Interval.Real.Operations.ExtremalLo
public import CORALean.ContSet.Interval.Real.Operations.ExtremalHi
public import CORALean.ContSet.Interval.Real.Operations.PolyBoxReviseLeft
public import CORALean.ContSet.Interval.Real.Operations.PolyBoxReviseRight
public import Mathlib.Logic.Function.Basic

@[expose] public section

/-!
# `Interval.polyBoxRevise`

[1, Sec. 3 (PolyBoxRevise)] in the polynomial case, `hᵢ(x) = xⁱ`: the constraint
`f(z) = Σᵢ fᵢ(z) z_kⁱ = 0` narrows coordinate `k` of the box `B`. `coeff B` is the box of
coefficients `[cᵢ] = [fᵢ]_N([Y])` an interval extension gives; from it the two extremal
functions, then the two bounds by the three cases, each search supplied (`BoxNarrow`, or
Cardano's formulas below degree four). The new interval is intersected with the old, as CORA's
`contractPolyBoxRevise` does with `& dom`, so a search landing outside `[x]` costs nothing.

## References

* [1] G. Trombettoni, Y. Papegay, G. Chabert and O. Pourtallier. "A Box-Consistency Contractor
      Based on Extremal Functions". In Proc. of the 16th International Conference on Principles
      and Practice of Constraint Programming (CP 2010), LNCS 6308, pp. 491-498, 2010.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `B` with coordinate `k` narrowed to `[max x̲ l, min x̅ r]`. -/
noncomputable def Interval.polyBoxRevise {d : ℕ}
    (coeff : Interval (Vec ℝ n) → Interval (Vec ℝ (d + 1))) (k : Fin n)
    (rootL rootR : (ℝ → ℝ) → ℝ → ℝ → ℝ) (B : Interval (Vec ℝ n)) : Interval (Vec ℝ n) :=
  let C := coeff B                                                -- `[cᵢ] = [fᵢ]_N([Y])`
  let gLo := fun x : ℝ => C.extremalLo (fun i => x ^ (i : ℕ))     -- `g̲[Y]`
  let gHi := fun x : ℝ => C.extremalHi (fun i => x ^ (i : ℕ))     -- `g̅[Y]`
  let l := Interval.polyBoxReviseLeft gLo gHi rootL (B.inf k) (B.sup k)
  let r := Interval.polyBoxReviseRight gLo gHi rootR (B.inf k) (B.sup k)
  { inf := Function.update B.inf k (max (B.inf k) l)
    sup := Function.update B.sup k (min (B.sup k) r) }

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
