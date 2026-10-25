module

public import CORALean.Global.Float.PowUp
public import CORALean.ContSet.PolyZonotope.Float.Operations.IndepFactors
public import CORALean.ContSet.PolyZonotope.Float.Operations.InnerGeneral

@[expose] public section

/-!
# `PolyZonotope.containsPointApprox`

The point branch of CORA's `@polyZonotope/contains_` with `'approx'`: a point equal to the center
is contained; otherwise `aux_containsInterval`, [1, Alg. 3] (`innerGeneral`), tries to prove the
point box inside the image of `[-1, 1]ᵖ⁺ᵍ` under `aux_funcPoly` (`indepFactors`), from the box
`x ± 1e-10` around a start point `x`. CORA finds `x` by `fmincon`; here it is the caller's
`start`. CORA's center shortcut `withinTol(S(:,i), pZ.c)` accepts a point `1e-8` away; here the
point must equal the center and no column of `E` be zero. `true` is only returned where the
error box holds `0`; `false` decides nothing.

## Inputs
* `pZ` – polynomial zonotope
* `s` – point
* `start` – starting point of the factor search
* `inv` – matrix inverse routine
* `iter` – number of iterations

## Output
* Boolean, true only if the point is shown to lie in the set

## References

* [1] O. Mullier, É. Goubault, M. Kieffer and S. Putot. "General Inner Approximation of
      Vector-valued Functions". Reliable Computing, 2013.
-/

-- Authors:       Claude Opus 5.5
-- Written:       10-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `true` proves that the point `s` lies in `pZ`. -/
def PolyZonotope.containsPointApprox (pZ : PolyZonotope (Vec 𝕋 n)) (s : Vec 𝕋 n)
    (start : Vec 𝕋 (pZ.p + pZ.q)) (inv : {k : ℕ} → Mat 𝕋 k k → Mat 𝕋 k k) (iter : ℕ) : Bool :=
  -- fHan = aux_funcPoly(x, c, G, GI, E)
  let pZd : PolyZonotope (Vec 𝕋 n) := pZ.indepFactors
  -- X = interval(-onesVec, onesVec)
  let X : Interval (Vec 𝕋 (pZ.p + pZ.q)) := ⟨fun _ => neg one, fun _ => one⟩
  -- res(i) = all(withinTol(S(:,i), pZ.c)), exactly, and the center in the set
  let atCenter : Bool := ((List.finRange n).all fun i => le (s i) (pZ.c i) && le (pZ.c i) (s i))
    && (List.finRange pZ.h).all fun l => (List.finRange pZ.p).any fun k => pZ.E k l != 0
  -- Y = interval(S(:,i))
  let Y : Interval (Vec 𝕋 n) := Interval.point s
  -- X_ = interval(x - 1e-10, x + 1e-10)
  let δ : 𝕋 := divUp one (powUp (nsmulUp 10 one) 10)
  let X₀ : Interval (Vec 𝕋 (pZ.p + pZ.q)) :=
    ⟨fun k => subDown (start k) δ, fun k => addUp (start k) δ⟩
  -- the error box holds `0`
  ((List.finRange n).all fun i => le (pZ.I_error.inf i) zero && le zero (pZ.I_error.sup i)) &&
    (atCenter || PolyZonotope.innerGeneral pZd X X₀ Y inv iter)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
