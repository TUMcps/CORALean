module

public import CORALean.ContDynamics.NonlinearSys.Definitions.PolyAbstractionError
public import CORALean.ContDynamics.NonlinearSys.Operations.PrecompStatError
public import CORALean.ContSet.PolyZonotope.Real.Theorems.QuadMapDepPoint
public import Mathlib.Tactic.Abel

@[expose] public section

/-!
# `precompStatError` certifies whatever is left over

The certificate the polynomialization variant runs on: the caller says how far the field
departs from its second-order expansion — one set `W` covering every state in `Ba` and every
input in `U` — and `precompStatError` is then a dependency-preserving abstraction error for it.
That hypothesis is what CORA computes as `error_thirdOrder_dyn` and the higher-order remainder
in `priv_abstrerr_poly`, and the only place the field is touched: `Q` is data, so a wrong
Hessian yields a `W` nothing can satisfy rather than an unsound certificate. `hp` is `rfl`:
`quadMapDep` keeps the factor count it was handed.

## Inputs
* `f` – field
* `A` – state Jacobian
* `B` – input Jacobian
* `xs` – state expansion point
* `us` – input expansion point
* `pZ` – region polynomial zonotope
* `Ba` – factor domain
* `U` – input region
* `W` – remainder polynomial zonotope
* `Q` – halved Hessian family

## Hypotheses
* `hW` – remainder lies in the covering set

## Conclusion
* the second-order term plus the cover is a polynomial certificate
-/

-- Authors:       Claude Opus 5
-- Written:       07-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix Real.PolyZonotope

variable {n m : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

section
variable {n : ℕ}

/-- The value at `a` is the second-order term at the state `a` names. -/
theorem aux_precompStatError_point (Q : Fin n → Mat ℝ n n) (xs : Vec ℝ n)
    (pZ : Real.PolyZonotope (Vec ℝ n)) (a : Fin pZ.p → ℝ) : -- --- CONCL ---
    (precompStatError Q xs pZ).point a = quadEval Q (pZ.point a - xs) := by -- --- PROOF ---
  -- the shifted set has `pZ`'s monomials and generators, so only the center moves
  have hshift : ({ pZ with c := pZ.c - xs } : Real.PolyZonotope (Vec ℝ n)).point a
      = pZ.point a - xs := by
    show pZ.c - xs + ∑ i, Real.PolyZonotope.monomial pZ.E a i • pZ.G i
        = pZ.c + ∑ i, Real.PolyZonotope.monomial pZ.E a i • pZ.G i - xs
    abel
  have h := Real.PolyZonotope.quadMapDep_point Q
    ({ pZ with c := pZ.c - xs } : Real.PolyZonotope _) a
  rw [hshift] at h
  exact h

end


-- =======================================  MAIN THEOREM  ======================================= --

/-- The second-order term, plus whatever `W` covers, is a certificate over
`pZ`'s own factors. -/
theorem PolyAbstractionError.of_quadRemainder {f : Vec ℝ n → Vec ℝ m → Vec ℝ n}
    {A : Mat ℝ n n} {B : Mat ℝ n m} {xs : Vec ℝ n} {us : Vec ℝ m}
    {pZ : Real.PolyZonotope (Vec ℝ n)} {Ba : Set (Fin pZ.p → ℝ)} {U : Set (Vec ℝ m)}
    {W : Real.PolyZonotope (Vec ℝ n)} (Q : Fin n → Mat ℝ n n)
    (hW : ∀ a ∈ Ba, ∀ u ∈ U,
      f (pZ.point a) u - (f xs us + A *ᵥ (pZ.point a - xs) + B *ᵥ (u - us))
        - quadEval Q (pZ.point a - xs) ∈ W.construct) :
    PolyAbstractionError f A B xs us pZ Ba U (precompStatError Q xs pZ) rfl W where
  encloses a ha u hu := by
    -- `Fin.cast rfl` is the identity, so the certificate reads at `a` itself
    rw [aux_precompStatError_point]
    exact hW a ha u hu

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
