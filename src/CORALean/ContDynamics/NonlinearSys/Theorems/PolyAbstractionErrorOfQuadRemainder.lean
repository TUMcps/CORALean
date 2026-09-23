import CORALean.ContDynamics.NonlinearSys.Definitions.PolyAbstractionError
import CORALean.ContDynamics.NonlinearSys.Theorems.PrecompStatErrorPoint

/-!
# `precompStatError` certifies whatever is left over

The certificate the polynomialization variant runs on, assembled: the caller
says how far the field departs from its second-order expansion — one set `W`
covering every state in `Ba` and every input in `U` — and `precompStatError` is
then a dependency-preserving abstraction error for it.

That hypothesis is what CORA computes as `error_thirdOrder_dyn` and the
higher-order remainder in `priv_abstrerr_poly`, and it is the only place the
field is touched: `Q` is data, so a wrong Hessian yields a `W` nothing can
satisfy rather than an unsound certificate. At a field quadratic in the state and
affine in the input, `W` is a point.

`hp` is `rfl`: `precompStatError` runs `quadMapDep`, whose factor count is the
one it was handed, so "the same factors" holds definitionally rather than by a
cast.
-/

-- Authors:       Tobias Ladner
-- Written:       07-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix Real.PolyZonotope

variable {n m : ℕ}


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
    rw [precompStatError_point]
    exact hW a ha u hu

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
