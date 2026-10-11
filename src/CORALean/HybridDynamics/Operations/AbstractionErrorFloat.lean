import CORALean.ContDynamics.LinearSys.MatExp.Operations.ExpRemainderBoundFloat
import CORALean.ContDynamics.LinearSys.MatExp.Operations.InvFactorialBoundsFloat
import CORALean.ContDynamics.LinearSys.MatExp.Operations.NormUpperBoundFloat
import CORALean.ContSet.Conversion.Float.Interval_to_Zonotope
import CORALean.ContSet.Interval.Float.Operations.MatPow
import CORALean.ContSet.Interval.Float.Operations.Smul
import CORALean.ContSet.Zonotope.Float.Operations.MtimesIntervalMat
import CORALean.ContSet.Zonotope.Float.Operations.Recentre
import CORALean.ContSet.Zonotope.Float.Operations.SumTerms
import CORALean.Global.Float.PowDown
import CORALean.Global.Float.PowUp

/-!
# The abstraction error of the state-dependent constant flow, over a floating-point scalar

`GuardMap.abstractionError`, CORA's `aux_abstractionError` [1], at float zonotopes, one `let`
per line of the code: `τ(err₁ ⊕ err₂ ⊕ err₃) ⊕ Ê R₀ ⊕ Ê tmax U`, `τ = [0, tmax]`. Every
coefficient that rounds is an interval: `Aⁱ` is `matPow` at the point interval matrix of `A`,
`1/i!` is `invFactorialBounds`, the powers of `th` and `tmax` are `powDown`/`powUp` (both are
nonnegative where the enclosure is claimed), and `−thⁱ ξ` is a box. The products are the float
`mtimesIntervalMat`. `err1` accumulates its summands, as in the exact layer.

`W` departs from CORA, which computes `|e^{|A|tmax} − ∑ᵢ₌₀^η (|A|tmax)ⁱ/i!|` with a rounded
`expm`: here every entry of `W` is `MatExp.expRemainderBound` at a float bound of `‖tmax A‖`,
a sound bound on each entry of `e^{Aτ} − ∑ᵢ₌₀^η (Aτ)ⁱ/i!` for `τ ∈ [0, tmax]` whenever that
norm bound is at most `(η + 2)/2`, which the enclosure theorem takes as a float test.

## References

* [1] `hybridDynamics/@location/guardIntersect_hyperplaneMap.m`, `aux_abstractionError`
-/

-- Authors:       Tobias Ladner
-- Written:       11-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float CORALean.Float.FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `err = aux_abstractionError(A,U,R0,th,tmax,order)`, with `err1` accumulated, at floats. -/
def GuardMap.abstractionErrorFloat (A : Mat 𝕋 n n) (U R₀ : Zonotope 𝕋 n) (th tmax : 𝕋)
    (η : ℕ) : Zonotope 𝕋 n :=
  -- `[a, b] * Z` of a float interval and a zonotope, as the interval matrix `[a, b] I`
  let mulI : 𝕋 → 𝕋 → Interval (Mat 𝕋 n n) := fun a b =>
    Interval.smul a b (Interval.point (diagonalBlock fun _ => one))
  let Apow : ℕ → Interval (Mat 𝕋 n n) := fun i =>                -- `A^i`, bracketed
    Interval.matPow (Interval.point A) i
  let M₁ : ℕ → Interval (Mat 𝕋 n n) := fun m =>                  -- `A^(m+2)/(m+2)!`
    Interval.smul (MatExp.invFactorialBounds (m + 2)).1 (MatExp.invFactorialBounds (m + 2)).2
      (Apow (m + 2))
  let M₂ : ℕ → Interval (Mat 𝕋 n n) := fun m =>                  -- `A^(m+1)/(m+2)!`
    Interval.smul (MatExp.invFactorialBounds (m + 2)).1 (MatExp.invFactorialBounds (m + 2)).2
      (Apow (m + 1))
  let tmaxHi : ℕ → 𝕋 := fun m => powUp tmax (m + 1)             -- `tmax^(m+1)`, up
  let thLo : ℕ → 𝕋 := fun m => powDown th (m + 1)               -- `th^(m+1)`, down
  let thHi : ℕ → 𝕋 := fun m => powUp th (m + 1)                 -- and up
  let nrm := MatExp.normUpperBound (Interval.smul tmax tmax (Interval.point A))  -- `‖tmax A‖`
  let W : Mat 𝕋 n n := fun _ _ => MatExp.expRemainderBound nrm η  -- W, entrywise
  let What : Interval (Mat 𝕋 n n) := ⟨fun j k => neg (W j k), W⟩ -- e_hat = interval(-W,W)
  let xi := R₀.c                                                  -- xi = center(R0)
  let u := U.c                                                    -- u = center(U)
  let U_ := U.recentre                                            -- U_ = U - u
  let err1 := Zonotope.sumTerms (fun m =>                         -- for i = 2:order
    Zonotope.mtimesIntervalMat (M₁ m)
      ((Zonotope.mtimesIntervalMat (mulI zero (tmaxHi m)) R₀).plus
        (⟨fun i => Interval.mulLo (neg (thHi m)) (neg (thLo m)) (xi i) (xi i),
          fun i => Interval.mulHi (neg (thHi m)) (neg (thLo m)) (xi i) (xi i)⟩ :
            Interval (Vec 𝕋 n)).zonotope)) (η - 1)               -- M*(tau_pow*R0 - th_pow*xi)
  let err2 := Zonotope.sumTerms (fun m =>                         -- for i = 1:order
    Zonotope.mtimesIntervalMat
      (Interval.smul (neg (thHi m)) (subUp (tmaxHi m) (thLo m)) (M₂ m))
      (Zonotope.point u)) η                                       -- M*(tau_pow - th_pow)*u
  let err3 := U_.plus (Zonotope.sumTerms (fun m =>                -- for i = 1:order
    Zonotope.mtimesIntervalMat (Interval.smul zero (tmaxHi m) (M₂ m)) U_) η)  -- U_ + M*tau_pow*U_
  ((Zonotope.mtimesIntervalMat (mulI zero tmax) ((err1.plus err2).plus err3)).plus
    (Zonotope.mtimesIntervalMat What R₀)).plus                    -- tau*(...) + e_hat*R0
    (Zonotope.mtimesIntervalMat (Interval.smul tmax tmax What) U)  -- + e_hat*tmax*U

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
