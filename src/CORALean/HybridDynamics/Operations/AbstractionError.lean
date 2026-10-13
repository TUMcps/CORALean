module

public import CORALean.ContDynamics.LinearSys.MatExp.Definitions.ExpRemainderMat
public import CORALean.ContSet.Interval.Real.Operations.MulLo
public import CORALean.ContSet.Interval.Real.Operations.MulHi
public import CORALean.ContSet.Zonotope.Real.Operations.Mtimes
public import CORALean.ContSet.Zonotope.Real.Operations.MtimesIntervalMat
public import CORALean.ContSet.Zonotope.Real.Operations.OfPoint
public import CORALean.ContSet.Zonotope.Real.Operations.Recentre
public import CORALean.ContSet.Zonotope.Real.Operations.SumTerms

@[expose] public section

/-!
# The abstraction error of the state-dependent constant flow, with uncertain inputs

CORA's `aux_abstractionError` [1], the set `E` of [2, Eq. 13] holding `x(t) − y(t)`, `t ∈ [0,
tmax]`, for a run of `ẋ = Ax + u`, `u ∈ U`, from `x₀ ∈ R₀` and the flow `x₀ + (Ax₀ + b)t` of
[2, Prop. 1] at `th`: `τ(err₁ ⊕ err₂ ⊕ err₃) ⊕ Ê R₀ ⊕ Ê tmax U`, `τ = [0, tmax]`, `Ê = [−W, W]`,
`W = |e^{|A|tmax} − ∑ᵢ₌₀^η (|A|tmax)ⁱ/i!|`. Interval products are CORA's (`Interval.mulLo`,
`Interval.mulHi`, `Zonotope.mtimesIntervalMat`; `[a, b] Z` as `[a, b] I` times `Z`). `err1`
accumulates its summands, which CORA's assignment `err1 = M * (...)` in the loop does not
(FINDINGS.md, `Location guardIntersect_hyperplaneMap, abstraction error and quadratic map`).

## References

* [1] `hybridDynamics/@location/guardIntersect_hyperplaneMap.m`, `aux_abstractionError`
* [2] M. Althoff and B. H. Krogh. "Avoiding Geometric Intersection Operations in
      Reachability Analysis of Hybrid Systems". In Proc. of the 15th ACM
      International Conference on Hybrid Systems: Computation and Control (HSCC),
      2012, pp. 45-54.
-/

-- Authors:       Claude Opus 5.5
-- Written:       11-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real Matrix

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `err = aux_abstractionError(A,U,R0,th,tmax,order)`, with `err1` accumulated. -/
noncomputable def GuardMap.abstractionError (A : Mat ℝ n n) (U R₀ : Zonotope (Vec ℝ n))
    (th tmax : ℝ) (η : ℕ) : Zonotope (Vec ℝ n) :=
  -- `[lo, hi] * [a, b]` of an interval matrix and a real interval, entry by entry
  let mulI : Mat ℝ n n → Mat ℝ n n → ℝ → ℝ → Interval (Mat ℝ n n) := fun lo hi a b =>
    ⟨Matrix.of fun j k => Interval.mulLo (lo j k) (hi j k) a b,
      Matrix.of fun j k => Interval.mulHi (lo j k) (hi j k) a b⟩
  let W : Mat ℝ n n := fun j k => |MatExp.expRemainderMat A tmax η j k|  -- W = abs(expm - M)
  let xi := R₀.c                                                    -- xi = center(R0)
  let u := U.c                                                      -- u = center(U)
  let U_ := U.recentre                                              -- U_ = U - u
  let err1 := Zonotope.sumTerms (fun m =>                           -- for i = 2:order
    Zonotope.mtimes (((Nat.factorial (m + 2) : ℝ)⁻¹) • A ^ (m + 2))
      ((Zonotope.mtimesIntervalMat (mulI 1 1 0 (tmax ^ (m + 1))) R₀).plus
        (Zonotope.ofPoint (-(th ^ (m + 1)) • xi)))) (η - 1)      -- M*(tau_pow*R0 - th_pow*xi)
  let err2 := Zonotope.sumTerms (fun m =>                           -- for i = 1:order
    Zonotope.mtimesIntervalMat
      (mulI (((Nat.factorial (m + 2) : ℝ)⁻¹) • A ^ (m + 1))
        (((Nat.factorial (m + 2) : ℝ)⁻¹) • A ^ (m + 1))
        (-(th ^ (m + 1))) (tmax ^ (m + 1) - th ^ (m + 1)))
      (Zonotope.ofPoint u)) η                                       -- M*(tau_pow - th_pow)*u
  let err3 := U_.plus (Zonotope.sumTerms (fun m =>                  -- for i = 1:order
    Zonotope.mtimesIntervalMat
      (mulI (((Nat.factorial (m + 2) : ℝ)⁻¹) • A ^ (m + 1))
        (((Nat.factorial (m + 2) : ℝ)⁻¹) • A ^ (m + 1)) 0 (tmax ^ (m + 1)))
      U_) η)                                                        -- U_ + M*tau_pow*U_
  ((Zonotope.mtimesIntervalMat (mulI 1 1 0 tmax) ((err1.plus err2).plus err3)).plus
    (Zonotope.mtimesIntervalMat ⟨-W, W⟩ R₀)).plus                    -- tau*(...) + e_hat*R0
    (Zonotope.mtimesIntervalMat (mulI (-W) W tmax tmax) U)          -- + e_hat*tmax*U

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
