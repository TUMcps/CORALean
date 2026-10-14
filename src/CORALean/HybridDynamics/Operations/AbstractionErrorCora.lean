module

public import CORALean.ContDynamics.LinearSys.MatExp.Definitions.ExpRemainderMat
public import CORALean.ContSet.Interval.Real.Operations.Basic
public import CORALean.ContSet.Zonotope.Real.Operations.Mtimes
public import CORALean.ContSet.Zonotope.Real.Operations.MtimesIntervalMat
public import CORALean.ContSet.Zonotope.Real.Operations.OfPoint
public import CORALean.ContSet.Zonotope.Real.Operations.Recentre
public import CORALean.ContSet.Zonotope.Real.Operations.SumTerms

@[expose] public section

/-!
# CORA's printed `aux_abstractionError`, with `err1` overwritten

`GuardMap.abstractionError` as CORA's [1] loop runs it: `for i = 2:order`, `M = M * A/i` and
`err1 = M * (tau_pow{i-1}*R0 + (-th_pow{i-1}*xi))`, an assignment, so `err1` leaves the loop as
its last summand `(A^η/η!)(τ^{η−1}R₀ − th^{η−1}ξ)` and drops `(Aⁱ/i!)(τ^{i−1}R₀ − th^{i−1}ξ)`,
`2 ≤ i < η`, of [2, Eq. 13] (`{0}` for `η ≤ 1`, the loop not entered). The fold below overwrites
as the loop does. `err2`, `err3` and the rest are `GuardMap.abstractionError`'s, line for line.
It misses the error (`GuardMap.abstractionErrorCora_counterexample`).

## References

* [1] `hybridDynamics/@location/guardIntersect_hyperplaneMap.m`, `aux_abstractionError`
* [2] M. Althoff and B. H. Krogh. "Avoiding Geometric Intersection Operations in
      Reachability Analysis of Hybrid Systems". In Proc. of the 15th ACM
      International Conference on Hybrid Systems: Computation and Control (HSCC),
      2012, pp. 45-54.
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real Matrix

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `err = aux_abstractionError(A,U,R0,th,tmax,order)` as printed: `err1` overwritten. -/
noncomputable def GuardMap.abstractionErrorCora (A : Mat ℝ n n) (U R₀ : Zonotope (Vec ℝ n))
    (th tmax : ℝ) (η : ℕ) : Zonotope (Vec ℝ n) :=
  -- `[lo, hi] * [a, b]` of an interval matrix and a real interval, entry by entry
  let mulI : Mat ℝ n n → Mat ℝ n n → ℝ → ℝ → Interval (Mat ℝ n n) := fun lo hi a b =>
    ⟨Matrix.of fun j k => Interval.mulLo (lo j k) (hi j k) a b,
      Matrix.of fun j k => Interval.mulHi (lo j k) (hi j k) a b⟩
  let W : Mat ℝ n n := fun j k => |MatExp.expRemainderMat A tmax η j k|  -- W = abs(expm - M)
  let xi := R₀.c                                                    -- xi = center(R0)
  let u := U.c                                                      -- u = center(U)
  let U_ := U.recentre                                              -- U_ = U - u
  let err1 := (List.range (η - 1)).foldl (fun _ m =>                -- for i = 2:order
    Zonotope.mtimes (((Nat.factorial (m + 2) : ℝ)⁻¹) • A ^ (m + 2))
      ((Zonotope.mtimesIntervalMat (mulI 1 1 0 (tmax ^ (m + 1))) R₀).plus
        (Zonotope.ofPoint (-(th ^ (m + 1)) • xi))))               -- err1 = M*(...), no +
    (Zonotope.ofPoint 0)                                            -- err1 = zonotope(zeros)
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
