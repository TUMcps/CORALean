module

public import CORALean.ContDynamics.LinearSysDT.Operations.ObservePropagation
public import CORALean.ContSet.Zonotope.Real.Theorems.MtimesExact
public import CORALean.ContSet.Zonotope.Real.Theorems.PlusExact
public import CORALean.ContSet.Zonotope.Real.Theorems.OfPointMem
public import CORALean.ContSet.Zonotope.Real.Theorems.ReduceOuter

@[expose] public section

/-!
# The set-propagation observer holds the true state

[1, Eq. 6] at any gains: every run `x_{k+1} = A x_k + u_k + w_k`, `w_k ∈ W`, with outputs
`y_k = C x_k + v_k`, `v_k ∈ V`, is in the observer's set at every step, provided `x_0 ∈ S_0`:
`x_{k+1} = (A - L C) x_k + u_k + L y_k + (-L) v_k + w_k` is a point of each summand. [1] asks
`x̂_0 ∈ S_0`, `0 ∈ V`, `0 ∈ W`; the induction uses only `x_0 ∈ S_0`. [2, Prop. 1] is this
induction for time-varying `A_k`, …, `F_k`, a feedthrough `D_k u`, a gain sequence and `↓_{q,W}`
before the product; here the matrices are constant, `D = 0`, the gain a function of the current
set and the reduction after the step. At `Zonotope.luenbergerGain` the sets are those of
[2, Sec. 5], Combastel's zonotopic Kalman filter, without its covariation recursion.

## Inputs
* `sys` – system
* `gain` – gain function
* `order` – zonotope order
* `W` – disturbance zonotope
* `R₀` – initial zonotope
* `V` – noise zonotope
* `u` – inputs
* `y` – measurements
* `x` – true states
* `w` – true disturbances
* `v` – true noise
* `k` – step

## Hypotheses
* `h0` – start lies in `R₀`
* `hw` – disturbances lie in `W`
* `hv` – noise lies in `V`
* `hstep` – the dynamics hold
* `hy` – the measurements follow the outputs

## Conclusion
* the true state lies in the observer's set

## References

* [1] M. Althoff. "Guaranteed State Estimation in CORA 2021". In Proc. of the 8th
      International Workshop on Applied Verification of Continuous and Hybrid Systems (ARCH21),
      EPiC Series in Computing, vol. 80, pp. 161-175, 2021.
* [2] C. Combastel. "Zonotopes and Kalman observers: Gain optimality under distinct uncertainty
      paradigms and robust convergence". Automatica, 55:265-273, 2015.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   14-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix Pointwise CORALean.Real

variable {n p : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem LinearSysDT.observePropagation_outer (sys : LinearSysDT ℝ n)
    (gain : Zonotope (Vec ℝ n) → Mat ℝ n sys.q) (order : ℕ) (W R₀ : Zonotope (Vec ℝ n))
    (V : Zonotope (Vec ℝ sys.q)) (u : ℕ → Vec ℝ sys.m) (y : ℕ → Vec ℝ sys.q) (x w : ℕ → Vec ℝ n)
    (v : ℕ → Vec ℝ sys.q) (h0 : x 0 ∈ R₀.construct) (hw : ∀ k, w k ∈ W.construct)
    (hv : ∀ k, v k ∈ V.construct) (hstep : ∀ k, x (k + 1) = sys.A *ᵥ x k + sys.B *ᵥ u k + w k)
    (hy : ∀ k, y k = sys.C *ᵥ x k + v k) (k : ℕ) : -- --- CONCL ---
    x k ∈ (sys.observePropagation gain order W R₀ V u y k).construct := by -- --- PROOF ---
  induction k with
  | zero => exact h0
  | succ k ih =>
    set S := sys.observePropagation gain order W R₀ V u y k
    set L := gain S
    -- the true state, one point of each summand of (6)
    have heq : x (k + 1) =
        (sys.A - L * sys.C) *ᵥ x k + sys.B *ᵥ u k + L *ᵥ y k + (-L) *ᵥ v k + w k := by
      rw [hstep, hy, Matrix.sub_mulVec, ← Matrix.mulVec_mulVec, Matrix.mulVec_add,
        Matrix.neg_mulVec]
      abel
    have h1 : (sys.A - L * sys.C) *ᵥ x k ∈ (Zonotope.mtimes (sys.A - L * sys.C) S).construct := by
      rw [← Zonotope.mtimes_exact]; exact ⟨x k, ih, rfl⟩
    have h4 : (-L) *ᵥ v k ∈ (Zonotope.mtimes (-L) V).construct := by
      rw [← Zonotope.mtimes_exact]; exact ⟨v k, hv k, rfl⟩
    show x (k + 1) ∈ (Zonotope.reduce (((((Zonotope.mtimes (sys.A - L * sys.C) S).plus
      (Zonotope.ofPoint (sys.B *ᵥ u k))).plus (Zonotope.ofPoint (L *ᵥ y k))).plus
      (Zonotope.mtimes (-L) V)).plus W) order).construct
    refine Zonotope.reduce_outer _ _ ?_
    rw [heq, ← Zonotope.plus_exact, ← Zonotope.plus_exact, ← Zonotope.plus_exact,
      ← Zonotope.plus_exact]
    exact Set.add_mem_add (Set.add_mem_add (Set.add_mem_add (Set.add_mem_add h1
      (Zonotope.mem_ofPoint _)) (Zonotope.mem_ofPoint _)) h4) (hw k)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
