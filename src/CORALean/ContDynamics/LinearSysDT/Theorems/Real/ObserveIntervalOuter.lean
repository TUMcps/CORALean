module

public import CORALean.ContDynamics.LinearSysDT.Operations.ObserveInterval
public import CORALean.ContSet.Zonotope.Real.Theorems.MtimesExact
public import CORALean.ContSet.Zonotope.Real.Theorems.PlusExact
public import CORALean.ContSet.Interval.Real.Theorems.PlusOuter
public import CORALean.ContSet.Interval.Real.Theorems.MemPoint
public import CORALean.ContSet.Conversion.Real.Operations.Zonotope_to_Interval
public import CORALean.ContSet.Conversion.Real.Theorems.ZonotopeIntervalContains

@[expose] public section

/-!
# The interval observer holds the true state

CORA's `priv_observe_interval` at any fixed gain `L`: every run
`x_{k+1} = A x_k + u_k + w_k`, `w_k ∈ W`, with outputs `y_k = C x_k + v_k`, `v_k ∈ V`, is in the
observer's box at every step, provided the initial error `x_0 - center(R₀)` lies in `R₀`
(CORA seeds `R_x` with `R₀` itself, so this is what its box needs). The error obeys
`e_{k+1} = (A - L C) e_k + (w_k - L v_k)`; unrolled, `e_k = (A - L C)^k e_0` plus the sum of
`(A - L C)^m d_{k-1-m}` with `d_j ∈ D`, and each term lies in the box of `(A - L C)^m D`.

[1, Alg. 1] encloses the true state when `S_{x,0}` holds the initial error `x_0 - x̂_0`;
as printed, `S_{x,0} ← X_0`, it need not (`observeInterval_cora_counterexample`).

## References

* [1] M. Althoff. "Guaranteed State Estimation in CORA 2021". In Proc. of the 8th
      International Workshop on Applied Verification of Continuous and Hybrid Systems (ARCH21),
      EPiC Series in Computing, vol. 80, pp. 161-175, 2021.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   14-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix Pointwise CORALean.Real

variable {n p : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

-- `R_x` after `k` steps is the initial set under `(A - L C)^k`
theorem LinearSysDT.aux_observeIntervalState_Rx (sys : LinearSysDT ℝ n) (L : Mat ℝ n sys.q)
    (R₀ W : Zonotope (Vec ℝ n)) (V : Zonotope (Vec ℝ sys.q)) (u : ℕ → Vec ℝ sys.m)
    (y : ℕ → Vec ℝ sys.q) (k : ℕ) :
    (sys.observeIntervalState L R₀ W V u y k).Rx.construct =
      (((sys.A - L * sys.C) ^ k) *ᵥ ·) '' R₀.construct := by -- --- PROOF ---
  induction k with
  | zero => simp [LinearSysDT.observeIntervalState]
  | succ k ih =>
    -- one more step maps the set through `A - L C`
    show (Zonotope.mtimes (sys.A - L * sys.C)
      (sys.observeIntervalState L R₀ W V u y k).Rx).construct = _
    rw [← Zonotope.mtimes_exact, ih, Set.image_image]
    simp [Matrix.mulVec_mulVec, pow_succ']

-- `D` after `k` steps is the disturbance set under `(A - L C)^k`
theorem LinearSysDT.aux_observeIntervalState_D (sys : LinearSysDT ℝ n) (L : Mat ℝ n sys.q)
    (R₀ W : Zonotope (Vec ℝ n)) (V : Zonotope (Vec ℝ sys.q)) (u : ℕ → Vec ℝ sys.m)
    (y : ℕ → Vec ℝ sys.q) (k : ℕ) :
    (sys.observeIntervalState L R₀ W V u y k).D.construct =
      (((sys.A - L * sys.C) ^ k) *ᵥ ·) ''
        ((Zonotope.mtimes (-L) V).plus W).construct := by -- --- PROOF ---
  induction k with
  | zero => simp [LinearSysDT.observeIntervalState]
  | succ k ih =>
    -- one more step maps the set through `A - L C`
    show (Zonotope.mtimes (sys.A - L * sys.C)
      (sys.observeIntervalState L R₀ W V u y k).D).construct = _
    rw [← Zonotope.mtimes_exact, ih, Set.image_image]
    simp [Matrix.mulVec_mulVec, pow_succ']

-- the boxed disturbance terms hold every sum `∑ (A - L C)^m d_m`
theorem LinearSysDT.aux_observeIntervalState_Rwv (sys : LinearSysDT ℝ n) (L : Mat ℝ n sys.q)
    (R₀ W : Zonotope (Vec ℝ n)) (V : Zonotope (Vec ℝ sys.q)) (u : ℕ → Vec ℝ sys.m)
    (y : ℕ → Vec ℝ sys.q) (d : ℕ → Vec ℝ n)
    (hd : ∀ j, d j ∈ ((Zonotope.mtimes (-L) V).plus W).construct) (k : ℕ) :
    ∑ m ∈ Finset.range k, ((sys.A - L * sys.C) ^ m) *ᵥ d m ∈
      (sys.observeIntervalState L R₀ W V u y k).Rwv.construct := by -- --- PROOF ---
  induction k with
  | zero => simpa [LinearSysDT.observeIntervalState] using Interval.mem_point 0
  | succ k ih =>
    -- the new term is in the box of `D` after `k` steps
    have hk : ((sys.A - L * sys.C) ^ k) *ᵥ d k ∈
        (sys.observeIntervalState L R₀ W V u y k).D.interval.construct := by
      refine Zonotope.interval_contains _ ?_
      rw [LinearSysDT.aux_observeIntervalState_D]
      exact ⟨_, hd k, rfl⟩
    rw [Finset.sum_range_succ]
    exact Interval.plus_outer _ _ ⟨_, ih, _, hk, rfl⟩

-- one step of the error `x - x̂`
theorem LinearSysDT.aux_observeInterval_error (A : Mat ℝ n n) (L : Mat ℝ n p) (C : Mat ℝ p n)
    (x x' xh u w : Vec ℝ n) (v : Vec ℝ p) (hx : x' = A *ᵥ x + u + w) :
    x' - (A *ᵥ xh + u + L *ᵥ ((C *ᵥ x + v) - C *ᵥ xh)) =
      (A - L * C) *ᵥ (x - xh) + (w - L *ᵥ v) := by
  subst hx
  simp only [Matrix.sub_mulVec, ← Matrix.mulVec_mulVec, Matrix.mulVec_sub, Matrix.mulVec_add]
  abel


-- =======================================  MAIN THEOREM  ======================================= --

theorem LinearSysDT.observeInterval_outer (sys : LinearSysDT ℝ n) (L : Mat ℝ n sys.q)
    (R₀ W : Zonotope (Vec ℝ n)) (V : Zonotope (Vec ℝ sys.q)) (u : ℕ → Vec ℝ sys.m)
    (y : ℕ → Vec ℝ sys.q) (x w : ℕ → Vec ℝ n) (v : ℕ → Vec ℝ sys.q)
    (h0 : x 0 - R₀.c ∈ R₀.construct) (hw : ∀ k, w k ∈ W.construct)
    (hv : ∀ k, v k ∈ V.construct) (hstep : ∀ k, x (k + 1) = sys.A *ᵥ x k + sys.B *ᵥ u k + w k)
    (hy : ∀ k, y k = sys.C *ᵥ x k + v k) (k : ℕ) :
    x k ∈ (sys.observeInterval L R₀ W V u y k).construct := by -- --- PROOF ---
  set s := sys.observeIntervalState L R₀ W V u y with hs
  set d : ℕ → Vec ℝ n := fun j => w j - L *ᵥ v j with hdef
  -- the disturbance terms lie in `D`
  have hd : ∀ j, d j ∈ ((Zonotope.mtimes (-L) V).plus W).construct := fun j => by
    rw [← Zonotope.plus_exact, ← Zonotope.mtimes_exact]
    exact ⟨_, ⟨v j, hv j, rfl⟩, w j, hw j, by simp [hdef, Matrix.neg_mulVec, sub_eq_neg_add]⟩
  -- the error recursion
  have herr : ∀ j, x (j + 1) - (s (j + 1)).x =
      (sys.A - L * sys.C) *ᵥ (x j - (s j).x) + d j := fun j => by
    have := aux_observeInterval_error sys.A L sys.C (x j) (x (j + 1)) (s j).x (sys.B *ᵥ u j)
      (w j) (v j) (hstep j)
    rw [← hy j] at this
    exact this
  -- its closed form
  have hclosed : ∀ j, x j - (s j).x = ((sys.A - L * sys.C) ^ j) *ᵥ (x 0 - (s 0).x) +
      ∑ m ∈ Finset.range j, ((sys.A - L * sys.C) ^ m) *ᵥ d (j - 1 - m) := fun j => by
    induction j with
    | zero => simp
    | succ j ih =>
      rw [herr, ih, Matrix.mulVec_add, Matrix.mulVec_mulVec, ← pow_succ',
        Finset.sum_range_succ' _ j, Matrix.mulVec_sum]
      simp only [Matrix.mulVec_mulVec, ← pow_succ', pow_zero, Matrix.one_mulVec]
      -- the indices agree after reversing
      have : ∀ m ∈ Finset.range j, d (j - 1 - m) = d (j + 1 - 1 - (m + 1)) := fun m _ => by
        congr 1
        omega
      rw [Finset.sum_congr rfl fun m hm => by rw [this m hm]]
      abel
  -- the three parts of `x k = x̂ + (a + b)`
  have ha : ((sys.A - L * sys.C) ^ k) *ᵥ (x 0 - (s 0).x) ∈ (s k).Rx.construct := by
    rw [LinearSysDT.aux_observeIntervalState_Rx]
    exact ⟨_, h0, rfl⟩
  have hb := LinearSysDT.aux_observeIntervalState_Rwv sys L R₀ W V u y
    (fun m => d (k - 1 - m)) (fun m => hd _) k
  have hxk : x k = (s k).x + (((sys.A - L * sys.C) ^ k) *ᵥ (x 0 - (s 0).x) +
      ∑ m ∈ Finset.range k, ((sys.A - L * sys.C) ^ m) *ᵥ d (k - 1 - m)) := by
    rw [← hclosed]
    abel
  rw [hxk]
  exact Interval.plus_outer _ _ ⟨_, Interval.mem_point _, _,
    Interval.plus_outer _ _ ⟨_, Zonotope.interval_contains _ ha, _, hb, rfl⟩, rfl⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
