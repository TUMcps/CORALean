module

public import CORALean.ContDynamics.LinearSys.Operations.ReachBox
public import CORALean.ContDynamics.LinearSys.Theorems.ListFoldlRangeStepOut
public import CORALean.ContDynamics.LinearSys.Theorems.ExpAddSmul
public import CORALean.ContDynamics.LinearSys.Theorems.ReachSetExactEq
public import CORALean.ContDynamics.LinearSys.Theorems.InputReachSeparationEq
public import CORALean.ContDynamics.LinearSys.Theorems.InputReachMono
public import CORALean.ContDynamics.LinearSys.Theorems.InputReachSubsetInputSolution
public import CORALean.ContDynamics.LinearSys.Theorems.ReachStepkWrappingFreeOuter
public import CORALean.ContSet.Zonotope.Real.Theorems.MtimesExact
public import CORALean.ContSet.Zonotope.Real.Theorems.PlusExact
public import CORALean.ContSet.ContSet.Theorems.Basic
public import CORALean.ContSet.Conversion.Real.Operations.Interval_to_Zonotope
public import CORALean.ContSet.Conversion.Real.Operations.Zonotope_to_Interval
public import CORALean.ContSet.Conversion.Real.Theorems.IntervalZonotopeContains
public import CORALean.ContSet.Conversion.Real.Theorems.ZonotopeIntervalContains

@[expose] public section

/-!
# [1, Alg. 2] encloses the reachable set on every time interval

`reachBox`'s `R_k ⊇ R(t)` for every `t ∈ [kr, (k+1)r]` and `k ≤ N`, from a zonotope `X⁰` and an
input zonotope `U ∋ 0`, at a Taylor order admissible for `r` and `A`: the claim of [1, Alg. 2] that
it computes `R([0, t_f])` window by window. `R(t)` is `reachSetExact` on `[0, t]`. Three invariants,
by induction on `k`, at every `τ ∈ [0, r]`: `e^{A(kr+τ)}X⁰ ⊆ H^R_k`, `e^{Akr} inputReach U τ ⊆ V_k`
and `inputReach U (kr+τ) ⊆ P^R_k`. The first holds at `k = 0` by `reachStepkWrappingFree_outer`, the
second by [1, Thm. 3.1] (`inputReach_subset_inputSolution`) once `inputReach U τ ⊆ inputReach U r`,
which `0 ∈ U` gives ([1, Prop. 3.3], `inputReach_mono`); the third is the superposition
(`inputReach_separation_eq`), the first summand inside `box(V_{k+1})`.

## Inputs
* `sys` – linear system
* `X₀` – initial zonotope
* `U` – input zonotope
* `r` – step length
* `m` – Taylor order offset
* `N` – number of steps
* `k` – window index
* `t` – time

## Hypotheses
* `hr` – step length positive
* `hε` – scaled norm small enough for the Taylor order
* `h0` – origin lies in the input zonotope
* `hk` – window index within the step count
* `ht` – time within the window

## Conclusion
* the window encloses the reachable set at the time

## References

* [1] M. Althoff. "Reachability Analysis and its Application to the Safety
      Assessment of Autonomous Cars". PhD thesis, TU München, 2010.
-/

-- Authors:       Claude Opus 5.5
-- Written:       08-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real
open Matrix ContSet Scalar NormedSpace Pointwise

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Alg. 2]: `R_k` encloses the reachable set at every `t ∈ [kr, (k+1)r]`, `k ≤ N`. -/
theorem LinearSys.reachBox_outer (sys : LinearSys 𝕋 n) (X₀ U : Zonotope (Vec ℝ n)) {r : ℝ}
    (hr : 0 < r) {m : ℕ} (hε : ‖r • toRealMat sys.A‖ / (((m + 2 : ℕ) : ℝ) + 2) < 1)
    (h0 : (0 : Vec ℝ n) ∈ U.construct)
    {N k : ℕ} (hk : k ≤ N) {t : ℝ} (ht : t ∈ Set.Icc ((k : ℝ) * r) ((k + 1) * r)) : -- --- CONCL ---
    ∃ R, (sys.reachBox X₀ U r (m + 2) N)[k]? = some R
      ∧ sys.reachSetExact (S := 𝒵) (Set.Icc 0 t) X₀ U t ⊆ R.construct := by -- --- PROOF ---
  set A := toRealMat sys.A
  set E := exp (r • A)
  set H₀ := sys.timeIntervalStep (S := 𝒵) r (m + 2) X₀
  set V₀ := sys.inputSolution (S := 𝒵) r (m + 2) U
  set step : Zonotope (Vec ℝ n) × Zonotope (Vec ℝ n) × Zonotope (Vec ℝ n)
      → Zonotope (Vec ℝ n) × Zonotope (Vec ℝ n) × Zonotope (Vec ℝ n) :=
    fun s => (s.1.mtimes E, s.2.1.mtimes E, s.2.2.plus (s.2.1.mtimes E).interval.zonotope)
  set out : Zonotope (Vec ℝ n) × Zonotope (Vec ℝ n) × Zonotope (Vec ℝ n)
      → Zonotope (Vec ℝ n) := fun s => s.1.plus s.2.2
  set s₀ := (H₀, V₀, V₀.interval.zonotope)
  have hlist : sys.reachBox X₀ U r (m + 2) N
      = (List.range (N + 1)).map fun j => out (step^[j] s₀) :=
    congrArg Prod.snd (foldl_range_step_out step out s₀ N)
  have hU : Bornology.IsBounded (construct (S := Zonotope (Vec ℝ n)) U) :=
    CompactSet.isBounded_construct U
  have hkr : ∀ k : ℕ, (0:ℝ) ≤ k * r := fun k => mul_nonneg (Nat.cast_nonneg k) hr.le
  -- the listing's first two sets: `H^R_0` and `V₀` enclose the first interval
  have hh : ∀ τ ∈ Set.Icc (0:ℝ) r, (fun x => exp (τ • A) *ᵥ x) '' X₀.construct ⊆ H₀.construct := by
    intro τ hτ
    have h := sys.reachStepkWrappingFree_outer (S := 𝒵) hr hε X₀ (k := 0) (t := τ)
      (by simpa using hτ.1) (by simpa using hτ.2)
    refine h.trans ?_
    show (Zonotope.mtimes (exp ((((0 : ℕ) : ℝ) * r) • A)) H₀).construct ⊆ H₀.construct
    rw [← Zonotope.mtimes_exact]
    simp
  have hi : ∀ τ ∈ Set.Icc (0:ℝ) r, sys.inputReach (S := 𝒵) U τ ⊆ V₀.construct := fun τ hτ =>
    (sys.inputReach_mono hU h0 hτ.1 hτ.2).trans
      (sys.inputReach_subset_inputSolution (S := 𝒵) hr (m + 2) (by exact_mod_cast hε)
        (ConvexSet.convex_construct U) (CompactSet.isClosed_construct U) hU
        (ConvexSet.convex_construct _) (CompactSet.isClosed_construct _)
        (CompactSet.isBounded_construct _))
  -- the three invariants
  have hinv : ∀ k : ℕ, ∀ τ ∈ Set.Icc (0:ℝ) r,
      (fun x => exp ((k * r + τ) • A) *ᵥ x) '' X₀.construct ⊆ (step^[k] s₀).1.construct
      ∧ (fun y => exp ((k * r) • A) *ᵥ y) '' sys.inputReach (S := 𝒵) U τ
          ⊆ (step^[k] s₀).2.1.construct
      ∧ sys.inputReach (S := 𝒵) U (k * r + τ) ⊆ (step^[k] s₀).2.2.construct := by
    intro k
    induction k with
    | zero =>
      intro τ hτ
      simp only [Nat.cast_zero, zero_mul, zero_add, zero_smul, exp_zero, Matrix.one_mulVec,
        Set.image_id', Function.iterate_zero, id]
      exact ⟨hh τ hτ, hi τ hτ,
        (hi τ hτ).trans ((Zonotope.interval_contains _).trans (Interval.zonotope_contains _))⟩
    | succ k ih =>
      intro τ hτ
      have hτ0 := hτ.1
      rw [Function.iterate_succ_apply']
      -- `e^{A(k+1)r} = e^{Ar} e^{Akr}`, with and without `τ`
      have hEk : exp ((((k + 1 : ℕ) : ℝ) * r) • A) = E * exp ((k * r) • A) := by
        rw [show ((k + 1 : ℕ) : ℝ) * r = r + k * r by push_cast; ring, exp_add_smul_eq_mul]
      have hEkτ : exp ((((k + 1 : ℕ) : ℝ) * r + τ) • A) = E * exp ((k * r + τ) • A) := by
        rw [show ((k + 1 : ℕ) : ℝ) * r + τ = r + (k * r + τ) by push_cast; ring,
          exp_add_smul_eq_mul]
      -- `V_{k+1}`: one more `e^{Ar}`
      have h2 : (fun y => exp ((((k + 1 : ℕ) : ℝ) * r) • A) *ᵥ y) '' sys.inputReach (S := 𝒵) U τ
          ⊆ (step (step^[k] s₀)).2.1.construct := by
        rintro _ ⟨v, hv, rfl⟩
        show _ ∈ ((step^[k] s₀).2.1.mtimes E).construct
        rw [← Zonotope.mtimes_exact]
        refine ⟨_, (ih τ hτ).2.1 ⟨v, hv, rfl⟩, ?_⟩
        simp only [hEk, Matrix.mulVec_mulVec]
      refine ⟨?_, h2, ?_⟩
      -- `H^R_{k+1}`: one more `e^{Ar}`
      · rintro _ ⟨x, hx, rfl⟩
        show _ ∈ ((step^[k] s₀).1.mtimes E).construct
        rw [← Zonotope.mtimes_exact]
        refine ⟨_, (ih τ hτ).1 ⟨x, hx, rfl⟩, ?_⟩
        simp only [hEkτ, Matrix.mulVec_mulVec]
      -- `P^R_{k+1}`: what `[0, τ]` contributes, propagated, plus `[0, (k+1)r]`
      · have hsep := sys.inputReach_separation_eq (S := 𝒵) hτ0 (hkr (k + 1)) hU
        rw [show (((k + 1 : ℕ) : ℝ) * r + τ) = τ + ((k + 1 : ℕ) : ℝ) * r by ring, hsep]
        rintro _ ⟨_, hw, v, hv, rfl⟩
        show _ ∈ ((step^[k] s₀).2.2.plus
          ((step^[k] s₀).2.1.mtimes E).interval.zonotope).construct
        rw [← Zonotope.plus_exact]
        refine ⟨v, ?_, _, (Zonotope.interval_contains _).trans (Interval.zonotope_contains _)
          (h2 hw), add_comm _ _⟩
        have hr' : r ∈ Set.Icc (0:ℝ) r := ⟨hr.le, le_rfl⟩
        have := (ih r hr').2.2
        rw [show ((k : ℝ) * r + r) = ((k + 1 : ℕ) : ℝ) * r by push_cast; ring] at this
        exact this hv
  -- the window `t ∈ [kr, (k+1)r]` is `τ = t - kr ∈ [0, r]`
  have hτ : t - k * r ∈ Set.Icc (0:ℝ) r := ⟨by linarith [ht.1], by linarith [ht.2]⟩
  refine ⟨out (step^[k] s₀), ?_, ?_⟩
  · rw [hlist, List.getElem?_map, List.getElem?_range (by omega)]
    rfl
  · have ht0 : 0 ≤ t := (hkr k).trans ht.1
    rw [sys.reachSetExact_eq (S := 𝒵) X₀ U ht0 hU]
    rintro _ ⟨_, ⟨x, hx, rfl⟩, v, hv, rfl⟩
    have hI := hinv k (t - k * r) hτ
    rw [show (k : ℝ) * r + (t - k * r) = t by ring] at hI
    show _ ∈ ((step^[k] s₀).1.plus (step^[k] s₀).2.2).construct
    rw [← Zonotope.plus_exact]
    exact ⟨_, hI.1 ⟨x, hx, rfl⟩, v, hI.2.2 hv, rfl⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
