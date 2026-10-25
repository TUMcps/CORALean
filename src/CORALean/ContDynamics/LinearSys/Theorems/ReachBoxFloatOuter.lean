module

public import CORALean.ContDynamics.LinearSys.Operations.ReachBoxFloat
public import CORALean.ContDynamics.LinearSys.Theorems.ListFoldlRangeStepOut
public import CORALean.ContDynamics.LinearSys.Theorems.ExpAddSmul
public import CORALean.ContDynamics.LinearSys.Theorems.ExpMemExpIntervalFloat
public import CORALean.ContDynamics.LinearSys.Theorems.InputReachMono
public import CORALean.ContDynamics.LinearSys.Theorems.InputReachSeparationEq
public import CORALean.ContDynamics.LinearSys.Theorems.InputReachSubsetInputSolutionFloat
public import CORALean.ContDynamics.LinearSys.Theorems.ReachSetExactEq
public import CORALean.ContDynamics.LinearSys.Theorems.ReachOrderFloatSpec
public import CORALean.ContDynamics.LinearSys.Theorems.TimeIntervalFloatOuter
public import CORALean.ContSet.Conversion.Float.Operations.Interval_to_Zonotope
public import CORALean.ContSet.Conversion.Float.Operations.Zonotope_to_Interval
public import CORALean.ContSet.Conversion.Real.Operations.Interval_to_Zonotope
public import CORALean.ContSet.Conversion.Real.Operations.Zonotope_to_Interval
public import CORALean.ContSet.Conversion.Float.Theorems.IntervalZonotopeContains
public import CORALean.ContSet.Conversion.Float.Theorems.ZonotopeIntervalContains
public import CORALean.ContSet.Conversion.Real.Theorems.IntervalZonotopeContains
public import CORALean.ContSet.Conversion.Real.Theorems.ZonotopeIntervalContains

@[expose] public section

/-!
# `reachBoxFloat` encloses the reachable set on every time interval

`reachBox_outer` in floats: `R_k ⊇ R(t)` for every `t ∈ [kr, (k+1)r]` and `k ≤ N`, from a zonotope
`X⁰` and an input zonotope `U ∋ 0`. The three invariants of the exact proof,
`e^{A(kr+τ)}X⁰ ⊆ H^R_k`, `e^{Akr} inputReach U τ ⊆ V_k` and `inputReach U (kr+τ) ⊆ P^R_k`, hold by
the same induction, with `e^{Ar}` in the float interval matrix `[e^{Ar}]`
(`exp_mem_expIntervalFloat`, `Mtimes.mtimes_outer`) and each sum and box an enclosure
(`Plus.plus_outer`, `Zonotope.interval_contains`, `Interval.zonotope_contains`). The base case is
`timeIntervalFloat_outer` and `inputReach_subset_inputSolutionFloat`, once
`inputReach U τ ⊆ inputReach U r`. The enclosure is of the exact `reachSetExact`.

## Inputs
* `sys` – linear system
* `X₀` – initial float zonotope
* `U` – input float zonotope
* `r` – float step length
* `η` – Taylor order
* `N` – number of steps
* `k` – window index
* `t` – time

## Hypotheses
* `hr` – step length positive
* `h0` – origin lies in the input zonotope
* `hk` – window index within the step count
* `ht` – time within the window

## Conclusion
* the float window encloses the reachable set at the time

## References

* [1] M. Althoff and B. H. Krogh. "Zonotope Bundles for the Efficient Computation of Reachable
      Sets". 2011 50th IEEE Conference on Decision and Control and European Control Conference
      (CDC-ECC 2011), 2011.
-/

-- Authors:       Claude Opus 5.5
-- Written:       10-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float FloatOps SoundFloatArithmetic NormedSpace Matrix Pointwise

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Alg. 1] in floats: `R_k` encloses the reachable set at every `t ∈ [kr, (k+1)r]`,
`k ≤ N`. -/
theorem LinearSys.reachBoxFloat_outer (sys : LinearSys 𝕋 n) (X₀ U : Zonotope (Vec 𝕋 n)) {r : 𝕋}
    {η N : ℕ} (hr : 0 < toReal r) (h0 : (0 : Vec ℝ n) ∈ U.construct) {k : ℕ} (hk : k ≤ N) {t : ℝ}
    (ht : t ∈ Set.Icc ((k : ℝ) * toReal r) ((k + 1) * toReal r)) : -- --- CONCL ---
    ∀ Rs ∈ sys.reachBoxFloat X₀ U r η N,
      ∃ R, Rs[k]? = some R ∧
        sys.reachSetExact (S := 𝒵[𝕋]) (Set.Icc 0 t) X₀ U t
          ⊆ R.construct := by -- --- PROOF ---
  intro Rs (h : sys.reachBoxFloat X₀ U r η N = some Rs)
  -- the order is the search's, and the list is the loop's
  simp only [LinearSys.reachBoxFloat, Option.bind_eq_bind, Option.bind_eq_some_iff,
    Option.pure_def, Option.some.injEq] at h
  obtain ⟨η', hη', rfl⟩ := h
  have hadm := (LinearSys.reachOrderFloat_spec _ hη').1
  -- the loop's pieces, named
  set A := Scalar.toRealMat sys.A
  set ρ := toReal r with hρ
  set E := exp (ρ • A)
  set eAr := sys.expIntervalFloat r r η'
  set H₀ := sys.timeIntervalFloat r η' X₀
  set V₀ := sys.inputSolutionFloat r η' U
  set step : Zonotope (Vec 𝕋 n) × Zonotope (Vec 𝕋 n) × Zonotope (Vec 𝕋 n)
      → Zonotope (Vec 𝕋 n) × Zonotope (Vec 𝕋 n) × Zonotope (Vec 𝕋 n) :=
    fun s => (Mtimes.mtimes (𝕄 := ℐ[𝕋])
      (S := 𝒵[𝕋]) eAr s.1,
      Mtimes.mtimes (𝕄 := ℐ[𝕋])
        (S := 𝒵[𝕋]) eAr s.2.1,
      s.2.2 ⊞ (Mtimes.mtimes (𝕄 := ℐ[𝕋])
        (S := 𝒵[𝕋]) eAr s.2.1).interval.zonotope)
  -- the loop's output and its closed form
  set out : Zonotope (Vec 𝕋 n) × Zonotope (Vec 𝕋 n) × Zonotope (Vec 𝕋 n) → Zonotope (Vec 𝕋 n) :=
    fun s => s.1 ⊞ s.2.2
  set s₀ := (H₀, V₀, V₀.interval.zonotope)
  have hlist : (List.range N).foldl
      (fun (s : (Zonotope (Vec 𝕋 n) × Zonotope (Vec 𝕋 n) × Zonotope (Vec 𝕋 n)) × List
        (Zonotope (Vec 𝕋 n))) _ =>
        ((step s.1), s.2 ++ [out (step s.1)])) ((s₀), [out s₀])
      = (step^[N] s₀, (List.range (N + 1)).map fun j => out (step^[j] s₀)) :=
    foldl_range_step_out step out s₀ N
  -- what the listing needs of the sets: bounded, a step is enclosed, a box encloses
  have hU : Bornology.IsBounded (ContSet.construct U) := CompactSet.isBounded_construct U
  have hkr : ∀ k : ℕ, (0:ℝ) ≤ k * ρ := fun k => mul_nonneg (Nat.cast_nonneg k) hr.le
  -- `e^{Ar}` is in `[e^{Ar}]`, so one more step is enclosed
  have hE : E ∈ eAr.construct := sys.exp_mem_expIntervalFloat hadm le_rfl le_rfl
  have hstep : ∀ (Z : Zonotope (Vec 𝕋 n)) (y : Vec ℝ n), y ∈ Z.construct →
      E *ᵥ y ∈ (Mtimes.mtimes (𝕄 := ℐ[𝕋])
        (S := 𝒵[𝕋]) eAr Z).construct :=
    fun Z y hy => Mtimes.mtimes_outer (𝕄 := ℐ[𝕋])
      (S := 𝒵[𝕋]) eAr Z
      (Set.mem_biUnion hE (Set.mem_image_of_mem _ hy))
  have hbox : ∀ Z : Zonotope (Vec 𝕋 n), Z.construct ⊆ Z.interval.zonotope.construct :=
    fun Z => (Zonotope.interval_contains Z).trans (Interval.zonotope_contains _)
  -- the first window's `H^R_0` holds the flow of `X⁰` at every `τ ∈ [0, r]`
  have hh : ∀ τ ∈ Set.Icc (0:ℝ) ρ, (fun x => exp (τ • A) *ᵥ x) '' X₀.construct
      ⊆ H₀.construct := by
    rintro τ hτ _ ⟨x, hx, rfl⟩
    exact sys.timeIntervalFloat_outer hr hadm X₀ hx hτ.1 hτ.2
  -- and `V₀` the input's reach, once `inputReach U τ ⊆ inputReach U r`
  have hi : ∀ τ ∈ Set.Icc (0:ℝ) ρ, sys.inputReach (S := 𝒵[𝕋]) U τ ⊆
    V₀.construct :=
    fun τ hτ => (sys.inputReach_mono hU h0 hτ.1 hτ.2).trans
      (sys.inputReach_subset_inputSolutionFloat hr hadm U)
  -- the three invariants, by induction on `k`
  have hinv : ∀ k : ℕ, ∀ τ ∈ Set.Icc (0:ℝ) ρ,
      (fun x => exp ((k * ρ + τ) • A) *ᵥ x) '' X₀.construct ⊆ (step^[k] s₀).1.construct
      ∧ (fun y => exp ((k * ρ) • A) *ᵥ y) '' sys.inputReach (S := 𝒵[𝕋]) U τ
          ⊆ (step^[k] s₀).2.1.construct
      ∧ sys.inputReach (S := 𝒵[𝕋]) U (k * ρ + τ) ⊆
        (step^[k] s₀).2.2.construct := by
    intro k
    -- at `k = 0` the three are the first window's, `box(V₀)` holding `V₀`
    induction k with
    | zero =>
      intro τ hτ
      simp only [Nat.cast_zero, zero_mul, zero_add, zero_smul, exp_zero, Matrix.one_mulVec,
        Set.image_id', Function.iterate_zero, id]
      exact ⟨hh τ hτ, hi τ hτ, (hi τ hτ).trans (hbox _)⟩
    | succ k ih =>
      intro τ hτ
      have hτ0 := hτ.1
      rw [Function.iterate_succ_apply']
      have hEk : exp ((((k + 1 : ℕ) : ℝ) * ρ) • A) = E * exp ((k * ρ) • A) := by
        rw [show ((k + 1 : ℕ) : ℝ) * ρ = ρ + k * ρ by push_cast; ring, exp_add_smul_eq_mul]
      have hEkτ : exp ((((k + 1 : ℕ) : ℝ) * ρ + τ) • A) = E * exp ((k * ρ + τ) • A) := by
        rw [show ((k + 1 : ℕ) : ℝ) * ρ + τ = ρ + (k * ρ + τ) by push_cast; ring,
          exp_add_smul_eq_mul]
      -- `V_{k+1}`: one more `e^{Ar}`
      have h2 : (fun y => exp ((((k + 1 : ℕ) : ℝ) * ρ) • A) *ᵥ y) ''
          sys.inputReach (S := 𝒵[𝕋]) U τ ⊆
            (step (step^[k] s₀)).2.1.construct := by
        rintro _ ⟨v, hv, rfl⟩
        have := hstep _ _ ((ih τ hτ).2.1 ⟨v, hv, rfl⟩)
        simpa only [hEk, Matrix.mulVec_mulVec] using this
      refine ⟨?_, h2, ?_⟩
      -- `H^R_{k+1}`: one more `e^{Ar}`
      · rintro _ ⟨x, hx, rfl⟩
        have := hstep _ _ ((ih τ hτ).1 ⟨x, hx, rfl⟩)
        simpa only [hEkτ, Matrix.mulVec_mulVec] using this
      -- `P^R_{k+1}`: what `[0, τ]` contributes, propagated, plus `[0, (k+1)r]`
      · have hsep := sys.inputReach_separation_eq (S := 𝒵[𝕋]) hτ0
          (hkr (k + 1)) hU
        rw [show (((k + 1 : ℕ) : ℝ) * ρ + τ) = τ + ((k + 1 : ℕ) : ℝ) * ρ by ring, hsep]
        rintro _ ⟨w, hw, v, hv, rfl⟩
        have hr' : ρ ∈ Set.Icc (0:ℝ) ρ := ⟨hr.le, le_rfl⟩
        have hv' := (ih ρ hr').2.2
        rw [show ((k : ℝ) * ρ + ρ) = ((k + 1 : ℕ) : ℝ) * ρ by push_cast; ring] at hv'
        show w + v ∈ _
        rw [add_comm]
        exact Plus.plus_outer (step^[k] s₀).2.2 _ (Set.add_mem_add (hv' hv) (hbox _ (h2 hw)))
  -- the window `t ∈ [kr, (k+1)r]` is `τ = t - kr ∈ [0, r]`
  have hτ : t - k * ρ ∈ Set.Icc (0:ℝ) ρ := ⟨by linarith [ht.1], by linarith [ht.2]⟩
  refine ⟨out (step^[k] s₀), ?_, ?_⟩
  · rw [hlist]
    dsimp only
    rw [ List.getElem?_map, List.getElem?_range (by omega)]
    rfl
  · have ht0 : 0 ≤ t := (hkr k).trans ht.1
    rw [sys.reachSetExact_eq (S := 𝒵[𝕋]) X₀ U ht0 hU]
    rintro _ ⟨_, ⟨x, hx, rfl⟩, v, hv, rfl⟩
    have hI := hinv k (t - k * ρ) hτ
    rw [show (k : ℝ) * ρ + (t - k * ρ) = t by ring] at hI
    exact Plus.plus_outer (step^[k] s₀).1 (step^[k] s₀).2.2
      (Set.add_mem_add (hI.1 ⟨x, hx, rfl⟩) (hI.2.2 hv))

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
