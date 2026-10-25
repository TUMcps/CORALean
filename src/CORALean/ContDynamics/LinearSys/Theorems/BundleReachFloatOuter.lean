module

public import CORALean.ContDynamics.LinearSys.Operations.BundleReachFloat
public import CORALean.ContDynamics.LinearSys.Theorems.ListFoldlRangeStepOut
public import CORALean.ContDynamics.LinearSys.Theorems.ExpAddSmul
public import CORALean.ContDynamics.LinearSys.Theorems.InputReachSeparationEq
public import CORALean.ContDynamics.LinearSys.Theorems.ReachSetExactEq
public import CORALean.ContDynamics.LinearSys.Theorems.ExpMemExpIntervalFloat
public import CORALean.ContSet.Conversion.Float.Operations.Interval_to_Zonotope
public import CORALean.ContSet.Conversion.Float.Operations.Zonotope_to_Interval
public import CORALean.ContSet.Conversion.Float.Operations.Basic
public import CORALean.ContSet.Conversion.Real.Operations.Interval_to_Zonotope
public import CORALean.ContSet.Conversion.Real.Operations.Zonotope_to_Interval
public import CORALean.ContSet.Conversion.Float.Theorems.IntervalZonotopeContains
public import CORALean.ContSet.Conversion.Float.Theorems.ZonotopeIntervalContains
public import CORALean.ContSet.Conversion.Float.Theorems.ZonotopeZonoBundleExact
public import CORALean.ContSet.Conversion.Real.Theorems.IntervalZonotopeContains
public import CORALean.ContSet.Conversion.Real.Theorems.ZonotopeIntervalContains

@[expose] public section

/-!
# [1, Alg. 1] in floats encloses the reachable set on every time interval

`bundleReach_outer`'s argument with `[e^{Ar}]` for `e^{Ar}`: the float list has the same shape, so
the same three invariants go through by induction on `k`, at every `τ ∈ [0, r]`, each product
`e^{Ar} v` landing in the product of the enclosure with the set `v` is in, and each sum in the float
sum. The claim is `⊇`, an outer approximation, and nothing is claimed of the tightness. `r` is a
float, the order `η` must be admissible for it (`IsOrderAdmissibleFloat r r η`, the condition
`expIntervalFloat` is sound under), and `Rh₀`, `Ri₀` are float sets held to enclose the listing's
first two inputs.

## Inputs
* `sys` – linear system
* `X₀` – initial set
* `U` – input set
* `Rh₀` – initial float homogeneous bundle
* `Ri₀` – initial float input zonotope
* `r` – float step length
* `η` – Taylor order
* `N` – number of steps
* `k` – window index
* `t` – time

## Hypotheses
* `hr` – step length nonnegative
* `hη` – order admissible
* `hU` – input set bounded
* `hh` – bundle holds the homogeneous flow
* `hi` – zonotope holds the input reach
* `hk` – window index within the step count
* `ht` – time within the window

## Conclusion
* the float window encloses the reachable set at the time

## References

* [1] M. Althoff and B. H. Krogh. "Zonotope Bundles for the Efficient Computation of
      Reachable Sets". In Proc. of the 50th IEEE Conference on Decision and Control and
      European Control Conference (CDC-ECC), pp. 6814-6821, 2011.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       08-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float SoundFloatArithmetic
open Matrix ContSet NormedSpace Pointwise

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Alg. 1] in floats: `R_k` encloses the reachable set at every `t ∈ [t_k, t_{k+1}]`,
`k ≤ N`. -/
theorem LinearSys.bundleReachFloat_outer (sys : LinearSys 𝕋 n) (X₀ U : S n)
    (Rh₀ : ZonoBundle (Vec 𝕋 n)) (Ri₀ : Zonotope (Vec 𝕋 n)) {r : 𝕋} (hr : 0 ≤ toReal r) {η : ℕ}
    (hη : sys.IsOrderAdmissibleFloat r r η)
    (hU : Bornology.IsBounded (construct U))
    (hh : ∀ τ ∈ Set.Icc (0:ℝ) (toReal r),
      (fun x => exp (τ • Scalar.toRealMat sys.A) *ᵥ x) '' construct X₀ ⊆ Rh₀.construct)
    (hi : ∀ τ ∈ Set.Icc (0:ℝ) (toReal r), sys.inputReach U τ ⊆ Ri₀.construct)
    {N k : ℕ} (hk : k ≤ N) {t : ℝ}
    (ht : t ∈ Set.Icc ((k : ℝ) * toReal r) ((k + 1) * toReal r)) : -- --- CONCL ---
    ∃ R, (sys.bundleReachFloat Rh₀ Ri₀ r η N)[k]? = some R
      ∧ sys.reachSetExact (Set.Icc 0 t) X₀ U t ⊆ R.construct := by -- --- PROOF ---
  -- the matrix, the step and the enclosure `[e^{Ar}]` the loop multiplies by
  set A := Scalar.toRealMat sys.A
  set r' := toReal r
  set E := exp (r' • A)
  set EI := sys.expIntervalFloat r r η
  have hE : E ∈ EI.construct := sys.exp_mem_expIntervalFloat hη le_rfl le_rfl
  have hmulZ : ∀ (Z : Zonotope (Vec 𝕋 n)) (v : Vec ℝ n), v ∈ Z.construct →
      E *ᵥ v ∈ (Mtimes.mtimes (𝕄 := ℐ[𝕋])
        (S := 𝒵[𝕋]) EI Z).construct :=
    fun Z v hv => Mtimes.mtimes_outer (𝕄 := ℐ[𝕋])
      (S := 𝒵[𝕋]) EI Z
      (Set.mem_biUnion hE (Set.mem_image_of_mem _ hv))
  have hmulB : ∀ (B : ZonoBundle (Vec 𝕋 n)) (v : Vec ℝ n), v ∈ B.construct →
      E *ᵥ v ∈ (Mtimes.mtimes (𝕄 := ℐ[𝕋])
        (S := 𝒵ℬ[𝕋]) EI B).construct :=
    fun B v hv => Mtimes.mtimes_outer (𝕄 := ℐ[𝕋])
      (S := 𝒵ℬ[𝕋]) EI B
      (Set.mem_biUnion hE (Set.mem_image_of_mem _ hv))
  -- the loop's state, its step and its output, and the closed form of the list it builds
  set step : ZonoBundle (Vec 𝕋 n) × Zonotope (Vec 𝕋 n) × Zonotope (Vec 𝕋 n)
      → ZonoBundle (Vec 𝕋 n) × Zonotope (Vec 𝕋 n) × Zonotope (Vec 𝕋 n) :=
    fun s => (Mtimes.mtimes (𝕄 := ℐ[𝕋])
      (S := 𝒵ℬ[𝕋]) EI s.1,
      Mtimes.mtimes (𝕄 := ℐ[𝕋])
        (S := 𝒵[𝕋]) EI s.2.1,
      Plus.plus s.2.2
        (Mtimes.mtimes (𝕄 := ℐ[𝕋]) (S := 𝒵[𝕋]) EI
          s.2.1).interval.zonotope)
  set out : ZonoBundle (Vec 𝕋 n) × Zonotope (Vec 𝕋 n) × Zonotope (Vec 𝕋 n) → ZonoBundle (Vec 𝕋 n) :=
    fun s => Plus.plus s.1 s.2.2.zonoBundle
  set s₀ := (Rh₀, Ri₀, Ri₀.interval.zonotope)
  have hlist : sys.bundleReachFloat Rh₀ Ri₀ r η N
      = (List.range (N + 1)).map fun j => out (step^[j] s₀) :=
    congrArg Prod.snd (foldl_range_step_out step out s₀ N)
  -- the time `k r` is nonnegative
  have hkr : ∀ k : ℕ, (0:ℝ) ≤ k * r' := fun k => mul_nonneg (Nat.cast_nonneg k) hr
  -- the three invariants
  have hinv : ∀ k : ℕ, ∀ τ ∈ Set.Icc (0:ℝ) r',
      (fun x => exp ((k * r' + τ) • A) *ᵥ x) '' construct X₀ ⊆ (step^[k] s₀).1.construct
      ∧ (fun y => exp ((k * r') • A) *ᵥ y) '' sys.inputReach U τ ⊆ (step^[k] s₀).2.1.construct
      ∧ sys.inputReach U (k * r' + τ) ⊆ (step^[k] s₀).2.2.construct := by
    intro k
    induction k with
    | zero =>
      intro τ hτ
      simp only [Nat.cast_zero, zero_mul, zero_add, zero_smul, exp_zero, Matrix.one_mulVec,
        Set.image_id', Function.iterate_zero, id]
      exact ⟨hh τ hτ, hi τ hτ,
        (hi τ hτ).trans ((Zonotope.interval_contains _).trans (Interval.zonotope_contains _))⟩
    | succ k ih =>
      -- one more `e^{Ar}`, which splits `e^{A(k+1)r}` into `e^{Ar} e^{Akr}`
      intro τ hτ
      have hτ0 := hτ.1
      rw [Function.iterate_succ_apply']
      have hEk : exp ((((k + 1 : ℕ) : ℝ) * r') • A) = E * exp ((k * r') • A) := by
        rw [show ((k + 1 : ℕ) : ℝ) * r' = r' + k * r' by push_cast; ring,
          exp_add_smul_eq_mul]
      have hEkτ : exp ((((k + 1 : ℕ) : ℝ) * r' + τ) • A) = E * exp ((k * r' + τ) • A) := by
        rw [show ((k + 1 : ℕ) : ℝ) * r' + τ = r' + (k * r' + τ) by push_cast; ring,
          exp_add_smul_eq_mul]
      have h2 : (fun y => exp ((((k + 1 : ℕ) : ℝ) * r') • A) *ᵥ y) '' sys.inputReach U τ
          ⊆ (step (step^[k] s₀)).2.1.construct := by
        rintro _ ⟨v, hv, rfl⟩
        have := hmulZ _ _ ((ih τ hτ).2.1 ⟨v, hv, rfl⟩)
        simpa only [hEk, Matrix.mulVec_mulVec] using this
      -- the homogeneous part
      refine ⟨?_, h2, ?_⟩
      · rintro _ ⟨x, hx, rfl⟩
        have := hmulB _ _ ((ih τ hτ).1 ⟨x, hx, rfl⟩)
        simpa only [hEkτ, Matrix.mulVec_mulVec] using this
      · have hsep := sys.inputReach_separation_eq hτ0 (hkr (k + 1)) hU
        rw [show (((k + 1 : ℕ) : ℝ) * r' + τ) = τ + ((k + 1 : ℕ) : ℝ) * r' by ring, hsep]
        rintro _ ⟨_, hw, v, hv, rfl⟩
        have hr'' : r' ∈ Set.Icc (0:ℝ) r' := ⟨hr, le_rfl⟩
        have hP := (ih r' hr'').2.2
        rw [show ((k : ℝ) * r' + r') = ((k + 1 : ℕ) : ℝ) * r' by push_cast; ring] at hP
        have hb : _ ∈ (Mtimes.mtimes (𝕄 := ℐ[𝕋])
          (S := 𝒵[𝕋]) EI
            (step^[k] s₀).2.1).interval.zonotope.construct :=
          (Zonotope.interval_contains _).trans (Interval.zonotope_contains _) (h2 hw)
        exact Plus.plus_outer (S := Zonotope (Vec 𝕋 n)) _ _ ⟨v, hP hv, _, hb, add_comm _ _⟩
  -- the window `t ∈ [kr, (k+1)r]` is `τ = t - kr ∈ [0, r]`
  have hτ : t - k * r' ∈ Set.Icc (0:ℝ) r' := ⟨by linarith [ht.1], by linarith [ht.2]⟩
  refine ⟨out (step^[k] s₀), ?_, ?_⟩
  · rw [hlist, List.getElem?_map, List.getElem?_range (by omega)]
    rfl
  · have ht0 : 0 ≤ t := (hkr k).trans ht.1
    rw [sys.reachSetExact_eq X₀ U ht0 hU]
    rintro _ ⟨_, ⟨x, hx, rfl⟩, v, hv, rfl⟩
    have hI := hinv k (t - k * r') hτ
    rw [show (k : ℝ) * r' + (t - k * r') = t by ring] at hI
    have hv' : v ∈ (step^[k] s₀).2.2.zonoBundle.construct := by
      rw [← Zonotope.zonoBundle_exact]
      exact hI.2.2 hv
    exact Plus.plus_outer (S := ZonoBundle (Vec 𝕋 n)) _ _
      ⟨_, hI.1 ⟨x, hx, rfl⟩, v, hv', rfl⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
