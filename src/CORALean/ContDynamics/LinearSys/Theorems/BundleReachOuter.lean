import CORALean.ContDynamics.LinearSys.Operations.BundleReach
import CORALean.ContDynamics.LinearSys.Theorems.ReachSetEq
import CORALean.ContDynamics.LinearSys.Theorems.InputReachSeparationEq
import CORALean.ContSet.ZonoBundle.Real.Theorems.MtimesOuter
import CORALean.ContSet.ZonoBundle.Real.Theorems.PlusOuter
import CORALean.ContSet.Zonotope.Real.Theorems.MtimesExact
import CORALean.ContSet.Zonotope.Real.Theorems.PlusExact

/-!
# [1, Alg. 1] encloses the reachable set on every time interval

If `R^h_0` contains `e^{Aτ}X₀` and `R^i_0` contains `inputReach U τ` for every `τ ∈ [0, r]`,
the listing's own inputs `R^h([0, t_1])` and `R^i([0, t_1])`, then `R_k ⊇ R(t)` for every
`t ∈ [kr, (k+1)r]` and `k ≤ N`: the claim of [1, Alg. 1] that it computes `R([t_k, t_{k+1}])`.
`R(t)` is `reachSet` on `[0, t]`. Three invariants, by induction on `k`, at every
`τ ∈ [0, r]`: `e^{A(kr+τ)}X₀ ⊆ R^h_k`, `e^{Akr} inputReach U τ ⊆ R^i_k` and
`inputReach U (kr+τ) ⊆ P_k`; the last is where the superposition is, the input over
`[0, (k+1)r+τ]` separating into `e^{A(k+1)r}` of the input over `[0, τ]` plus the input over
`[0, (k+1)r]` (`inputReach_separation_eq`). The sum of a bundle and a zonotope is enclosed by
[1, Prop. 2], the image of a bundle by [1, Prop. 1]. Nothing is claimed of the tightness.

## References

* [1] M. Althoff and B. H. Krogh. "Zonotope Bundles for the Efficient Computation of
      Reachable Sets". In Proc. of the 50th IEEE Conference on Decision and Control and
      European Control Conference (CDC-ECC), pp. 6814-6821, 2011.
-/

-- Authors:       Tobias Ladner
-- Written:       01-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real
open Matrix ContSet Scalar NormedSpace Pointwise

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- `k` passes of a loop that steps its state and appends what the new state outputs. -/
theorem aux_foldl_step {σ β : Type} (step : σ → σ) (out : σ → β) (s₀ : σ) (k : ℕ) :
    (List.range k).foldl (fun (P : σ × List β) (_ : ℕ) => (step P.1, P.2 ++ [out (step P.1)]))
      (s₀, [out s₀])
      = (step^[k] s₀,
        (List.range (k + 1)).map fun j => out (step^[j] s₀)) := by -- --- PROOF ---
  induction k with
  | zero => simp
  | succ k ih =>
    rw [List.range_succ, List.foldl_append, ih]
    simp [List.range_succ, Function.iterate_succ_apply']

/-- `e^{A(a+b)} = e^{Aa} e^{Ab}`. -/
theorem aux_exp_add_smul_eq_mul (A : Mat ℝ n n) (a b : ℝ) :
    exp ((a + b) • A) = exp (a • A) * exp (b • A) := by
  rw [add_smul]
  exact exp_add_of_commute (((Commute.refl A).smul_left a).smul_right b)


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Alg. 1]: `R_k` encloses the reachable set at every `t ∈ [t_k, t_{k+1}]`, `k ≤ N`. -/
theorem LinearSys.bundleReach_outer (sys : LinearSys 𝕋 n) (X₀ U : S n)
    (Rh₀ : ZonoBundle (Vec ℝ n)) (Ri₀ : Zonotope (Vec ℝ n)) {r : ℝ} (hr : 0 ≤ r)
    (hU : Bornology.IsBounded (construct U))
    (hh : ∀ τ ∈ Set.Icc (0:ℝ) r,
      (fun x => exp (τ • toRealMat sys.A) *ᵥ x) '' construct X₀ ⊆ Rh₀.construct)
    (hi : ∀ τ ∈ Set.Icc (0:ℝ) r, sys.inputReach U τ ⊆ Ri₀.construct)
    {N k : ℕ} (hk : k ≤ N) {t : ℝ} (ht : t ∈ Set.Icc ((k : ℝ) * r) ((k + 1) * r)) :
    ∃ R, (sys.bundleReach Rh₀ Ri₀ r N)[k]? = some R
      ∧ sys.reachSet (Set.Icc 0 t) X₀ U t ⊆ R.construct := by -- --- PROOF ---
  set A := toRealMat sys.A
  set E := exp (r • A)
  set step : ZonoBundle (Vec ℝ n) × Zonotope (Vec ℝ n) × Zonotope (Vec ℝ n)
      → ZonoBundle (Vec ℝ n) × Zonotope (Vec ℝ n) × Zonotope (Vec ℝ n) :=
    fun s => (s.1.mtimes E, s.2.1.mtimes E, s.2.2.plus (s.2.1.mtimes E).interval.zonotope)
  set out : ZonoBundle (Vec ℝ n) × Zonotope (Vec ℝ n) × Zonotope (Vec ℝ n)
      → ZonoBundle (Vec ℝ n) := fun s => s.1.plus s.2.2.zonoBundle
  set s₀ := (Rh₀, Ri₀, Ri₀.interval.zonotope)
  have hlist : sys.bundleReach Rh₀ Ri₀ r N
      = (List.range (N + 1)).map fun j => out (step^[j] s₀) :=
    congrArg Prod.snd (aux_foldl_step step out s₀ N)
  have hkr : ∀ k : ℕ, (0:ℝ) ≤ k * r := fun k => mul_nonneg (Nat.cast_nonneg k) hr
  -- the three invariants
  have hinv : ∀ k : ℕ, ∀ τ ∈ Set.Icc (0:ℝ) r,
      (fun x => exp ((k * r + τ) • A) *ᵥ x) '' construct X₀ ⊆ (step^[k] s₀).1.construct
      ∧ (fun y => exp ((k * r) • A) *ᵥ y) '' sys.inputReach U τ ⊆ (step^[k] s₀).2.1.construct
      ∧ sys.inputReach U (k * r + τ) ⊆ (step^[k] s₀).2.2.construct := by
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
        rw [show ((k + 1 : ℕ) : ℝ) * r = r + k * r by push_cast; ring, aux_exp_add_smul_eq_mul]
      have hEkτ : exp ((((k + 1 : ℕ) : ℝ) * r + τ) • A) = E * exp ((k * r + τ) • A) := by
        rw [show ((k + 1 : ℕ) : ℝ) * r + τ = r + (k * r + τ) by push_cast; ring,
          aux_exp_add_smul_eq_mul]
      -- the homogeneous part: one more `e^{Ar}`
      have h2 : (fun y => exp ((((k + 1 : ℕ) : ℝ) * r) • A) *ᵥ y) '' sys.inputReach U τ
          ⊆ (step (step^[k] s₀)).2.1.construct := by
        rintro _ ⟨v, hv, rfl⟩
        show _ ∈ ((step^[k] s₀).2.1.mtimes E).construct
        rw [← Zonotope.mtimes_exact]
        refine ⟨_, (ih τ hτ).2.1 ⟨v, hv, rfl⟩, ?_⟩
        simp only [hEk, Matrix.mulVec_mulVec]
      refine ⟨?_, h2, ?_⟩
      · rintro _ ⟨x, hx, rfl⟩
        -- the homogeneous part, one more `e^{Ar}`
        refine ZonoBundle.mtimes_outer E _ ⟨_, (ih τ hτ).1 ⟨x, hx, rfl⟩, ?_⟩
        simp only [hEkτ, Matrix.mulVec_mulVec]
      -- the input part: what `[0, τ]` contributes, propagated, plus `[0, (k+1)r]`
      · have hsep := sys.inputReach_separation_eq hτ0 (hkr (k + 1)) hU
        rw [show (((k + 1 : ℕ) : ℝ) * r + τ) = τ + ((k + 1 : ℕ) : ℝ) * r by ring, hsep]
        rintro _ ⟨_, hw, v, hv, rfl⟩
        show _ ∈ ((step^[k] s₀).2.2.plus
          ((step^[k] s₀).2.1.mtimes E).interval.zonotope).construct
        rw [← Zonotope.plus_exact]
        refine ⟨v, ?_, _, (Zonotope.interval_contains _).trans (Interval.zonotope_contains _)
          (h2 hw), add_comm _ _⟩
        have hr' : r ∈ Set.Icc (0:ℝ) r := ⟨hr, le_rfl⟩
        have := (ih r hr').2.2
        rw [show ((k : ℝ) * r + r) = ((k + 1 : ℕ) : ℝ) * r by push_cast; ring] at this
        exact this hv
  -- the window `t ∈ [kr, (k+1)r]` is `τ = t - kr ∈ [0, r]`
  have hτ : t - k * r ∈ Set.Icc (0:ℝ) r := ⟨by linarith [ht.1], by linarith [ht.2]⟩
  refine ⟨out (step^[k] s₀), ?_, ?_⟩
  · rw [hlist, List.getElem?_map, List.getElem?_range (by omega)]
    rfl
  · have ht0 : 0 ≤ t := (hkr k).trans ht.1
    rw [sys.reachSet_eq X₀ U ht0 hU]
    rintro _ ⟨_, ⟨x, hx, rfl⟩, v, hv, rfl⟩
    have hI := hinv k (t - k * r) hτ
    rw [show (k : ℝ) * r + (t - k * r) = t by ring] at hI
    refine ZonoBundle.plus_outer _ _ ⟨_, hI.1 ⟨x, hx, rfl⟩, v, ?_, rfl⟩
    rw [← Zonotope.zonoBundle_exact]
    exact hI.2.2 hv

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
