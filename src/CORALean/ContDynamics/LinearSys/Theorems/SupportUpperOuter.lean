import CORALean.ContDynamics.LinearSys.Operations.SupportUpper
import CORALean.ContDynamics.LinearSys.Definitions.ReachSet
import CORALean.ContDynamics.LinearSys.MatExp.Theorems.ConstCorrectionMatrix
import CORALean.ContDynamics.LinearSys.MatExp.Theorems.CorrectionMatrix
import CORALean.ContDynamics.LinearSys.Theorems.ExpIntegralAddMulVec
import CORALean.ContDynamics.LinearSys.Theorems.InputReachMono
import CORALean.ContDynamics.LinearSys.Theorems.InputReachSubsetInputSolution
import CORALean.ContDynamics.LinearSys.Theorems.PropagateInputReach
import CORALean.ContDynamics.LinearSys.Theorems.PropagateInputSolutionMono
import CORALean.ContDynamics.LinearSys.Theorems.TrajectorySubMemInputReachRecentre
import CORALean.ContSet.ContSet.Definitions.CompactSet
import CORALean.ContSet.ContSet.Definitions.ConvexSet
import CORALean.ContSet.ContSet.Theorems.IsBoundedConstruct
import CORALean.ContSet.ContSet.Theorems.IsClosedConstruct

/-!
# Lines 12 and 13 bound the support function of the reachable set

[1, Alg. 1 (upper bounds)]: line 12's `ρ(R̂(t_k), ℓ)` is at least `ℓ` at every state of the exact
reachable set `R(t_k)`, and line 13's `ρ(R̂(τ_k), ℓ)` at least `ℓ` at every state `R(t)` reaches
at a time `t` of `τ_k`. A state splits as `e^{tA}x(0)`, the constant input `ũ`'s share `Γ(t)ũ`
(`Pu`, line 9) and one admissible `U₀`-input's `inputReach U₀ t` (`Recentre`); the last is
propagated `k` times from the one step `inputReach U₀ Δt`, which line 4's `P̂_U(Δt)` encloses
(line 11). On `τ_k` the first two interpolate between `H(t_k)` and `H(t_{k+1})` up to
`e^{At_k}(F X₀ ⊕ G ũ)` (`C`, line 5), and `0 ∈ U₀` carries `inputReach U₀ t` into
`inputReach U₀ t_{k+1}`. `ρ` is hypothesised to bound the support function of every set it is
asked for; `η ≥ 2` is `m + 2`, Eq. (14) starting its sum at `i = 2`.

## References

* [1] M. Wetzlinger, N. Kochdumper, S. Bak and M. Althoff. "Fully-Automated
      Verification of Linear Systems Using Reachability Analysis with Support
      Functions". HSCC, 2023, Article 5.
-/

-- Authors:       Claude Opus 5.5
-- Written:       11-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real
open Matrix ContSet Scalar NormedSpace Pointwise

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]
variable [∀ n, Plus (S n) (Vec ℝ n)] [∀ n, OfPoint (S n) (Vec ℝ n)]
variable [∀ n, Recentre (S n) (Vec ℝ n)] [Mtimes (Mat ℝ) S] [Mtimes ℐ S]


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- Line 8 in closed form: `d_k = ℓ ∘ e^{AΔt k}`. -/
theorem aux_supportUpper_d (sys : LinearSys 𝕋 n) (Δt : ℝ) (η : ℕ) (X₀ U : S n)
    (ρ : S n → (Vec ℝ n →ₗ[ℝ] ℝ) → ℝ) (ℓ : Vec ℝ n →ₗ[ℝ] ℝ) (k : ℕ) :
    (sys.supportUpper Δt η X₀ U ρ ℓ k).d
      = ℓ.comp (mulVecLin (exp (Δt • toRealMat sys.A) ^ k)) := by -- --- PROOF ---
  induction k with
  | zero =>
    show ℓ = _
    rw [pow_zero, Matrix.mulVecLin_one, LinearMap.comp_id]
  | succ k ih =>
    show (sys.supportUpper Δt η X₀ U ρ ℓ k).d.comp (mulVecLin (exp (Δt • toRealMat sys.A))) = _
    rw [ih, pow_succ, Matrix.mulVecLin_mul, LinearMap.comp_assoc]

/-- Line 9 in closed form: `P_u(t_k) = Γ(t_k) ũ`, `Γ(t) = ∫₀ᵗ e^{Aσ}dσ`. -/
theorem aux_supportUpper_Pu (sys : LinearSys 𝕋 n) {Δt : ℝ} (hΔt : 0 ≤ Δt) (η : ℕ)
    (X₀ U : S n) (ρ : S n → (Vec ℝ n →ₗ[ℝ] ℝ) → ℝ) (ℓ : Vec ℝ n →ₗ[ℝ] ℝ) (k : ℕ) :
    (sys.supportUpper Δt η X₀ U ρ ℓ k).Pu
      = MatExp.expIntegral (toRealMat sys.A) ((k : ℝ) * Δt)
        *ᵥ Recentre.centre U := by -- --- PROOF ---
  induction k with
  | zero =>
    show (0 : Vec ℝ n) = _
    rw [Nat.cast_zero, zero_mul, Real.MatExp.expIntegral_mulVec _ _ le_rfl,
      intervalIntegral.integral_same]
  | succ k ih =>
    show exp (Δt • toRealMat sys.A) *ᵥ (sys.supportUpper Δt η X₀ U ρ ℓ k).Pu
      + MatExp.expIntegral (toRealMat sys.A) Δt *ᵥ Recentre.centre U = _
    rw [ih, Nat.cast_succ, add_one_mul, MatExp.expIntegral_add_mulVec _ _
      (mul_nonneg k.cast_nonneg hΔt) hΔt]

/-- Line 11 in closed form: `ρ(P̂_U(t_k), ℓ) = ∑_{j<k} ρ(P̂_U(Δt), d_j)`. -/
theorem aux_supportUpper_ρP (sys : LinearSys 𝕋 n) (Δt : ℝ) (η : ℕ) (X₀ U : S n)
    (ρ : S n → (Vec ℝ n →ₗ[ℝ] ℝ) → ℝ) (ℓ : Vec ℝ n →ₗ[ℝ] ℝ) (k : ℕ) :
    (sys.supportUpper Δt η X₀ U ρ ℓ k).ρP
      = ∑ j ∈ Finset.range k, ρ (sys.inputSolution Δt η (Recentre.recentre U))
          (ℓ.comp (mulVecLin (exp (Δt • toRealMat sys.A) ^ j))) := by -- --- PROOF ---
  induction k with
  | zero => rfl
  | succ k ih =>
    show (sys.supportUpper Δt η X₀ U ρ ℓ k).ρP
      + ρ (sys.inputSolution Δt η (Recentre.recentre U))
        (sys.supportUpper Δt η X₀ U ρ ℓ k).d = _
    rw [ih, aux_supportUpper_d, Finset.sum_range_succ]

/-- Lines 10 and 1 together: `ρ(H(t_k), ℓ) = ρ(X₀, d_k) + ℓ P_u(t_k)`. -/
theorem aux_supportUpper_ρH (sys : LinearSys 𝕋 n) (Δt : ℝ) (η : ℕ) (X₀ U : S n)
    (ρ : S n → (Vec ℝ n →ₗ[ℝ] ℝ) → ℝ) (ℓ : Vec ℝ n →ₗ[ℝ] ℝ) (k : ℕ) :
    (sys.supportUpper Δt η X₀ U ρ ℓ k).ρH
      = ρ X₀ (sys.supportUpper Δt η X₀ U ρ ℓ k).d
        + ℓ (sys.supportUpper Δt η X₀ U ρ ℓ k).Pu := by -- --- PROOF ---
  cases k with
  | zero =>
    show ρ X₀ ℓ = ρ X₀ ℓ + ℓ 0
    simp
  | succ k => rfl

/-- `e^{AΔt}` carried `j` times is the flow over `jΔt`. -/
theorem aux_exp_smul_eq_pow (A : Mat ℝ n n) (Δt : ℝ) (j : ℕ) :
    exp (((j : ℝ) * Δt) • A) = exp (Δt • A) ^ j := by
  have h1 : ((j : ℝ) * Δt) • A = j • (Δt • A) := by
    rw [← Nat.cast_smul_eq_nsmul ℝ, smul_smul]
  rw [h1]
  exact NormedSpace.exp_nsmul j _

/-- `P̂`'s propagation, bounded term by term: the `j`-th copy carried across `t_j` is read along
`d_j`. -/
theorem aux_propagate_le (sys : LinearSys 𝕋 n) (Δt : ℝ) {Z : Set (Vec ℝ n)}
    {ρZ : (Vec ℝ n →ₗ[ℝ] ℝ) → ℝ} (hZ : ∀ z ∈ Z, ∀ d : Vec ℝ n →ₗ[ℝ] ℝ, d z ≤ ρZ d)
    (ℓ : Vec ℝ n →ₗ[ℝ] ℝ) (m : ℕ) :
    ∀ y ∈ sys.propagateInputSolution Δt Z m,
      ℓ y ≤ ∑ j ∈ Finset.range m,
        ρZ (ℓ.comp (mulVecLin (exp (Δt • toRealMat sys.A) ^ j))) := by -- --- PROOF ---
  induction m with
  | zero =>
    intro y hy
    simp only [LinearSys.propagateInputSolution, Set.mem_singleton_iff] at hy
    simp [hy]
  | succ m ih =>
    rintro _ ⟨y, hy, _, ⟨z, hz, rfl⟩, rfl⟩
    have hpow := aux_exp_smul_eq_pow (toRealMat sys.A) Δt m
    rw [map_add, Finset.sum_range_succ]
    refine add_le_add (ih y hy) ?_
    show ℓ (exp (((m : ℝ) * Δt) • toRealMat sys.A) *ᵥ z) ≤ _
    rw [hpow]
    exact hZ z hz (ℓ.comp (mulVecLin (exp (Δt • toRealMat sys.A) ^ m)))

/-- Line 12 is lines 10 and 11 added, at every step. -/
theorem aux_supportUpper_ρR (sys : LinearSys 𝕋 n) (Δt : ℝ) (η : ℕ) (X₀ U : S n)
    (ρ : S n → (Vec ℝ n →ₗ[ℝ] ℝ) → ℝ) (ℓ : Vec ℝ n →ₗ[ℝ] ℝ) (k : ℕ) :
    (sys.supportUpper Δt η X₀ U ρ ℓ k).ρR
      = (sys.supportUpper Δt η X₀ U ρ ℓ k).ρH + (sys.supportUpper Δt η X₀ U ρ ℓ k).ρP := by
  cases k <;> rfl


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Alg. 1 (upper bounds)], lines 12 and 13: `ρ(R̂(t_k), ℓ)` bounds `ℓ` over the exact
reachable set at `t_k`, and `ρ(R̂(τ_k), ℓ)` over what it reaches at any time of `τ_k`. -/
theorem LinearSys.supportUpper_outer
    [∀ n, ConvexSet (S n) (Vec ℝ n)] [∀ n, CompactSet (S n) (Vec ℝ n)]
    (sys : LinearSys 𝕋 n) {Δt : ℝ} (hΔt : 0 < Δt) {m : ℕ}
    (hε : ‖Δt • toRealMat sys.A‖ / (((m + 2 : ℕ) : ℝ) + 2) < 1) (X₀ U : S n)
    {ρ : S n → (Vec ℝ n →ₗ[ℝ] ℝ) → ℝ}
    (hρ : ∀ X : S n, ∀ x ∈ construct X, ∀ d : Vec ℝ n →ₗ[ℝ] ℝ, d x ≤ ρ X d)
    (ℓ : Vec ℝ n →ₗ[ℝ] ℝ) (k : ℕ) :
    (∀ x ∈ sys.reachSet (Set.Icc 0 ((k : ℝ) * Δt)) X₀ U ((k : ℝ) * Δt),
        ℓ x ≤ (sys.supportUpper Δt (m + 2) X₀ U ρ ℓ k).ρR) ∧
    (∀ t ∈ Set.Icc ((k : ℝ) * Δt) (((k + 1 : ℕ) : ℝ) * Δt),
      ∀ x ∈ sys.reachSet (Set.Icc 0 t) X₀ U t,
        ℓ x ≤ (sys.supportUpper Δt (m + 2) X₀ U ρ ℓ (k + 1)).ρRτ) := by -- --- PROOF ---
  set A := toRealMat sys.A with hA
  set c := Recentre.centre U with hc
  set U₀ := Recentre.recentre U with hU₀
  set PU := sys.inputSolution Δt (m + 2) U₀ with hPU
  have hbdd₀ : Bornology.IsBounded (construct U₀) := CompactSet.isBounded_construct U₀
  have h0 : (0 : Vec ℝ n) ∈ construct U₀ := Recentre.zero_mem_recentre U
  -- line 4: one step of the input is inside `P̂_U(Δt)`
  have hΔ : sys.inputReach U₀ Δt ⊆ construct PU :=
    sys.inputReach_subset_inputSolution hΔt (m + 2) hε (ConvexSet.convex_construct U₀)
      (CompactSet.isClosed_construct U₀) hbdd₀ (ConvexSet.convex_construct _)
      (CompactSet.isClosed_construct _) (CompactSet.isBounded_construct _)
  -- line 11: `j` steps of it are inside the sum of `ρ(P̂_U(Δt), d_i)`
  have hw : ∀ (j : ℕ) (w : Vec ℝ n), w ∈ sys.inputReach U₀ ((j : ℝ) * Δt) →
      ℓ w ≤ ∑ i ∈ Finset.range j, ρ PU (ℓ.comp (mulVecLin (exp (Δt • A) ^ i))) := by
    intro j w hwj
    rw [← sys.propagateInputSolution_inputReach hΔt.le hbdd₀ ⟨0, h0⟩ j] at hwj
    exact aux_propagate_le sys Δt (fun z hz d => hρ PU z hz d) ℓ j w
      (sys.propagateInputSolution_mono Δt hΔ j hwj)
  -- lines 1, 9, 10 at a step `j`: `z(jΔt)` is under `ρ(H(t_j), ℓ)`
  have hz : ∀ (j : ℕ) (x₀ : Vec ℝ n), x₀ ∈ construct X₀ →
      ℓ (exp (((j : ℝ) * Δt) • A) *ᵥ x₀ + MatExp.expIntegral A ((j : ℝ) * Δt) *ᵥ c)
        ≤ (sys.supportUpper Δt (m + 2) X₀ U ρ ℓ j).ρH := by
    intro j x₀ hx₀
    rw [aux_supportUpper_ρH, aux_supportUpper_d, aux_supportUpper_Pu sys hΔt.le, map_add]
    refine add_le_add ?_ le_rfl
    have := hρ X₀ x₀ hx₀ (ℓ.comp (mulVecLin (exp (Δt • A) ^ j)))
    rw [aux_exp_smul_eq_pow]
    exact this
  refine ⟨?_, ?_⟩
  · -- line 12
    rintro _ ⟨x, u, traj, rfl⟩
    have hk0 : (0 : ℝ) ≤ (k : ℝ) * Δt := mul_nonneg k.cast_nonneg hΔt.le
    have hmem := traj.sub_mem_inputReach_recentre (V := U) subset_rfl ⟨hk0, le_rfl⟩
    rw [aux_supportUpper_ρR, aux_supportUpper_ρP, ← sub_add_cancel (x ((k : ℝ) * Δt))
      (exp (((k : ℝ) * Δt) • A) *ᵥ x 0 + MatExp.expIntegral A ((k : ℝ) * Δt) *ᵥ c),
      add_comm (x _ - _), map_add]
    exact add_le_add (hz k (x 0) traj.init) (hw k _ hmem)
  · -- line 13
    rintro t ht _ ⟨x, u, traj, rfl⟩
    have hk0 : (0 : ℝ) ≤ (k : ℝ) * Δt := mul_nonneg k.cast_nonneg hΔt.le
    have ht0 : 0 ≤ t := le_trans hk0 ht.1
    have hmem := traj.sub_mem_inputReach_recentre (V := U) subset_rfl ⟨ht0, le_rfl⟩
    -- the particular solution of `U₀` up to `t` is inside the one up to `t_{k+1}`, as `0 ∈ U₀`
    have hmem' := sys.inputReach_mono hbdd₀ h0 ht0 ht.2 hmem
    have hP : ℓ (x t - (exp (t • A) *ᵥ x 0 + MatExp.expIntegral A t *ᵥ c))
        ≤ (sys.supportUpper Δt (m + 2) X₀ U ρ ℓ (k + 1)).ρP := by
      rw [aux_supportUpper_ρP]
      exact hw (k + 1) _ hmem'
    -- the time inside `τ_k`, and its position `λ` along it
    set s : ℝ := t - (k : ℝ) * Δt with hs
    have hs0 : 0 ≤ s := sub_nonneg.mpr ht.1
    have hsΔ : s ≤ Δt := by
      have := ht.2
      push_cast at this
      linarith
    set lam : ℝ := s / Δt with hlam
    have hlam0 : 0 ≤ lam := div_nonneg hs0 hΔt.le
    have hlam1 : lam ≤ 1 := (div_le_one hΔt).mpr hsΔ
    -- the flow over `t`, `t_k` and `t_{k+1}` in terms of `e^{At_k}`
    set E := exp (((k : ℝ) * Δt) • A) with hE
    have hexp : ∀ r : ℝ, exp (((k : ℝ) * Δt + r) • A) = E * exp (r • A) := fun r => by
      rw [add_smul]
      exact exp_add_of_commute (((Commute.refl A).smul_left _).smul_right _)
    have hts : t = (k : ℝ) * Δt + s := by rw [hs]; ring
    have hk1 : (((k + 1 : ℕ) : ℝ) * Δt) = (k : ℝ) * Δt + Δt := by push_cast; ring
    have hΓ : ∀ r : ℝ, 0 ≤ r → MatExp.expIntegral A ((k : ℝ) * Δt + r) *ᵥ c
        = E *ᵥ (MatExp.expIntegral A r *ᵥ c) + MatExp.expIntegral A ((k : ℝ) * Δt) *ᵥ c := by
      intro r hr
      rw [add_comm, MatExp.expIntegral_add_mulVec A c hr hk0]
    -- the interpolation between `z(t_k)` and `z(t_{k+1})` and its error
    set Fs := exp (s • A) - 1 - lam • (exp (Δt • A) - 1) with hFs
    set Gs := MatExp.expIntegral A s - lam • MatExp.expIntegral A Δt with hGs
    have hzid : ∀ x₀ : Vec ℝ n, exp (t • A) *ᵥ x₀ + MatExp.expIntegral A t *ᵥ c
        = (1 - lam) • (exp (((k : ℝ) * Δt) • A) *ᵥ x₀
            + MatExp.expIntegral A ((k : ℝ) * Δt) *ᵥ c)
          + lam • (exp ((((k + 1 : ℕ) : ℝ) * Δt) • A) *ᵥ x₀
            + MatExp.expIntegral A (((k + 1 : ℕ) : ℝ) * Δt) *ᵥ c)
          + E *ᵥ (Fs *ᵥ x₀ + Gs *ᵥ c) := by
      intro x₀
      rw [hts, hexp, hΓ s hs0, hk1, hexp, hΓ Δt hΔt.le, ← hE, hFs, hGs]
      simp only [← Matrix.mulVec_mulVec, Matrix.sub_mulVec, Matrix.smul_mulVec,
        Matrix.mulVec_add, Matrix.mulVec_sub, Matrix.mulVec_smul, Matrix.one_mulVec]
      module
    -- the correction `E (F x₀ ⊕ G ũ)` lies in `e^{At_k} C`, so `ρ(C, d_k)` bounds it
    have hFmem : Fs ∈ (MatExp.correctionMatrix A Δt (m + 2)).construct :=
      MatExp.expDiff_mem_correctionMatrix A hΔt hε hs0 hsΔ
    have hGmem : Gs ∈ (MatExp.constCorrectionMatrix A Δt (m + 2)).construct :=
      MatExp.expIntegralDiff_mem_constCorrectionMatrix A hΔt (m + 2) hε hs0 hsΔ
    have hC : Fs *ᵥ x 0 + Gs *ᵥ c ∈ construct (Plus.plus
        (Mtimes.mtimes (𝕄 := ℐ) (MatExp.correctionMatrix A Δt (m + 2)) X₀)
        (Mtimes.mtimes (𝕄 := ℐ) (MatExp.constCorrectionMatrix A Δt (m + 2))
          (OfPoint.ofPoint c))) :=
      Plus.plus_outer _ _ (Set.add_mem_add
        (Mtimes.mtimes_outer _ _ (Set.mem_biUnion hFmem (Set.mem_image_of_mem _ traj.init)))
        (Mtimes.mtimes_outer _ _
          (Set.mem_biUnion hGmem (Set.mem_image_of_mem _ (OfPoint.mem_ofPoint c)))))
    have hCle := hρ _ _ hC (ℓ.comp (mulVecLin E))
    have hdk : (sys.supportUpper Δt (m + 2) X₀ U ρ ℓ k).d = ℓ.comp (mulVecLin E) := by
      rw [aux_supportUpper_d, hE, aux_exp_smul_eq_pow]
    -- the interpolation is under the larger of the two ends
    have hmax : (1 - lam) * (sys.supportUpper Δt (m + 2) X₀ U ρ ℓ k).ρH
        + lam * (sys.supportUpper Δt (m + 2) X₀ U ρ ℓ (k + 1)).ρH
        ≤ max (sys.supportUpper Δt (m + 2) X₀ U ρ ℓ k).ρH
          (sys.supportUpper Δt (m + 2) X₀ U ρ ℓ (k + 1)).ρH := by
      have h1 := mul_le_mul_of_nonneg_left
        (le_max_left (sys.supportUpper Δt (m + 2) X₀ U ρ ℓ k).ρH
          (sys.supportUpper Δt (m + 2) X₀ U ρ ℓ (k + 1)).ρH) (sub_nonneg.mpr hlam1)
      have h2 := mul_le_mul_of_nonneg_left
        (le_max_right (sys.supportUpper Δt (m + 2) X₀ U ρ ℓ k).ρH
          (sys.supportUpper Δt (m + 2) X₀ U ρ ℓ (k + 1)).ρH) hlam0
      linarith
    -- line 13 as the algorithm computes it
    have hτ : (sys.supportUpper Δt (m + 2) X₀ U ρ ℓ (k + 1)).ρRτ
        = max (sys.supportUpper Δt (m + 2) X₀ U ρ ℓ k).ρH
            (sys.supportUpper Δt (m + 2) X₀ U ρ ℓ (k + 1)).ρH
          + ρ (Plus.plus (Mtimes.mtimes (𝕄 := ℐ) (MatExp.correctionMatrix A Δt (m + 2)) X₀)
            (Mtimes.mtimes (𝕄 := ℐ) (MatExp.constCorrectionMatrix A Δt (m + 2))
              (OfPoint.ofPoint c))) (sys.supportUpper Δt (m + 2) X₀ U ρ ℓ k).d
          + (sys.supportUpper Δt (m + 2) X₀ U ρ ℓ (k + 1)).ρP := rfl
    -- the two ends of the step, and `x t` as the interpolation plus the input's share
    have hk := hz k (x 0) traj.init
    have hk1 := hz (k + 1) (x 0) traj.init
    have hsplit : ℓ (x t) = ℓ (exp (t • A) *ᵥ x 0 + MatExp.expIntegral A t *ᵥ c)
        + ℓ (x t - (exp (t • A) *ᵥ x 0 + MatExp.expIntegral A t *ᵥ c)) := by
      rw [← map_add]
      congr 1
      abel
    have hlin : ℓ (exp (t • A) *ᵥ x 0 + MatExp.expIntegral A t *ᵥ c)
        = (1 - lam) * ℓ (exp (((k : ℝ) * Δt) • A) *ᵥ x 0
            + MatExp.expIntegral A ((k : ℝ) * Δt) *ᵥ c)
          + lam * ℓ (exp ((((k + 1 : ℕ) : ℝ) * Δt) • A) *ᵥ x 0
            + MatExp.expIntegral A (((k + 1 : ℕ) : ℝ) * Δt) *ᵥ c)
          + ℓ (E *ᵥ (Fs *ᵥ x 0 + Gs *ᵥ c)) := by
      rw [hzid (x 0), map_add, map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
    have h1 := mul_le_mul_of_nonneg_left hk (sub_nonneg.mpr hlam1)
    have h2 := mul_le_mul_of_nonneg_left hk1 hlam0
    rw [hsplit, hτ, hlin, hdk]
    simp only [LinearMap.comp_apply, mulVecLin_apply] at hCle ⊢
    linarith

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
