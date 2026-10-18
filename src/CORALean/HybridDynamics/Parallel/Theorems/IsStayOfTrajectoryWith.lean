module

public import CORALean.HybridDynamics.Parallel.Theorems.IsStayTrajectoryWith
public import CORALean.HybridDynamics.Parallel.Theorems.StackUnstack
public import CORALean.HybridDynamics.Parallel.Theorems.Basic
public import CORALean.HybridDynamics.Parallel.Definitions.LiftingExact
public import CORALean.HybridDynamics.Parallel.Definitions.FlowLawConverse

@[expose] public section

/-!
# A stay of the product is a shared stay

The converse of `IsStay.trajectoryWith`, for any flow with `FlowLawConverse`. Given a stay of the
product's location, the components' states are the blocks of its state; at each instant the
converse law supplies the components' inputs, disturbances and global inputs, bound as the
parallel automaton binds them and in the components' sets, under which the product's right-hand
side is every component's own, so each block flows as its component does. The invariant comes
back through `Lifting.Exact`.
-/

-- Authors:       Claude Sonnet 5.5, Claude Opus 5.5
-- Written:       11-October-2026
-- Last update:   18-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix ContSet Scalar MeasureTheory

variable {S G : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] [∀ n, ContSet (G n) (Vec ℝ n)]
variable {𝕋 : Type} [Scalar 𝕋] {k m : ℕ} {n : Fin k → ℕ} {L : Fin k → Type}


-- =======================================  MAIN THEOREM  ======================================= --

/-- A stay of the product at `ℓ` is a stay of the components, whose states are the blocks of the
product's state. -/
theorem ParallelHybridAutomaton.IsStay.ofTrajectoryWith [ExactScalar 𝕋]
    {P : ParallelHybridAutomaton S G k L 𝕋 n m} {F : (∀ i, L i) → LinearSys 𝕋 (∑ i, n i)}
    {U : ∀ ℓ, S (F ℓ).m} {W : ∀ ℓ, S (F ℓ).r} (hF : P.FlowLawConverse F U W)
    {lift : ParallelHybridAutomaton.Lifting S G n m} (hex : lift.Exact) {ℓ : ∀ i, L i} {τ : ℝ}
    {X : ℝ → Vec ℝ (∑ i, n i)} {g' w'}
    (h : ((P.productWith lift F U W).loc ℓ).IsTrajectory τ X g' w') : -- --- STMT ---
    ∃ (x : ∀ i, ℝ → Vec ℝ (n i)) (u : ∀ i, ℝ → Vec ℝ (P.sys ℓ i).m)
      (w : ∀ i, ℝ → Vec ℝ (P.sys ℓ i).r) (g : ℝ → Vec ℝ m),
      P.IsStay ℓ τ x u w g ∧ ∀ i, x i = fun t => unstack (X t) i := by -- --- PROOF ---
  classical
  -- at each instant, the converse law's inputs, disturbances and global inputs
  have key : ∀ t, ∃ uwg : (∀ i, Vec ℝ (P.sys ℓ i).m) × (∀ i, Vec ℝ (P.sys ℓ i).r) × Vec ℝ m,
      t ∈ Set.Icc 0 τ →
      (∀ i j, uwg.1 i j = P.boundInput ℓ (unstack (X t)) uwg.1 uwg.2.2 i j) ∧
      (∀ i, ∃ v ∈ construct ((P.comp i).loc (ℓ i)).U, ∀ j a, P.bindsAt ℓ i j = .global a →
        v j = uwg.2.2 a) ∧
      (∀ i, uwg.2.1 i ∈ construct ((P.comp i).loc (ℓ i)).W) ∧
      ∀ i a, (toRealMat (F ℓ).A *ᵥ X t + toRealMat (F ℓ).B *ᵥ g' t + toRealVec (F ℓ).c +
        toRealMat (F ℓ).E *ᵥ w' t) (finSigmaFinEquiv ⟨i, a⟩) =
        (toRealMat (P.sys ℓ i).A *ᵥ unstack (X t) i + toRealMat (P.sys ℓ i).B *ᵥ uwg.1 i +
          toRealVec (P.sys ℓ i).c + toRealMat (P.sys ℓ i).E *ᵥ uwg.2.1 i) a := by
    intro t
    -- outside the stay nothing is asked
    by_cases ht : t ∈ Set.Icc 0 τ
    · obtain ⟨u, w, g, h1, h2, h3, h4⟩ := hF ℓ (unstack (X t)) (g' t) (w' t) (h.input t ht)
        (h.dist t ht)
      refine ⟨(u, w, g), fun _ => ⟨h1, h2, h3, ?_⟩⟩
      rw [← stack_unstack (X t)]
      simpa only [unstack_stack] using h4
    · exact ⟨(0, 0, 0), fun h' => absurd h' ht⟩
  choose uwg huwg using key
  -- component `i`'s right-hand side, coordinate `a`, is the product's at `⟨i, a⟩`
  set Fp : ℝ → Vec ℝ (∑ i, n i) := fun t => toRealMat (F ℓ).A *ᵥ X t +
    toRealMat (F ℓ).B *ᵥ g' t + toRealVec (F ℓ).c + toRealMat (F ℓ).E *ᵥ w' t
  have hco : ∀ i, ∀ t ∈ Set.Icc 0 τ, (toRealMat (P.sys ℓ i).A *ᵥ unstack (X t) i +
      toRealMat (P.sys ℓ i).B *ᵥ (uwg t).1 i + toRealVec (P.sys ℓ i).c +
        toRealMat (P.sys ℓ i).E *ᵥ (uwg t).2.1 i) = fun a => Fp t (finSigmaFinEquiv ⟨i, a⟩) :=
    fun i t ht => funext fun a => ((huwg t ht).2.2.2 i a).symm
  have hwin : ∀ t ∈ Set.Icc 0 τ, Set.uIcc 0 t ⊆ Set.Icc 0 τ := fun t ht =>
    Set.OrdConnected.uIcc_subset inferInstance (Set.left_mem_Icc.2 h.nonneg) ht
  have hev : ∀ {N : ℕ} {g : ℝ → Vec ℝ N} {t : ℝ}, IntervalIntegrable g volume 0 t →
      ∀ q : Fin N, (∫ s in (0:ℝ)..t, g s) q = ∫ s in (0:ℝ)..t, g s q := fun {N} {_} {_} hg q =>
    ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin N => ℝ) q).intervalIntegral_comp_comm
      hg).symm
  -- the product's integrand read at block `i` is integrable, coordinate by coordinate
  have hbi : ∀ i, ∀ t ∈ Set.Icc 0 τ,
      IntervalIntegrable (fun s a => Fp s (finSigmaFinEquiv ⟨i, a⟩)) volume 0 t :=
    fun i t ht => ⟨Integrable.of_eval fun a => (h.integrable t ht).1.eval _,
      Integrable.of_eval fun a => (h.integrable t ht).2.eval _⟩
  refine ⟨fun i t => unstack (X t) i, fun i t => (uwg t).1 i, fun i t => (uwg t).2.1 i,
    fun t => (uwg t).2.2, ⟨h.nonneg, fun i t ht => (huwg t ht).2.1 i,
    fun i t ht => (huwg t ht).2.2.1 i, fun i => ?_, fun i t ht => ?_,
    fun i => continuousOn_pi.mpr fun a => (continuous_apply _).comp_continuousOn h.cont,
    fun i t ht => ?_, fun i t ht => ?_, fun i j t ht => (huwg t ht).1 i j⟩, fun i => rfl⟩
  · exact (aemeasurable_pi_iff.mpr fun a => h.meas.aemeasurable.eval
      (finSigmaFinEquiv ⟨i, a⟩)).aestronglyMeasurable.congr
        (ae_restrict_of_forall_mem measurableSet_Icc fun t ht => (hco i t ht).symm)
  · exact (intervalIntegrable_congr fun s hs =>
      (hco i s (hwin t ht (Set.uIoc_subset_uIcc hs))).symm).mp (hbi i t ht)
  · -- block `i` of the product's integral equation, coordinate by coordinate
    rw [intervalIntegral.integral_congr fun s hs => hco i s (hwin t ht hs)]
    funext a
    have hX := congrFun (h.flow t ht) (finSigmaFinEquiv ⟨i, a⟩)
    rw [Pi.add_apply, hev (h.integrable t ht)] at hX
    rw [Pi.add_apply, hev (hbi i t ht)]
    exact hX
  · -- the invariant, through `Lifting.Exact`
    exact hex.inv_inv _ _ (by rw [stack_unstack]; exact h.invariant t ht) i

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
