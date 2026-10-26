module

public import CORALean.HybridDynamics.Parallel.Theorems.IsStayTrajectoryWith
public import CORALean.HybridDynamics.Parallel.Theorems.StackUnstack
public import CORALean.HybridDynamics.Parallel.Theorems.Basic
public import CORALean.HybridDynamics.Parallel.Definitions.LiftingExact
public import CORALean.HybridDynamics.Parallel.Definitions.IsFlowLawConverse
public import CORALean.HybridDynamics.Parallel.Theorems.LiftTransitionReset

@[expose] public section

/-!
# Every run of the product is a parallel run

The converse of `IsRun.toProductWith`, for any flow with `IsFlowLawConverse`, by the product run's
recursion. A stay is `IsStay.aux_ofTrajectoryWith`; a jump of the product is a lifted transition of
some component `c`, whose guard comes back through `Lifting.IsExact` and whose reset is the update,
by `liftTransition_reset`, of the blocks of the stacked state. The conditions are those under which
the product loses nothing: `Lifting.IsExact` and the converse flow law, which for
`mergeFlowsLinearSys` asks `GlobalsDistinct` and nonempty input sets as well
(`mergeFlowsLinearSys_flowLawConverse`).

## Inputs
* `P` – parallel automaton
* `F` – product flow at each location tuple
* `U` – product input sets
* `W` – product disturbance sets
* `lift` – lifting
* `ℓ` – start locations
* `ℓ'` – end locations
* `z` – start state of the product
* `w` – end state of the product

## Hypotheses
* `hF` – the flow has the converse flow law
* `hex` – lifting is exact
* `run` – run of the product from `z` to `w`

## Conclusion
* the unstacked states are a parallel run
-/

-- Authors:       Claude Sonnet 5.5, Claude Opus 5.5
-- Written:       11-October-2026
-- Last update:   14-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix ContSet Scalar

variable {S G : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] [∀ n, ContSet (G n) (Vec ℝ n)]
variable {𝕋 : Type} [Scalar 𝕋] {k m : ℕ} {n : Fin k → ℕ} {L : Fin k → Type}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

section
open MeasureTheory

/-- A stay of the product at `ℓ` is a stay of the components, whose states are the blocks of the
product's state. -/
private theorem ParallelHybridAutomaton.IsStay.aux_ofTrajectoryWith [ExactScalar 𝕋]
    {P : ParallelHybridAutomaton S G k L 𝕋 n m} {F : (∀ i, L i) → LinearSys 𝕋 (∑ i, n i)}
    {U : ∀ ℓ, S (F ℓ).m} {W : ∀ ℓ, S (F ℓ).r} (hF : P.IsFlowLawConverse F U W)
    {lift : ParallelHybridAutomaton.Lifting S G n m} (hex : lift.IsExact) {ℓ : ∀ i, L i} {τ : ℝ}
    {X : ℝ → Vec ℝ (∑ i, n i)} {g' w'}
    (h : ((P.productWith lift F U W).loc ℓ).IsTrajectory τ X g' w') : -- --- CONCL ---
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
  · -- the invariant, through `Lifting.IsExact`
    exact hex.inv_inv _ _ (by rw [stack_unstack]; exact h.invariant t ht) i

end


-- =======================================  MAIN THEOREM  ======================================= --

/-- A run of the product is a run of the parallel automaton, on the blocks of its states. -/
theorem ParallelHybridAutomaton.IsRun.ofProductWith [ExactScalar 𝕋]
    {P : ParallelHybridAutomaton S G k L 𝕋 n m} {F : (∀ i, L i) → LinearSys 𝕋 (∑ i, n i)}
    {U : ∀ ℓ, S (F ℓ).m} {W : ∀ ℓ, S (F ℓ).r} (hF : P.IsFlowLawConverse F U W)
    {lift : ParallelHybridAutomaton.Lifting S G n m} (hex : lift.IsExact) {ℓ ℓ' : ∀ i, L i}
    {z w : Vec ℝ (∑ i, n i)} (run : (P.productWith lift F U W).IsRun ℓ z ℓ' w) : -- --- CONCL ---
    P.IsRun ℓ (unstack z) ℓ' (unstack w) := by -- --- PROOF ---
  induction run with
  | @flow ℓ₁ τ X g' w' h =>
    obtain ⟨x, u, w, g, hst, hx⟩ := ParallelHybridAutomaton.IsStay.aux_ofTrajectoryWith hF hex h
    have h0 : (fun i => x i 0) = unstack (X 0) := funext fun i => by rw [hx i]
    have hτ : (fun i => x i τ) = unstack (X τ) := funext fun i => by rw [hx i]
    rw [← h0, ← hτ]
    exact ParallelHybridAutomaton.IsRun.flow (P := P) hst
  | @jump ℓ₁ ℓ₂ τ X g' w' Y e h hmem hguard rest ih =>
    obtain ⟨x, u, w, g, hst, hx⟩ := ParallelHybridAutomaton.IsStay.aux_ofTrajectoryWith hF hex h
    have h0 : (fun i => x i 0) = unstack (X 0) := funext fun i => by rw [hx i]
    have hτ : (fun i => x i τ) = unstack (X τ) := funext fun i => by rw [hx i]
    -- the product's transition is a component's, lifted
    obtain ⟨c, -, e₀, he₀, rfl⟩ : ∃ c ∈ List.finRange k,
        ∃ e₀ ∈ ((P.comp c).loc (ℓ₁ c)).trans,
          ParallelHybridAutomaton.liftTransition lift ℓ₁ c e₀ = e := by
      obtain ⟨c, hc, he⟩ := List.mem_flatMap.mp hmem
      obtain ⟨e₀, he₀, rfl⟩ := List.mem_map.mp he
      exact ⟨c, hc, e₀, he₀, rfl⟩
    have hg : x c τ ∈ construct e₀.guard := by
      refine hex.guard_inv c e₀.guard (fun i => x i τ) ?_
      rw [hτ, stack_unstack]
      exact hguard
    have hr : (ParallelHybridAutomaton.liftTransition lift ℓ₁ c e₀).reset (X τ) =
        stack (Function.update (fun i => x i τ) c (e₀.reset (x c τ))) := by
      have := ParallelHybridAutomaton.liftTransition_reset lift ℓ₁ c e₀ (fun i => x i τ)
      rwa [show stack (fun i => x i τ) = X τ by rw [hτ, stack_unstack]] at this
    rw [hr, unstack_stack] at ih
    rw [← h0]
    exact ParallelHybridAutomaton.IsRun.jump (P := P) hst he₀ hg ih

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
