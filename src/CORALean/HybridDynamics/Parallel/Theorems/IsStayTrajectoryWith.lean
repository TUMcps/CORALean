module

public import CORALean.HybridDynamics.Parallel.Definitions.FlowLaw
public import CORALean.HybridDynamics.Parallel.Operations.ProductWith
public import CORALean.HybridDynamics.Parallel.Theorems.Basic
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.MeasureTheory.SpecificCodomains.Pi

@[expose] public section

/-!
# A shared stay is a stay of the product

For any flow with `FlowLaw`. At each instant of the stay the flow law supplies the product's input
and disturbance, in its input and disturbance sets, under which every coordinate of the product's
right-hand side at the stack is the component's own; the integral of the stack is the stack of
the integrals, so the stack is a stay of the product with those. The invariant is the lifted
one, by `Lifting.mem_inv`. Nothing else of the product is read.

## Inputs
* `P` – parallel automaton
* `F` – product flow at each location tuple
* `U` – product input sets
* `W` – product disturbance sets
* `lift` – lifting
* `ℓ` – current locations
* `τ` – stay duration
* `x` – component trajectories
* `u` – component inputs
* `w` – component disturbances
* `g` – global input

## Hypotheses
* `hF` – the flow has the flow law
* `h` – shared stay of the components

## Conclusion
* the stacked stay is a trajectory of the product
-/

-- Authors:       Claude Sonnet 5.5, Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   18-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix ContSet Scalar MeasureTheory

variable {S G : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] [∀ n, ContSet (G n) (Vec ℝ n)]
variable {𝕋 : Type} [Scalar 𝕋] {k m : ℕ} {n : Fin k → ℕ} {L : Fin k → Type}


-- =======================================  MAIN THEOREM  ======================================= --

/-- A stay of every component, inputs as bound, is one stay of the product, whose state is the
stack, under some input and disturbance of the product. -/
theorem ParallelHybridAutomaton.IsStay.trajectoryWith [ExactScalar 𝕋]
    {P : ParallelHybridAutomaton S G k L 𝕋 n m} {F : (∀ i, L i) → LinearSys 𝕋 (∑ i, n i)}
    {U : ∀ ℓ, S (F ℓ).m} {W : ∀ ℓ, S (F ℓ).r} (hF : P.FlowLaw F U W)
    (lift : ParallelHybridAutomaton.Lifting S G n m) {ℓ : ∀ i, L i} {τ : ℝ}
    {x : ∀ i, ℝ → Vec ℝ (n i)} {u w} {g : ℝ → Vec ℝ m} (h : P.IsStay ℓ τ x u w g) : -- --- CONCL ---
    ∃ (g' : ℝ → Vec ℝ (F ℓ).m) (w' : ℝ → Vec ℝ (F ℓ).r),
      ((P.productWith lift F U W).loc ℓ).IsTrajectory τ (fun t => stack fun i => x i t)
        g' w' := by -- --- PROOF ---
  classical
  -- at each instant of the stay, the flow law's input and disturbance of the product
  have key : ∀ t, ∃ gw : Vec ℝ (F ℓ).m × Vec ℝ (F ℓ).r, t ∈ Set.Icc 0 τ →
      gw.1 ∈ construct (U ℓ) ∧ gw.2 ∈ construct (W ℓ) ∧ ∀ i a,
        (toRealMat (F ℓ).A *ᵥ stack (fun i => x i t) + toRealMat (F ℓ).B *ᵥ gw.1 +
          toRealVec (F ℓ).c + toRealMat (F ℓ).E *ᵥ gw.2) (finSigmaFinEquiv ⟨i, a⟩) =
        (toRealMat (P.sys ℓ i).A *ᵥ x i t + toRealMat (P.sys ℓ i).B *ᵥ u i t +
          toRealVec (P.sys ℓ i).c + toRealMat (P.sys ℓ i).E *ᵥ w i t) a := by
    intro t
    by_cases ht : t ∈ Set.Icc 0 τ
    · obtain ⟨g', w', h1, h2, h3⟩ := hF ℓ (fun i => x i t) (fun i => u i t) (fun i => w i t)
        (g t) (fun i j => h.bound i j t ht) (fun i => h.input i t ht) (fun i => h.dist i t ht)
      exact ⟨(g', w'), fun _ => ⟨h1, h2, h3⟩⟩
    · exact ⟨(0, 0), fun h' => absurd h' ht⟩
  choose gw hgw using key
  -- the product's right-hand side along the stack is the stack of the components' own
  set f : ∀ i, ℝ → Vec ℝ (n i) := fun i t => toRealMat (P.sys ℓ i).A *ᵥ x i t +
    toRealMat (P.sys ℓ i).B *ᵥ u i t + toRealVec (P.sys ℓ i).c + toRealMat (P.sys ℓ i).E *ᵥ w i t
  have hstack : ∀ t ∈ Set.Icc 0 τ, toRealMat (F ℓ).A *ᵥ stack (fun i => x i t) +
      toRealMat (F ℓ).B *ᵥ (gw t).1 + toRealVec (F ℓ).c + toRealMat (F ℓ).E *ᵥ (gw t).2 =
      stack fun i => f i t := fun t ht => funext fun p => by
    obtain ⟨⟨i, a⟩, rfl⟩ := finSigmaFinEquiv.surjective p
    rw [stack_apply]
    exact (hgw t ht).2.2 i a
  -- the stack of the components' integrands, measurable and integrable coordinate by coordinate
  have hsm : AEStronglyMeasurable (fun t => stack fun i => f i t)
      (volume.restrict (Set.Icc 0 τ)) :=
    (aemeasurable_pi_iff.mpr fun p => ((h.meas (finSigmaFinEquiv.symm p).1).aemeasurable.eval
      (finSigmaFinEquiv.symm p).2)).aestronglyMeasurable
  have hsi : ∀ t ∈ Set.Icc 0 τ, IntervalIntegrable (fun s => stack fun i => f i s) volume 0 t :=
    fun t ht => ⟨Integrable.of_eval fun p => (h.integrable (finSigmaFinEquiv.symm p).1 t ht).1.eval
      (finSigmaFinEquiv.symm p).2, Integrable.of_eval fun p =>
        (h.integrable (finSigmaFinEquiv.symm p).1 t ht).2.eval (finSigmaFinEquiv.symm p).2⟩
  have hwin : ∀ t ∈ Set.Icc 0 τ, Set.uIcc 0 t ⊆ Set.Icc 0 τ := fun t ht =>
    Set.OrdConnected.uIcc_subset inferInstance (Set.left_mem_Icc.2 h.nonneg) ht
  refine ⟨fun t => (gw t).1, fun t => (gw t).2, h.nonneg, fun t ht => (hgw t ht).1,
    fun t ht => (hgw t ht).2.1, hsm.congr (ae_restrict_of_forall_mem measurableSet_Icc
      fun t ht => (hstack t ht).symm), fun t ht => ?_, continuousOn_pi.mpr fun p =>
        (continuous_apply _).comp_continuousOn (h.cont _), fun t ht => ?_, fun t ht => ?_⟩
  · exact (intervalIntegrable_congr fun s hs =>
      (hstack s (hwin t ht (Set.uIoc_subset_uIcc hs))).symm).mp (hsi t ht)
  · -- coordinate `⟨i, a⟩` of the stack's integral equation is component `i`'s, coordinate `a`
    show stack (fun i => x i t) = stack (fun i => x i 0) + ∫ s in (0:ℝ)..t,
      (toRealMat (F ℓ).A *ᵥ stack (fun i => x i s) + toRealMat (F ℓ).B *ᵥ (gw s).1 +
        toRealVec (F ℓ).c + toRealMat (F ℓ).E *ᵥ (gw s).2)
    rw [intervalIntegral.integral_congr fun s hs => hstack s (hwin t ht hs)]
    have hev : ∀ {N : ℕ} {g : ℝ → Vec ℝ N}, IntervalIntegrable g volume 0 t → ∀ q : Fin N,
        (∫ s in (0:ℝ)..t, g s) q = ∫ s in (0:ℝ)..t, g s q := fun {N} {_} hg q =>
      ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin N => ℝ) q).intervalIntegral_comp_comm
        hg).symm
    funext p
    obtain ⟨⟨i, a⟩, rfl⟩ := finSigmaFinEquiv.surjective p
    rw [Pi.add_apply, stack_apply, stack_apply, hev (hsi t ht)]
    simp only [stack_apply]
    rw [h.flow i t ht, Pi.add_apply, hev (h.integrable i t ht)]
  · -- the invariant, lifted
    exact lift.mem_inv _ (fun i => x i t) fun i => h.invariant i t ht

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
