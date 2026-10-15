module

public import CORALean.HybridDynamics.Parallel.Definitions.FlowLaw
public import CORALean.HybridDynamics.Parallel.Operations.ProductWith
public import CORALean.HybridDynamics.Parallel.Theorems.Basic
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Prod
public import Mathlib.Analysis.InnerProductSpace.Basic

@[expose] public section

/-!
# A shared stay is a stay of the product

For any flow with `FlowLaw`. At each instant of the stay the flow law supplies the product's input
and disturbance, in its input and disturbance sets, under which every coordinate of the product's
right-hand side at the stack is the component's own; the derivative of the stack is the stack of
the derivatives, so the stack is a stay of the product with those. The invariant is the lifted
one, by `Lifting.mem_inv`. Nothing else of the product is read.
-/

-- Authors:       Claude Sonnet 5.5, Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   14-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix ContSet Scalar

variable {S G : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] [∀ n, ContSet (G n) (Vec ℝ n)]
variable {𝕋 : Type} [Scalar 𝕋] {k m : ℕ} {n : Fin k → ℕ} {L : Fin k → Type}


-- =======================================  MAIN THEOREM  ======================================= --

/-- A stay of every component, inputs as bound, is one stay of the product, whose state is the
stack, under some input and disturbance of the product. -/
theorem ParallelHybridAutomaton.IsStay.trajectoryWith [ExactScalar 𝕋]
    {P : ParallelHybridAutomaton S G k L 𝕋 n m} {F : (∀ i, L i) → LinearSys 𝕋 (∑ i, n i)}
    {U : ∀ ℓ, S (F ℓ).m} {W : ∀ ℓ, S (F ℓ).r} (hF : P.FlowLaw F U W)
    (lift : ParallelHybridAutomaton.Lifting S G n m) {ℓ : ∀ i, L i} {τ : ℝ}
    {x : ∀ i, ℝ → Vec ℝ (n i)} {u w} {g : ℝ → Vec ℝ m} (h : P.IsStay ℓ τ x u w g) :
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
  refine ⟨fun t => (gw t).1, fun t => (gw t).2, h.nonneg, fun t ht => (hgw t ht).1,
    fun t ht => (hgw t ht).2.1, fun t ht => ?_, fun t ht => ?_⟩
  · -- the stack is differentiable coordinate by coordinate, each coordinate a component's
    rw [hasDerivWithinAt_pi]
    intro p
    obtain ⟨⟨i, j⟩, rfl⟩ := finSigmaFinEquiv.surjective p
    simp only [stack_apply]
    exact (hasDerivWithinAt_pi.mp (h.flow i t ht) j).congr_deriv ((hgw t ht).2.2 i j).symm
  · -- the invariant, lifted
    exact lift.mem_inv _ (fun i => x i t) fun i => h.invariant i t ht

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
