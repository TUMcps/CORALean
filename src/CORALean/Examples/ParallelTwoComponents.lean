import CORALean.ContSet.HPolytope.Real.API
import CORALean.ContSet.Interval.Real.Instances
import CORALean.HybridDynamics.Parallel.API

/-!
# Two components, one fed by the other, as a parallel hybrid automaton

Two one-dimensional components. Component `0` decays, `ẋ₀ = -x₀ + u₀`, with its input *bound*
to component `1`'s state, and has a transition: past `x₀ ≥ 1` it resets to `0`. Component `1`
integrates a global input, `ẋ₁ = u₁`, `u₁ ∈ [-1, 1]`. Invariants are boxes `x₀ ∈ [0, 2]` and
`x₁ ∈ [-1, 1]`.

The lifting is `boxLifting`: boxes for the input sets, `HPolytope` for invariants and guards, so
the product's invariant is the box `[0, 2] × [-1, 1]` as halfspaces and the lifted guard
`x₀ ≥ 1` is free in `x₁`. The product's flow matrix is read off entrywise, and the box is a
product `Invariant`, so `ParallelHybridAutomaton.reachSet_subset_invariant` puts every reachable
tuple of the parallel automaton in it. The invariant proof is by hand: the flow half is the
location invariant sitting inside the box, the jump half is the reset landing in it.

`ExactScalar` is held at `ℝ` alone, so the example does not run at a float scalar: the product
cannot be assembled there, and no `#eval` of the flow matrix is possible (#40).
-/

-- Authors:       Tobias Ladner
-- Written:       01-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix ContSet

/-- `x ∈ [lo, hi]` as a slab, in one dimension. -/
def PTC.range (lo hi : ℝ) : HPolytope (Vec ℝ 1) :=
  HPolytope.slab (1 : Mat ℝ 1 1) ![lo] ![hi]

/-- Component `0`: decays under the input it is bound to, and resets to `0` past `1`. -/
def PTC.decay : HybridAutomaton ℐ𝒱 ℋ𝒫 Unit ℝ 1 where
  loc _ :=
    { inv := PTC.range 0 2
      dynamics := ⟨!![-1]⟩
      U := ⟨![0], ![0]⟩
      trans := [⟨HPolytope.ineqs !![-1] ![-1], !![0], 0, ()⟩] }

/-- Component `1`: integrates its global input. -/
def PTC.integrator : HybridAutomaton ℐ𝒱 ℋ𝒫 Unit ℝ 1 where
  loc _ :=
    { inv := PTC.range (-1) 1
      dynamics := ⟨!![0]⟩
      U := ⟨![-1], ![1]⟩
      trans := [] }

/-- Component `0`'s one input is component `1`'s state; component `1`'s is the global one. -/
def PTC.binds : ∀ _ : Fin 2, Fin 1 → InputSource 2 (fun _ => 1) 1 :=
  ![fun _ => .state 1 0, fun _ => .global 0]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The parallel automaton. -/
def PTC.parallel :
    ParallelHybridAutomaton ℐ𝒱 ℋ𝒫 2 (fun _ => Unit) ℝ (fun _ => 1) 1 where
  comp := ![PTC.decay, PTC.integrator]
  binds := PTC.binds

/-- The product, through `boxLifting`: a single automaton in the stacked space. -/
def PTC.product : HybridAutomaton ℐ𝒱 ℋ𝒫 (∀ _ : Fin 2, Unit) ℝ (∑ _ : Fin 2, 1) :=
  PTC.parallel.product (ParallelHybridAutomaton.boxLifting PTC.binds)

/-- The box each component stays in. -/
def PTC.box : ∀ _ : Fin 2, Interval (Vec ℝ 1) := ![⟨![0], ![2]⟩, ⟨![-1], ![1]⟩]

/-- The product's invariant: the stacked box, the same at every location tuple. -/
def PTC.R : (∀ _ : Fin 2, Unit) → Interval (Vec ℝ (∑ _ : Fin 2, 1)) :=
  fun _ => Interval.stackProd PTC.box

/-- The product's flow matrix, entrywise: `-1` on component `0`, plus the `1` its input
takes from component `1`'s state; component `1` has no flow and a global input. -/
theorem PTC.flow_entries :
    let A := ((PTC.product.loc fun _ => ()).dynamics.A)
    A (finSigmaFinEquiv ⟨0, 0⟩) (finSigmaFinEquiv ⟨0, 0⟩) = -1 ∧
    A (finSigmaFinEquiv ⟨0, 0⟩) (finSigmaFinEquiv ⟨1, 0⟩) = 1 ∧
    A (finSigmaFinEquiv ⟨1, 0⟩) (finSigmaFinEquiv ⟨0, 0⟩) = 0 ∧
    A (finSigmaFinEquiv ⟨1, 0⟩) (finSigmaFinEquiv ⟨1, 0⟩) = 0 := by
  intro A
  simp [A, PTC.product, ParallelHybridAutomaton.product, ParallelHybridAutomaton.locationProduct,
    ParallelHybridAutomaton.mergeFlows, PTC.parallel, PTC.decay, PTC.integrator,
    PTC.binds]

/-- A slab is inside the box of the same bounds. -/
theorem PTC.range_subset (lo hi : ℝ) {v : Vec ℝ 1} (hv : v ∈ (PTC.range lo hi).construct) :
    v ∈ (⟨![lo], ![hi]⟩ : Interval (Vec ℝ 1)).construct := by -- --- PROOF ---
  have h := HPolytope.mem_slab_iff.mp hv
  intro j
  rw [show j = 0 from Subsingleton.elim j 0]
  obtain ⟨h1, h2⟩ := h 0
  simp only [Matrix.one_mulVec] at h1 h2
  exact ⟨h1, h2⟩

/-- The box is an inductive invariant of the product. -/
theorem PTC.invariant : PTC.product.Invariant PTC.R where
  flow {ℓ τ x u} h h₀ {t} ht := by
    -- in the location, so in each component's invariant, so in each component's box
    have hx := h.invariant t ht
    change x t ∈ (HPolytope.stackProd fun i => ((PTC.parallel.comp i).loc (ℓ i)).inv).construct
      at hx
    rw [HPolytope.stackProd_exact] at hx
    change x t ∈ (Interval.stackProd PTC.box).construct
    rw [Interval.stackProd_exact]
    intro i
    fin_cases i
    · exact PTC.range_subset 0 2 (hx 0)
    · exact PTC.range_subset (-1) 1 (hx 1)
  jump {ℓ e} hmem {z} hz hguard := by
    simp [PTC.product, ParallelHybridAutomaton.product,
      ParallelHybridAutomaton.locationProduct, ParallelHybridAutomaton.mergeTransitionSets,
      List.mem_flatMap, PTC.parallel, PTC.integrator] at hmem
    obtain ⟨a, ha, rfl⟩ := hmem
    -- the one transition of component `0`
    simp only [PTC.decay, List.mem_singleton] at ha
    subst ha
    -- a point of the product space is the stack of its blocks, and the reset acts on block `0`
    obtain ⟨x, rfl⟩ : ∃ x, z = stack x := ⟨unstack z, (stack_unstack z).symm⟩
    rw [ParallelHybridAutomaton.liftTransition_reset]
    change stack x ∈ (Interval.stackProd PTC.box).construct at hz
    rw [Interval.stackProd_exact] at hz
    simp only [Set.mem_setOf_eq, unstack_stack] at hz
    change _ ∈ (Interval.stackProd PTC.box).construct
    rw [Interval.stackProd_exact]
    simp only [Set.mem_setOf_eq, unstack_stack]
    intro i
    fin_cases i
    · -- the reset sends the position to `0`, which is in `[0, 2]`
      show Function.update x 0 _ 0 ∈ (PTC.box 0).construct
      rw [Function.update_self]
      intro j
      rw [show j = 0 from Subsingleton.elim j 0]
      simp [Transition.reset, PTC.box, Scalar.toRealMat, Scalar.toRealVec]
      exact (by norm_num : (0 : ℝ) ≤ 2)
    · simpa [Function.update_of_ne] using hz 1

/-- A parallel run is a run of the product, stacked. -/
theorem PTC.run_toProduct {ℓ ℓ' : ∀ _ : Fin 2, Unit} {x y : ∀ _ : Fin 2, Vec ℝ 1}
    (run : PTC.parallel.Run ℓ x ℓ' y) : PTC.product.Run ℓ (stack x) ℓ' (stack y) :=
  ParallelHybridAutomaton.Run.toProduct (P := PTC.parallel)
    (ParallelHybridAutomaton.boxLifting PTC.binds) run

/-- Every tuple of states the parallel automaton reaches from the box, stacked, is in the box. -/
theorem PTC.reachSet_subset (ℓ₀ ℓ : ∀ _ : Fin 2, Unit) :
    stack '' PTC.parallel.reachSet PTC.box ℓ₀ ℓ ⊆ construct (PTC.R ℓ) := by -- --- PROOF ---
  refine ParallelHybridAutomaton.reachSet_subset_invariant
    (P := PTC.parallel) (lift := ParallelHybridAutomaton.boxLifting PTC.binds)
    PTC.invariant (fun x hx => ?_) ℓ
  -- a stack of points of the boxes is in the stacked box
  change stack x ∈ (Interval.stackProd PTC.box).construct
  rw [Interval.stackProd_exact]
  simp only [Set.mem_setOf_eq, unstack_stack]
  exact hx

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
