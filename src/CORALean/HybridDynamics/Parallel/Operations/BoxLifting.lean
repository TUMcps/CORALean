module

public import CORALean.HybridDynamics.Parallel.Theorems.IntervalStackProdExact
public import CORALean.HybridDynamics.Parallel.Theorems.HPolytopeStackProdExact
public import CORALean.HybridDynamics.Parallel.Theorems.Basic
public import CORALean.HybridDynamics.Parallel.Operations.Basic
public import CORALean.HybridDynamics.Parallel.Definitions.Lifting
public import CORALean.HybridDynamics.Parallel.Theorems.SelectGlobalMulVec
public import CORALean.ContSet.HPolytope.Real.Instances

@[expose] public section

/-!
# `boxLifting`: a `Lifting` at boxes and halfspace descriptions

The first concrete `Lifting`: inputs and disturbances in `Interval`, invariants and guards in
`HPolytope`.

* `inv` is `HPolytope.stackProd`, the Cartesian product of the components' invariants;
* `guard i g` is `HPolytope.comap (blockProj i) g`, constraining block `i` and free elsewhere,
  which no box can say;
* `input b` is the box of the global inputs: at `a`, the bounds of the first input `b` binds to
  `a` (`selectGlobal`), `[0, 0]` where none is;
* `dist` is `Interval.stackProd`, the product of the components' disturbance boxes.

`inv`, `guard` and `dist` are exact (`Theorems.IntervalStackProdExact`,
`Theorems.HPolytopeStackProdExact`); `input` is, where no global input feeds two inputs.
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   14-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real ContSet Matrix

variable {k m : ℕ} {n : Fin k → ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def ParallelHybridAutomaton.boxLifting :
    ParallelHybridAutomaton.Lifting (ℐ𝒱) (ℋ𝒫) n m where
  inv := HPolytope.stackProd
  guard i g := HPolytope.comap (blockProj i) g
  input b us := ⟨selectGlobal b *ᵥ stack fun i => (us i).inf,
    selectGlobal b *ᵥ stack fun i => (us i).sup⟩
  dist := Interval.stackProd
  mem_inv gs x hx := by
    -- the product is exactly the blocks' sets, and the blocks of a stack are what was stacked
    show stack x ∈ (HPolytope.stackProd gs).construct
    rw [HPolytope.stackProd_exact]
    intro i
    rw [unstack_stack]
    exact hx i
  mem_guard i g x hx := by
    -- the lifted guard asks of a point only that its block `i` be in `g`
    show stack x ∈ (HPolytope.comap (blockProj i) g).construct
    rw [HPolytope.comap_blockProj_exact]
    show unstack (stack x) i ∈ g.construct
    rw [unstack_stack]
    exact hx
  mem_input b us g hg hz := by
    -- at `a`, the bounds of the first input bound to `a`, which a point of its box meets
    intro a
    show (selectGlobal b *ᵥ _) a ≤ g a ∧ g a ≤ (selectGlobal b *ᵥ _) a
    rw [selectGlobal_mulVec, selectGlobal_mulVec]
    split_ifs with h
    · obtain ⟨v, hv, hva⟩ := hg (finSigmaFinEquiv.symm (Fin.find _ h)).1
      have hj : (us _).inf (finSigmaFinEquiv.symm (Fin.find _ h)).2 ≤
          v (finSigmaFinEquiv.symm (Fin.find _ h)).2 ∧
          v (finSigmaFinEquiv.symm (Fin.find _ h)).2 ≤
            (us _).sup (finSigmaFinEquiv.symm (Fin.find _ h)).2 := hv _
      rw [hva _ a (Fin.find_spec h)] at hj
      exact hj
    · -- no input reads `a`, so `g a = 0`
      rw [hz a fun i j hij => h ⟨finSigmaFinEquiv ⟨i, j⟩, by
        rw [show finSigmaFinEquiv.symm (finSigmaFinEquiv ⟨i, j⟩) = ⟨i, j⟩ from
          Equiv.symm_apply_apply _ _]
        exact hij⟩]
      exact ⟨le_rfl, le_rfl⟩
  mem_dist ws w hw := by
    -- as `mem_inv`, at the box of the stacked disturbances
    show stack w ∈ (Interval.stackProd ws).construct
    rw [Interval.stackProd_exact]
    intro i
    rw [unstack_stack]
    exact hw i

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
