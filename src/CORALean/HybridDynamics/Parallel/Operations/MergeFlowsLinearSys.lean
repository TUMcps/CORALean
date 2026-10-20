module

public import CORALean.HybridDynamics.Definitions.ResolveSource
public import CORALean.ContDynamics.LinearSys.LinearSys
public import Mathlib.Algebra.BigOperators.Fin

@[expose] public section

/-!
# `mergeFlows` at the components' full equations

CORA's `aux_mergeFlowsLinearSys` [1] over any commutative ring, its sums exact: the components'
full linear equations as one system of dimension `∑ i, n i`, input `j` of component `i` bound by
`binds i j` to a global input or to an output `s` of a component `c`. `Amerged` adds
`B(:,j) C_c(s,:)` to the block-diagonal `Aᵢ`, `Bmerged`, `cMerged` and `Fmerged` follow.
Two departures, in `Fmerged` alone: CORA assigns each term where this adds, and numbers the noise
blocks by the disturbance counts where this stacks them. The flow theorem `mergeFlowsLinearSys_flow`
is for noise-free bound outputs. It is the product's flow (`locationProduct`).

## Inputs
* `sys` – linear system of each component
* `binds` – input bindings

## Output
* merged linear system of the product

## References

* [1] `hybridDynamics/@parallelHybridAutomaton/mergeFlows.m`
-/

-- Authors:       Claude Opus 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix

variable {k m : ℕ} {n : Fin k → ℕ} {𝕋 : Type} [CommRing 𝕋]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `sys_merged = aux_mergeFlowsLinearSys(pHA, flowList)`. -/
def ParallelHybridAutomaton.mergeFlowsLinearSys (sys : ∀ i, LinearSys 𝕋 (n i))
    (binds : ∀ i, Fin (sys i).m → ResolveSource k (fun i => (sys i).q) m) :
    LinearSys 𝕋 (∑ i, n i) :=
  let Amerged : Mat 𝕋 (∑ i, n i) (∑ i, n i) :=                     -- A, plus B(:,j) C(s,:)
    Matrix.reindex finSigmaFinEquiv finSigmaFinEquiv <| Matrix.of fun p q =>
      (if h : p.1 = q.1 then (sys p.1).A p.2 (Fin.cast (congrArg n h.symm) q.2) else 0) +
      ∑ j, match binds p.1 j with
        | .global _ => 0
        | .output c s => if h : c = q.1 then (sys p.1).B p.2 j * (sys q.1).C (h ▸ s) q.2 else 0
  let Bmerged : Mat 𝕋 (∑ i, n i) m :=                              -- B(:,j), and B(:,j) D(s,:)
    Matrix.reindex finSigmaFinEquiv (Equiv.refl _) <| Matrix.of fun p a =>
      ∑ j, match binds p.1 j with
        | .global a' => if a' = a then (sys p.1).B p.2 j else 0
        | .output c s => (sys p.1).B p.2 j * ∑ j', match binds c j' with
            | .global a' => if a' = a then (sys c).D s j' else 0
            | .output _ _ => 0
  let cMerged : Vec 𝕋 (∑ i, n i) := fun r =>                       -- c, plus B(:,j) k(s)
    let p := finSigmaFinEquiv.symm r
    (sys p.1).c p.2 + ∑ j, match binds p.1 j with
      | .global _ => 0
      | .output c s => (sys p.1).B p.2 j * (sys c).k s
  let Emerged : Mat 𝕋 (∑ i, n i) (∑ i, (sys i).r) :=               -- E, block diagonal
    Matrix.reindex finSigmaFinEquiv finSigmaFinEquiv <| Matrix.of fun p q =>
      if h : p.1 = q.1 then (sys p.1).E p.2 (Fin.cast (by rw [h]) q.2) else 0
  let Fmerged : Mat 𝕋 (∑ i, n i) (∑ i, (sys i).s) :=               -- B(:,j) F(s,:)
    Matrix.reindex finSigmaFinEquiv finSigmaFinEquiv <| Matrix.of fun p q =>
      ∑ j, match binds p.1 j with
        | .global _ => 0
        | .output c s => if h : c = q.1 then (sys p.1).B p.2 j * (sys q.1).F (h ▸ s) q.2 else 0
  ⟨m, ∑ i, n i, ∑ i, (sys i).r, ∑ i, (sys i).s, Amerged, Bmerged, cMerged, 1, 0, 0, Emerged,
    Fmerged⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
