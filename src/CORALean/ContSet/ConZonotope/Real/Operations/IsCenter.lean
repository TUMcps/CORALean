module

public import CORALean.ContSet.ConZonotope.Real.Theorems.MemDomainIff
public import CORALean.ContSet.ConZonotope.Real.Operations.OfMat
public import CORALean.ContSet.HPolytope.Real.HPolytope
public import CORALean.ContSet.HPolytope.Real.Operations.IsLPCenter
public import CORALean.ContSet.HPolytope.Real.Operations.Ineqs
public import CORALean.ContSet.HPolytope.Real.Operations.RowLin

@[expose] public section

/-!
# `ConZonotope.IsCenter`

CORA's `@conZonotope/center` of `conZonotope(c, G, A, b)` as a specification: a linear-program
optimum cannot be computed here, so `x` is a center when a branch returns it (which applies depends
on `isFullDim(cZ)`, not decided here).

* `A` empty: the center `c`. * Otherwise `c + G β` for `β` a Chebyshev center of `{β : |β| ≤ 1, A β
= b}`: the program of `HPolytope.IsLPCenter` on the domain (the set not full-dimensional); or in
null-space coordinates, `N = null(A)`, `x0 = pinv(A) b` and `ConZonotope.aux_nullPolytope`
(full-dimensional); or the unique solution, for a trivial kernel.

## Inputs
* `c` – center
* `G` – generators
* `A` – constraint matrix
* `b` – constraint offset
* `x` – candidate center

## Output
* the point is a center of the constrained zonotope
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {α : Type} [AddCommGroup α] [Module ℝ α] {q h : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- `y ↦ x0 + N y` in `[-1, 1]^h`, as `2h` halfspaces over `y`. -/
def ConZonotope.aux_nullPolytope {k : ℕ} (N : Mat ℝ h k) (x0 : Vec ℝ h) : HPolytope (Vec ℝ k) :=
  HPolytope.ineqs (Fin.append N (-N)) (Fin.append (fun i => 1 - x0 i) (fun i => 1 + x0 i))


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `x` is what a branch of `center(cZ)` returns for `cZ = conZonotope(c, G, A, b)`. -/
def ConZonotope.IsCenter (c : α) (G : Fin h → α) (A : Mat ℝ q h) (b : Vec ℝ q) (x : α) : Prop :=
  (q = 0 ∧ x = c) ∨
  (0 < q ∧
    ((∃ β : Vec ℝ h, (ConZonotope.ofMat c G A b).domain.IsLPCenter β
        ∧ x = c + ∑ j, β j • G j) ∨
     (∃ (k : ℕ) (N : Mat ℝ h k) (x0 : Vec ℝ h) (y : Vec ℝ k),
        A *ᵥ x0 = b ∧ A * N = 0 ∧ Nᵀ * N = 1 ∧ Nᵀ *ᵥ x0 = 0
        ∧ (∀ β : Vec ℝ h, A *ᵥ β = 0 → ∃ y : Vec ℝ k, β = N *ᵥ y) ∧ 0 < k
        ∧ (ConZonotope.aux_nullPolytope N x0).IsLPCenter y
        ∧ x = c + ∑ j, (x0 + N *ᵥ y) j • G j) ∨
     (∃ β : Vec ℝ h, (∀ β' : Vec ℝ h, A *ᵥ β' = 0 → β' = 0) ∧ A *ᵥ β = b
        ∧ (∀ j, |β j| ≤ 1) ∧ x = c + ∑ j, β j • G j)))


end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
