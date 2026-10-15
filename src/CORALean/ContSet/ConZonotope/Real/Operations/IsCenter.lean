module

public import CORALean.ContSet.ConZonotope.Real.Operations.MemDomainIff
public import CORALean.ContSet.ConZonotope.Real.Operations.OfMat
public import CORALean.ContSet.ConZonotope.Real.Operations.NullPolytope
public import CORALean.ContSet.HPolytope.Real.Operations.IsLPCenter

@[expose] public section

/-!
# `ConZonotope.IsCenter`

CORA's `@conZonotope/center` of `conZonotope(c, G, A, b)` as a specification: a linear-program
optimum cannot be computed here, so `x` is a center when a branch of the method returns it.

* `A` empty: the center `c`.
* Otherwise `c + G β` for `β` a Chebyshev center of `{β : |β| ≤ 1, A β = b}`: the program of
  `HPolytope.IsLPCenter` on the domain (the set not full-dimensional); or in null-space coordinates,
  `N = null(A)`, `x0 = pinv(A) b` and `ConZonotope.nullPolytope` (full-dimensional); or the unique
  solution, for a trivial kernel.

Which branch applies depends on `isFullDim(cZ)`, not decided here: any branch's condition suffices.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {α : Type} [AddCommGroup α] [Module ℝ α] {q h : ℕ}


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
        ∧ (ConZonotope.nullPolytope N x0).IsLPCenter y
        ∧ x = c + ∑ j, (x0 + N *ᵥ y) j • G j) ∨
     (∃ β : Vec ℝ h, (∀ β' : Vec ℝ h, A *ᵥ β' = 0 → β' = 0) ∧ A *ᵥ β = b
        ∧ (∀ j, |β j| ≤ 1) ∧ x = c + ∑ j, β j • G j)))


end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
