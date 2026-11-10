module

public import CORALean.ContDynamics.LinParamSysDT.Operations.Reach

@[expose] public section

/-!
# One step of `LinParamSysDT.reach` encloses one step of the dynamics

`LinearSysDT.reach_one_outer`'s statement, at a matrix `A` drawn from
`toSet sys.A` instead of the one `toRealMat sys.A` a point matrix denotes.
`Set.mem_biUnion hA` replaces the singleton's `Set.mem_biUnion rfl`: `hA` is a
real membership proof, doing what `rfl` only stood in for there.

## Inputs
* `sys` – system
* `o` – maximum zonotope order
* `R` – initial set
* `U` – input set
* `A` – system matrix member
* `x` – state
* `u` – input value

## Hypotheses
* `ho` – order positive
* `hA` – `A` lies in the matrix set
* `hx` – `x` lies in `R`
* `hu` – `u` lies in `U`

## Conclusion
* the one-step successor lies in the one-step reachable set
-/

-- Authors:       Claude Opus 5
-- Written:       06-September-2026
-- Last update:   30-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix Pointwise ContSetLike Plus Reduce Mtimes

variable {n : ℕ} {𝕄 : ℕ → ℕ → Type} [∀ m n, ContSetLike (𝕄 m n) (Mat ℝ m n)]
variable {S : ℕ → Type} [∀ n, ContSetLike (S n) (Vec ℝ n)]
variable [∀ n, Plus (S n) (Vec ℝ n)] [∀ n, Reduce (S n) (Vec ℝ n)] [Mtimes 𝕄 S]


-- =======================================  MAIN THEOREM  ======================================= --

theorem LinParamSysDT.reach_one_outer (sys : LinParamSysDT 𝕄 n) {o : ℕ} (ho : 0 < o) (R U : S n)
    {A : Mat ℝ n n} (hA : A ∈ toSet sys.A) {x u : Vec ℝ n}
    (hx : x ∈ toSet R) (hu : u ∈ toSet U) :
    A *ᵥ x + u ∈ toSet (sys.reach ⟨R, U, 0, 1⟩ ⟨o, ho⟩) :=
  reduce_outer _ _ (plus_outer _ _
    (Set.add_mem_add
      (mtimes_outer sys.A _ (Set.mem_biUnion hA (Set.mem_image_of_mem _ hx)))
      hu))

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
