import CORALean.ContDynamics.LinParamSysDT.Operations

/-!
# One step of `LinParamSysDT.reach` encloses one step of the dynamics

`LinearSysDT.reach_one_outer`'s statement, at a matrix `A` drawn from
`construct sys.A` instead of the one `toRealMat sys.A` a point matrix denotes.
`Set.mem_biUnion hA` replaces the singleton's `Set.mem_biUnion rfl`: `hA` is a
real membership proof, doing what `rfl` only stood in for there.
-/

-- Authors:       Tobias Ladner
-- Written:       06-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix Pointwise ContSet Plus Reduce Mtimes

variable {n : ℕ} {𝕄 : ℕ → ℕ → Type} [∀ m n, ContSet (𝕄 m n) (Mat ℝ m n)]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]
variable [∀ n, Plus (S n) (Vec ℝ n)] [∀ n, Reduce (S n) (Vec ℝ n)] [Mtimes 𝕄 S]


-- =======================================  MAIN THEOREM  ======================================= --

theorem LinParamSysDT.reach_one_outer (sys : LinParamSysDT 𝕄 n) {o : ℕ} (ho : 0 < o) (R U : S n)
    {A : Mat ℝ n n} (hA : A ∈ construct sys.A) {x u : Vec ℝ n}
    (hx : x ∈ construct R) (hu : u ∈ construct U) :
    A *ᵥ x + u ∈ construct (sys.reach o ho R U 1) :=
  reduce_outer _ _ (plus_outer _ _
    (Set.add_mem_add
      (mtimes_outer sys.A _ (Set.mem_biUnion hA (Set.mem_image_of_mem _ hx)))
      hu))

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
