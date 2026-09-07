import CORALean.ContDynamics.LinearSysDT.Operations

/-!
# One step of `LinearSysDT.reach` encloses one step of the dynamics

`reach_outer`'s induction step on its own: a state in `R` and an input in `U`
land inside what `reach` returns after one step. Stated separately because a
closed loop needs exactly this and cannot use `reach_outer` — there the input
set is fixed for the whole run, while a controller produces a fresh one at every
step, so each step is a `reach ... 1` at a set the previous step computed.

Only `plus_outer`, `mtimes_outer` and `reduce_outer` are used, so it asks for no
more than `reach` itself does.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix Pointwise ContSet Scalar Plus Reduce Mtimes

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]
variable [∀ n, Plus (S n) (Vec ℝ n)] [∀ n, Reduce (S n) (Vec ℝ n)] [Mtimes (Mat 𝕋) S]


-- =======================================  MAIN THEOREM  ======================================= --

theorem LinearSysDT.reach_one_outer (sys : LinearSysDT 𝕋 n) {o : ℕ} (ho : 0 < o) (R U : S n)
    {x u : Vec ℝ n} (hx : x ∈ construct R) (hu : u ∈ construct U) :
    toRealMat sys.A *ᵥ x + u ∈ construct (sys.reach o ho R U 1) :=
  reduce_outer _ _ (plus_outer _ _
    (Set.add_mem_add
      (mtimes_outer sys.A _ (Set.mem_biUnion rfl (Set.mem_image_of_mem _ hx)))
      hu))

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
