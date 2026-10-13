import CORALean.ContDynamics.NonlinearSys.Definitions.AbstractionError
import CORALean.ContDynamics.NonlinearSys.Operations.LinInput
import CORALean.ContSet.Interval.Real.Operations.Point
import CORALean.ContSet.Interval.Real.Theorems.MemPoint

/-!
# The widened input set holds every input the field can demand

The set-level heart of conservative linearization, and the only place the
certificate is used: wherever the state is in `R` and the input in `U`, the
quantity `f(x,u) - A x` — what the linearized system has to be fed to follow
the nonlinear one — lies in `linInput`.

No time appears, which is the point: the statement is about one state and one
input, so how long a trajectory is asked to stay in `R` is the caller's choice
rather than this theorem's.

The identity doing the work is
`f(x,u) - A x = (f(x✱,u✱) - A x✱) + B(u - u✱) + L(x,u)`, where the three
summands are exactly the three parts `linInput` is built from and the `A x✱`
terms cancel.
-/

-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   04-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix Pointwise ContSet Plus Mtimes Real.OfInterval

variable {n m : ℕ}
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]
variable [∀ n, Plus (S n) (Vec ℝ n)] [Mtimes (Mat ℝ) S] [Real.OfInterval S]


-- =======================================  MAIN THEOREM  ======================================= --

/-- The remainder of the split lies in `linInput` wherever the certificate holds. -/
theorem linInput_outer {f : Vec ℝ n → Vec ℝ m → Vec ℝ n} {A : Mat ℝ n n}
    {B : Mat ℝ n m} {xs : Vec ℝ n} {us : Vec ℝ m} {R : Set (Vec ℝ n)}
    {U : S m} {L : S n} (cert : AbstractionError f A B xs us R (construct U) L)
    {x : Vec ℝ n} {u : Vec ℝ m} (hx : x ∈ R) (hu : u ∈ construct U) :
    f x u - A *ᵥ x ∈ construct (linInput f A B xs us U L) := by -- --- PROOF ---
  have hsplit : f x u - A *ᵥ x
      = ((f xs us - A *ᵥ xs) + B *ᵥ (u - us))
        + (f x u - (f xs us + A *ᵥ (x - xs) + B *ᵥ (u - us))) := by
    simp only [Matrix.mulVec_sub]
    abel
  have hshift : u - us ∈ construct (U ⊞ ofInterval (Real.Interval.point (-us))) := by
    rw [sub_eq_add_neg]
    exact plus_outer _ _ (Set.add_mem_add hu (ofInterval_outer _ (Real.Interval.mem_point _)))
  rw [hsplit]
  exact plus_outer _ _ (Set.add_mem_add
    (plus_outer _ _ (Set.add_mem_add
      (ofInterval_outer _ (Real.Interval.mem_point _))
      (mtimes_outer B _ (Set.mem_biUnion rfl (Set.mem_image_of_mem _ hshift)))))
    (cert.encloses x hx u hu))

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
