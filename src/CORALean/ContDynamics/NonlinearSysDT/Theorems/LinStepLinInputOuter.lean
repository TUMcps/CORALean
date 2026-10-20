module

public import CORALean.ContDynamics.NonlinearSysDT.Operations.LinInput
public import CORALean.ContSet.Interval.Float.Theorems.MemPoint

@[expose] public section

/-!
# The step's widened input holds every input the field can demand

`NonlinearSys.linInput_outer` for a `LinStep`, in its scalar `𝕋`: wherever the state is
in the step's region and the input in `U`, `f(x,u) - A x` lies in `linInput`. The
three summands are the constant `c`, `B(u - u✱)` and the abstraction error; the
`A x✱` terms cancel against the constant `c` encloses.

## Inputs
* `sys` – system
* `U` – input set
* `step` – linearization step
* `x` – state
* `u` – admissible input

## Hypotheses
* `hx` – state in the step's region
* `hu` – input in the input set

## Conclusion
* the field less its linear part lies in the input set
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   03-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix ContSet Plus Mtimes CORALean.Float OfInterval

variable {n m : ℕ} {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]
variable [∀ n, Plus (S n) (Vec ℝ n)] [Mtimes (Mat 𝕋) S] [OfInterval S 𝕋]


-- =======================================  MAIN THEOREM  ======================================= --

/-- `f(x,u) - A x` lies in `linInput` wherever the step's certificate holds. -/
theorem NonlinearSysDT.LinStep.linInput_outer {sys : NonlinearSysDT n m} {U : S m}
    (step : sys.LinStep 𝕋 U) {x : Vec ℝ n} {u : Vec ℝ m} (hx : x ∈ step.R)
    (hu : u ∈ construct U) :
    sys.f x u - Scalar.toRealMat step.A *ᵥ x ∈ construct step.linInput := by -- --- PROOF ---
  -- the real readings of the step's data
  set A := Scalar.toRealMat step.A
  set B := Scalar.toRealMat step.B
  set us := Scalar.toRealVec step.us
  set xs := Scalar.toRealVec step.xs
  have hsplit : sys.f x u - A *ᵥ x
      = ((sys.f xs us - A *ᵥ xs) + B *ᵥ (u - us))
        + (sys.f x u - (sys.f xs us + A *ᵥ (x - xs) + B *ᵥ (u - us))) := by
    simp only [Matrix.mulVec_sub]
    abel
  -- `-u✱` as the point box's real reading, rounding-free by `toReal_neg`
  have hneg : -us = Scalar.toRealVec (-step.us) := by
    funext i
    simp only [us, Scalar.toRealVec_apply, Pi.neg_apply]
    exact (SoundFloatArithmetic.toReal_neg _).symm
  have hshift : u - us ∈ construct (U ⊞ ofInterval (Interval.point
      (-step.us))) := by
    rw [sub_eq_add_neg, hneg]
    exact plus_outer _ _ (Set.add_mem_add hu
      (ofInterval_outer _ (Interval.mem_point (-step.us))))
  -- each summand lies in its own part of `linInput`
  rw [hsplit]
  exact plus_outer _ _ (Set.add_mem_add
    (plus_outer _ _ (Set.add_mem_add
      (ofInterval_outer _ step.c_mem)
      (mtimes_outer (𝕄 := Mat 𝕋) step.B _ (Set.mem_biUnion rfl (Set.mem_image_of_mem _ hshift)))))
    (step.cert.encloses x hx u hu))

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
