module

public import CORALean.ContDynamics.NonlinParamSys.Operations.Linearize
public import CORALean.ContSet.Interval.Real.Theorems.ExistsCoeffOfMem

@[expose] public section

/-!
# The constant term's zonotope holds the dynamics at every parameter of the box

For a system affine in `p` (`hAff`: the split `f = f_0 + ∑ pᵢ fᵢ` that `linearize` makes from
`f(·, ·, 0)` and the unit vectors), `f(x*, u*, p)` lies in `zf` for every `p` in the box: `p` is
the centre plus `βᵢ rᵢ` and `f` is affine in it. The set of values is the image of a box under an
affine map, a zonotope, so `zf` is not only an enclosure of it; the statement is the inclusion.
Without `hAff` it fails (`linearize_f_counterexample`).
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       09-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real

variable {n m q : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem NonlinParamSys.linearize_f_mem (sys : NonlinParamSys n m q)
    (hAff : ∀ x u p, sys.f x u p
      = sys.f x u 0 + ∑ i, p i • (sys.f x u (Pi.single i 1) - sys.f x u 0))
    (xs : Vec ℝ n) (us : Vec ℝ m) (I : Interval (Vec ℝ q)) {p : Vec ℝ q}
    (hp : p ∈ I.construct) :
    sys.f xs us p ∈ (sys.linearize xs us I).zf.construct := by -- --- PROOF ---
  obtain ⟨β, hβ, hpi⟩ := I.exists_coeff_of_mem hp
  refine ⟨β, hβ, ?_⟩
  -- each summand splits into the centre's and the generator's
  have hsum : ∀ i, p i • (sys.f xs us (Pi.single i 1) - sys.f xs us 0)
      = I.center i • (sys.f xs us (Pi.single i 1) - sys.f xs us 0)
        + β i • (I.radius i • (sys.f xs us (Pi.single i 1) - sys.f xs us 0)) := fun i => by
    rw [hpi i, add_smul, mul_smul]
  rw [hAff xs us p]
  simp only [NonlinParamSys.linearize, Finset.sum_congr rfl fun i _ => hsum i,
    Finset.sum_add_distrib]
  abel

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
