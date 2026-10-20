module

public import CORALean.ContSet.Zonotope.Real.Operations.ObserveDescriptorCurrent
public import CORALean.ContSet.Zonotope.Real.Operations.IntersectDescriptor

@[expose] public section

/-!
# The current-estimation-type observer is the set-membership estimator

[1, Thm. 7]: the zonotope `⟨p̃₊(Ĝ), H̃₊(Ĝ)⟩` of the current-estimation-type observer Eq. 39 of [1,
Thm. 7] is the intersection zonotope `⟨p̂₊(Λ), Ĥ₊(Λ)⟩` of Eq. 7 of [1, Thm. 1] at `Λ = Ĝ`, as sets.
The centers are the same expression, and the generators agree up to the sign of the last two blocks,
`-(I - ĜC)NF` and `-ĜF` against `(I - ĜC)NF` and `ΛF`, which "can be removed by definition of the
zonotope": flipping the sign of a coefficient that ranges over `[-1, 1]` changes nothing.

## Inputs
* `T` – decoupling matrix
* `N` – measurement decoupling matrix
* `Ghat` – observer gain
* `A` – state matrix
* `B` – input matrix
* `D` – disturbance matrix
* `C` – output matrix
* `F` – noise matrix
* `u` – control input
* `y_plus` – next output
* `X` – state zonotope

## Hypotheses
* none

## Conclusion
* the observer zonotope equals the intersection zonotope

## References

* [1] Y. Wang, V. Puig and G. Cembrano. "Set-membership approach and Kalman observer based on
      zonotopes for discrete-time descriptor systems". Automatica, 93:435-443, 2018.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {n nu nw ny nv : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zonotope.observeDescriptorCurrent_construct (T : Mat ℝ n n) (N Ghat : Mat ℝ n ny)
    (A : Mat ℝ n n) (B : Mat ℝ n nu) (D : Mat ℝ n nw) (C : Mat ℝ ny n) (F : Mat ℝ ny nv)
    (u : Vec ℝ nu) (y_plus : Vec ℝ ny) (X : Zonotope (Vec ℝ n)) : -- --- CONCL ---
    (X.observeDescriptorCurrent T N Ghat A B D C F u y_plus).construct =
      (X.intersectDescriptor T N Ghat A B D C F u y_plus).construct := by -- --- PROOF ---
  -- the sign pattern of the four blocks
  let σ : Fin (X.h + nw + nv + nv) → ℝ :=
    Fin.append (Fin.append (Fin.append (fun _ => 1) (fun _ => 1)) (fun _ => -1)) (fun _ => -1)
  have hσ : ∀ j, σ j * σ j = 1 := fun j => by
    refine Fin.addCases (fun j => Fin.addCases (fun j => Fin.addCases (fun j => ?_)
      (fun j => ?_) j) (fun j => ?_) j) (fun j => ?_) j <;> simp [σ]
  have hσa : ∀ j, |σ j| = 1 := fun j => by
    refine Fin.addCases (fun j => Fin.addCases (fun j => Fin.addCases (fun j => ?_)
      (fun j => ?_) j) (fun j => ?_) j) (fun j => ?_) j <;> simp [σ]
  have hG : ∀ j : Fin (X.h + nw + nv + nv),
      (X.observeDescriptorCurrent T N Ghat A B D C F u y_plus).G j =
        σ j • (X.intersectDescriptor T N Ghat A B D C F u y_plus).G j := fun j => by
    refine Fin.addCases (fun j => Fin.addCases (fun j => Fin.addCases (fun j => ?_)
      (fun j => ?_) j) (fun j => ?_) j) (fun j => ?_) j <;>
      ext i <;> simp [σ, Zonotope.observeDescriptorCurrent, Zonotope.intersectDescriptor]
  -- a coefficient vector for one is the sign-flipped one for the other
  ext x
  constructor
  · rintro ⟨β, hβ, rfl⟩
    refine ⟨fun j => σ j * β j, fun j => by rw [abs_mul, hσa, one_mul]; exact hβ j, ?_⟩
    show _ = _ + ∑ j : Fin (X.h + nw + nv + nv), _
    refine congrArg _ (Finset.sum_congr rfl fun j _ => ?_)
    rw [hG j, smul_smul]
    congr 1
    exact mul_comm _ _
  · rintro ⟨β, hβ, rfl⟩
    refine ⟨fun j => σ j * β j, fun j => by rw [abs_mul, hσa, one_mul]; exact hβ j, ?_⟩
    show _ = _ + ∑ j : Fin (X.h + nw + nv + nv), _
    refine congrArg _ (Finset.sum_congr rfl fun j _ => ?_)
    rw [hG j, smul_smul]
    congr 1
    show β j = σ j * β j * σ j
    rw [mul_comm (σ j) (β j), mul_assoc, hσ j, mul_one]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
