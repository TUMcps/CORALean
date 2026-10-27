module

public import CORALean.ContDynamics.LinearSysDT.Definitions.BackReachSetRobustExact
public import CORALean.ContSet.ContSet.ContSet

@[expose] public section

/-!
# One robust backward step is a Minkowski difference, a sum and a preimage

[1, Eq. 4]: `X_{k+1} = {x | Ax ∈ X_k ⊖ EW ⊕ -BU - K}`, which [1] takes from Kurzhanskiy
and Varaiya. `∀w` is the difference by `EW`, `∃u` the sum with `-BU`, and the state enters
through `A` alone, so the step is a preimage and asks nothing of `A`; [1, Prop. 5] reads it
as the image under `A⁻¹` (`backReachAligned`).

## Inputs
* `A` – state matrix
* `B` – input matrix
* `E` – disturbance matrix
* `K` – offset
* `U` – input set
* `W` – disturbance set
* `X₀` – target set
* `k` – step

## Hypotheses
* none

## Conclusion
* the next set is the preimage of a difference, a sum and an offset

## References

* [1] [L. Yang and N. Ozay. "Scalable zonotopic under-approximation of backward reachable sets for
      uncertain linear systems". IEEE Control Systems Letters,
      2022.](../../../../../../references/2022/yang-lcss-zonotopic-underapproximation.md)
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix Pointwise

variable {n m p : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Eq. 4]: `X_{k+1}` is the preimage under `A` of `X_k ⊖ EW ⊕ -BU - K`. -/
theorem LinearSysDT.backReachSetRobustExact_succ (A : Mat ℝ n n) (B : Mat ℝ n m) (E : Mat ℝ n p)
    (K : Vec ℝ n) (U : Set (Vec ℝ m)) (W : Set (Vec ℝ p)) (X₀ : Set (Vec ℝ n))
    (k : ℕ) : -- --- CONCL ---
    LinearSysDT.backReachSetRobustExact A B E K U W X₀ (k + 1)
      = (A *ᵥ ·) ⁻¹' (minkowskiDiff (LinearSysDT.backReachSetRobustExact A B E K U W X₀ k)
          ((E *ᵥ ·) '' W) + (fun u => -(B *ᵥ u)) '' U + {-K}) := by -- --- PROOF ---
  ext x
  simp only [LinearSysDT.backReachSetRobustExact, Set.mem_setOf_eq, Set.mem_preimage]
  constructor
  -- the input's point of the difference is `Ax + Bu + K`
  · rintro ⟨u, hu, hw⟩
    refine ⟨_, ⟨A *ᵥ x + B *ᵥ u + K, ?_, -(B *ᵥ u), ⟨u, hu, rfl⟩, rfl⟩, -K, rfl, by
      beta_reduce; rw [add_right_comm _ K, add_neg_cancel_right, add_neg_cancel_right]⟩
    rintro _ ⟨w, hwW, rfl⟩
    have := hw w hwW
    rwa [show A *ᵥ x + B *ᵥ u + K + E *ᵥ w = A *ᵥ x + B *ᵥ u + E *ᵥ w + K by abel]
  -- conversely a point `d` of the difference with `Ax = d - Bu - K` gives `Ax + Bu + K = d`
  · rintro ⟨_, ⟨d, hd, _, ⟨u, hu, rfl⟩, rfl⟩, _, rfl, hx⟩
    refine ⟨u, hu, fun w hw => ?_⟩
    have := hd (E *ᵥ w) ⟨w, hw, rfl⟩
    simp only at hx
    rwa [show A *ᵥ x + B *ᵥ u + E *ᵥ w + K = d + E *ᵥ w by rw [← hx]; abel]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
