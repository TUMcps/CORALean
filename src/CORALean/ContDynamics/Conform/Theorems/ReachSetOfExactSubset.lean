module

public import CORALean.ContDynamics.Conform.Theorems.ReachSetOfExactGlo

@[expose] public section

/-!
# [1, Thm. 1]: `Ŷ = Ȳ ⊕ Ê` encloses the reachable set

Any output map `τ`, linearized as `τ̄` along the reference (8): if `Ê` holds every
linearization error `ē = τ - τ̄` [1, Def. 7] the admissible initial states and inputs
produce, then the reachable set lies in `Ȳ ⊕ Ê` (6) — the output is `τ̄ + ē` (9), and `τ̄`
reaches exactly `Ȳ` (`reachSetOfExact_glo`). How tight it is depends on `Ê` alone, `Ȳ` being
exact.

## Inputs
* `τ` – output map
* `yb` – reference output
* `Cb` – state-to-output matrix
* `Db` – input-to-output matrices
* `xs` – nominal initial state
* `cx` – initial center offset
* `X0` – initial uncertainty set
* `us` – nominal inputs
* `cu` – input center offset
* `U` – input uncertainty sets
* `E` – linearization error set

## Hypotheses
* `hE` – `E` holds every linearization error

## Conclusion
* the reachable set lies in the approximation set plus `E`

## References

* [1] L. Lützow and M. Althoff. "Reachset-Conformant System Identification". IEEE
      Transactions on Automatic Control, 71(5):3014-3029, 2026.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Pointwise

variable {n p q k : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Thm. 1]: the reachable set lies in `Ȳ ⊕ Ê` when `Ê` encloses every linearization
error. -/
theorem Conform.reachSetOfExact_subset (τ : Vec ℝ n → (Fin (k + 1) → Vec ℝ p) → Vec ℝ q)
    (yb : Vec ℝ q) (Cb : Mat ℝ q n) (Db : Fin (k + 1) → Mat ℝ q p) (xs cx : Vec ℝ n)
    (X0 : Set (Vec ℝ n)) (us : Fin (k + 1) → Vec ℝ p) (cu : Vec ℝ p)
    (U : Fin (k + 1) → Set (Vec ℝ p)) (E : Set (Vec ℝ q))
    (hE : ∀ x0 ∈ {xs} + X0, ∀ u : Fin (k + 1) → Vec ℝ p, (∀ i, u i ∈ {us i} + U i) →
      τ x0 u - Conform.glo yb Cb Db (xs + cx) (fun i => us i + cu) x0 u ∈ E) : -- --- CONCL ---
    Conform.reachSetOfExact τ xs X0 us U
      ⊆ Conform.gloSet yb Cb Db cx X0 cu U + E := by -- --- PROOF ---
  rintro y ⟨x0, hx0, u, hu, rfl⟩
  rw [← Conform.reachSetOfExact_glo]
  -- the output is the approximation plus its error
  refine ⟨_, ⟨x0, hx0, u, hu, rfl⟩, _, hE x0 hx0 u hu, ?_⟩
  simp only [add_sub_cancel]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
