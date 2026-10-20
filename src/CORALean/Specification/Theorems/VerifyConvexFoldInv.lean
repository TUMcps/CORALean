module

public import CORALean.Specification.Operations.VerifyConvex
public import CORALean.Specification.Theorems.DiffPointMemSub

@[expose] public section

/-!
# `aux_verifyConvexStep`'s loop invariant

`verifyConvexFold_inv`: the accumulated points stay inside `O - U`, a `violated` answer
already carries the origin in their hull, and a `safe` one already carries a separating
direction — preserved by every further step of [1, Alg. 3 (exits)].

## Inputs
* `bO` – bounds of the reachable set
* `bU` – bounds of the unsafe set
* `wO` – witnesses of the reachable set
* `wU` – witnesses of the unsafe set
* `ℓ` – sequence of directions

## Hypotheses
* none

## Conclusion
* the fold keeps the invariant of its answer and accumulated points

## References

* [1] M. Wetzlinger, N. Kochdumper, S. Bak and M. Althoff. "Fully-Automated
      Verification of Linear Systems Using Reachability Analysis with Support
      Functions". HSCC, 2023, Article 5.
-/

-- Authors:       Claude Sonnet 5
-- Written:       16-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open scoped Classical Pointwise

variable {α : Type} [AddCommGroup α] [Module ℝ α] {O U : Set α}


-- =======================================  MAIN THEOREM  ======================================= --

/-- The loop's invariant: the accumulated points stay inside `O - U`, a
`violated` answer already carries the origin in their hull, and a `safe` one
already carries a separating direction — preserved by every further step. -/
theorem verifyConvexFold_inv (bO : ∀ d : α →ₗ[ℝ] ℝ, SupportBound O d)
    (bU : ∀ d : α →ₗ[ℝ] ℝ, SupportBound U d) (wO : ∀ d : α →ₗ[ℝ] ℝ, SupportWitness O d)
    (wU : ∀ d : α →ₗ[ℝ] ℝ, SupportWitness U d) (ℓ : ℕ → α →ₗ[ℝ] ℝ) :
    ∀ (todo : List ℕ) {A : VerifyAnswer} {V : Set α}, V ⊆ O - U →
      (A = .violated → (0 : α) ∈ convexHull ℝ V) →
      (A = .safe → ∃ c : α →ₗ[ℝ] ℝ, (bO c).val + (bU (-c)).val < 0) →
      (todo.foldl (aux_verifyConvexStep bO bU wO wU ℓ) (A, V)).2 ⊆ O - U ∧
        ((todo.foldl (aux_verifyConvexStep bO bU wO wU ℓ) (A, V)).1 = .violated →
          (0 : α) ∈ convexHull ℝ (todo.foldl (aux_verifyConvexStep bO bU wO wU ℓ) (A, V)).2) ∧
        ((todo.foldl (aux_verifyConvexStep bO bU wO wU ℓ) (A, V)).1 = .safe →
          ∃ c : α →ₗ[ℝ] ℝ, (bO c).val + (bU (-c)).val < 0)
  -- Base case: nothing left to fold, the hypotheses already are the conclusion.
  | [], _, _, hV, hunsafe, hsafe => ⟨hV, hunsafe, hsafe⟩
  -- A conclusive answer is a fixed point of `aux_verifyConvexStep`, so it carries through.
  | i :: rest, .safe, V, hV, hunsafe, hsafe =>
      verifyConvexFold_inv bO bU wO wU ℓ rest hV hunsafe hsafe
  | i :: rest, .violated, V, hV, hunsafe, hsafe =>
      verifyConvexFold_inv bO bU wO wU ℓ rest hV hunsafe hsafe
  -- Still undecided: unfold one step and case on the two tests it runs.
  | i :: rest, .undecided, V, hV, _, _ => by
      rw [List.foldl_cons]
      simp only [aux_verifyConvexStep]
      by_cases hsep : (bO (ℓ i)).val + (bU (-(ℓ i))).val < 0
      · -- the bounds separate along `ℓ i`: `safe`, certified by `ℓ i` itself
        rw [if_pos hsep]
        exact verifyConvexFold_inv bO bU wO wU ℓ rest hV (fun h => by cases h)
          (fun _ => ⟨ℓ i, hsep⟩)
      · rw [if_neg hsep]
        set V' := insert (diffPoint wO wU (ℓ i)) V with hV'def
        have hV' : V' ⊆ O - U := Set.insert_subset (diffPoint_mem_sub wO wU (ℓ i)) hV
        by_cases hhull : (0 : α) ∈ convexHull ℝ V'
        · -- the new point brings the origin into the hull: `violated`
          rw [if_pos hhull]
          exact verifyConvexFold_inv bO bU wO wU ℓ rest hV' (fun _ => hhull)
            (fun h => by cases h)
        · -- still undecided: fold `V'` in and keep going
          rw [if_neg hhull]
          exact verifyConvexFold_inv bO bU wO wU ℓ rest hV' (fun h => by cases h)
            (fun h => by cases h)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
