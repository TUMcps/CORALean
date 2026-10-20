module

public import CORALean.ContSet.Zonotope.Float.Operations.DominantDirections

@[expose] public section

/-!
# The dominant directions are stored generators

An answer `P` of `Zonotope.dominantDirections` is `Zonotope.generatorMatrix` of one of the subsets
of the shortlist: the pick of `priv_volumeFilter` only chooses among them, so the columns are
generators of the zonotope, whatever the rounded rankings decided. This is the float counterpart of
`Zonotope.dominantDirections_mem_shortlist`, stated for the shortlist the clamped lengths give.

Source: [1].

## Inputs
* `Z` – zonotope
* `a` – length of the long-generator filter
* `b` – length of the shortlist

## Hypotheses
* none

## Conclusion
* every answer is the matrix of a shortlist subset

## References

* [1] `contSet/@zonotope/dominantDirections.m` and its private helpers, CORA (Sep. 2025), by
      M. Althoff (2010). No paper behind the rule was confirmed.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       10-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zonotope.dominantDirections_mem (Z : Zonotope (Vec 𝕋 n)) (a b : ℕ) : -- --- CONCL ---
    ∀ P ∈ Z.dominantDirections a b,
      ∃ T ∈ Z.dominantShortlist (min a Z.aux_nonzeroCount) (min b Z.aux_nonzeroCount),
        P = Z.generatorMatrix T := by -- --- PROOF ---
  intro P (h : Z.dominantDirections a b = some P)
  -- a fold that keeps the incumbent or the next candidate returns one of them
  have key : ∀ (c : Mat 𝕋 n n → Mat 𝕋 n n → Bool) (l : List (Mat 𝕋 n n))
      (init : Option (Mat 𝕋 n n)),
      l.foldl (fun best Q => match best with
        | none => some Q
        | some R => if c Q R then some Q else some R) init = some P →
      init = some P ∨ P ∈ l := by
    intro c l
    induction l with
    | nil => intro init hl; exact Or.inl hl
    | cons x t ih =>
      intro init hl
      -- the fold after the head is `some P` or `P` is in the tail; look at the head's step
      rcases ih _ hl with h1 | h1
      · cases init with
        | none => simp only [Option.some.injEq] at h1; exact Or.inr (h1 ▸ List.mem_cons_self)
        | some R =>
          simp only at h1
          split_ifs at h1 with hc
          · simp only [Option.some.injEq] at h1; exact Or.inr (h1 ▸ List.mem_cons_self)
          · exact Or.inl h1
      · exact Or.inr (List.mem_cons_of_mem _ h1)
  -- the answer is in the mapped list of candidates, or it is the (absent) initial value
  unfold Zonotope.dominantDirections at h
  rcases key _ _ _ h with h1 | h1
  · exact absurd h1 (by simp)
  · obtain ⟨T, hT, rfl⟩ := List.mem_map.mp h1
    exact ⟨T, hT, rfl⟩

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
