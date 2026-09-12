import CORALean.NN.Theorems.MinSuffExplanation
import CORALean.NN.Theorems.SuffExplanationMono

/-!
# [1, Alg. 1]: greedy minimal explanation search, at a sufficiency oracle

Every `suff(...)` call in the printed algorithm is decided by an external
neural network verifier — an NP-complete query in general (§2.3) — never
formalized as a computation here. `greedyMinimalExplanation` instead takes
that decision as an oracle `suff : Finset (Fin n) → Bool`, sound at any oracle
`hsuff` shows correct at `IsSuffExplanation`, not only at one CORALean itself
could certify.

`hl` supplies what line 2's comment records as already true: fixing every
feature makes `explainBox` a single point, so sufficiency there is just the
base classification `f x` already predicting `l` — `Alg. 1` leaves this
implicit in `l := argmax_j f(x)(j)`.

Minimality is the loop's name: a feature kept because dropping it broke
sufficiency at some larger, earlier set must still resist dropping from
whatever smaller set the loop ends at — `IsSuffExplanation.mono`, read as its
contrapositive, carries the witness down.

## References

* [1] S. Bassan, Y. Y. Elboher, T. Ladner, M. Althoff and G. Katz. "Explaining
      Fast and Slow: Abstraction and Refinement of Provable Explanations".
      ICML 2025.
-/

-- Authors:       Tobias Ladner
-- Written:       12-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {n m : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- [1, Alg. 1, l. 3-5]: drop `i` from `E` when the oracle says the result
stays sufficient, otherwise keep `E` as it is. -/
def aux_greedyStep (suff : Finset (Fin n) → Bool) (E : Finset (Fin n)) (i : Fin n) :
    Finset (Fin n) :=
  if suff (E \ {i}) then E \ {i} else E

/-- The loop's invariant: the running set stays sufficient, and every feature
no longer waiting in `todo` already has a witness — carried forward by
`IsSuffExplanation.mono` — that dropping it breaks sufficiency. -/
theorem aux_greedyFold_inv {f : Vec ℝ n → Vec ℝ m} {x : Vec ℝ n} {ε : ℝ} (hε : 0 ≤ ε) {l : Fin m}
    {suff : Finset (Fin n) → Bool} (hsuff : ∀ E, suff E = true ↔ IsSuffExplanation f x ε E l) :
    ∀ (todo : List (Fin n)) {E : Finset (Fin n)}, IsSuffExplanation f x ε E l →
      (∀ j ∈ E, j ∉ todo → ¬ IsSuffExplanation f x ε (E \ {j}) l) →
      IsSuffExplanation f x ε (todo.foldl (aux_greedyStep suff) E) l ∧
        ∀ j ∈ todo.foldl (aux_greedyStep suff) E,
          ¬ IsSuffExplanation f x ε (todo.foldl (aux_greedyStep suff) E \ {j}) l
  | [], E, hsuffE, hminE => ⟨hsuffE, fun j hj => hminE j hj (List.not_mem_nil)⟩
  | i :: rest, E, hsuffE, hminE => by
      have hfold : (i :: rest).foldl (aux_greedyStep suff) E
          = rest.foldl (aux_greedyStep suff) (aux_greedyStep suff E i) := rfl
      rw [hfold]
      by_cases hb : suff (E \ {i}) = true
      · -- the oracle allows dropping `i`: the smaller set is still sufficient
        have hsuffE' : IsSuffExplanation f x ε (E \ {i}) l := (hsuff _).mp hb
        have hstep : aux_greedyStep suff E i = E \ {i} := if_pos hb
        rw [hstep]
        refine aux_greedyFold_inv hε hsuff rest hsuffE' fun j hj hjrest => ?_
        have hjE : j ∈ E := (Finset.mem_sdiff.mp hj).1
        have hji : j ≠ i := fun heq =>
          (Finset.mem_sdiff.mp hj).2 (Finset.mem_singleton.mpr heq)
        have hnotin : j ∉ (i :: rest) := by simp [hji, hjrest]
        -- `(E \ {i}) \ {j} ⊆ E \ {j}`, so a witness at `E \ {j}` transfers down
        intro hcon
        exact hminE j hjE hnotin (hcon.mono hε fun k hk => by
          simp only [Finset.mem_sdiff, Finset.mem_singleton] at hk ⊢
          exact ⟨hk.1.1, hk.2⟩)
      · -- the oracle refuses: `i` stays, and it is now its own witness
        have hstep : aux_greedyStep suff E i = E := if_neg hb
        rw [hstep]
        refine aux_greedyFold_inv hε hsuff rest hsuffE fun j hj hjrest => ?_
        rcases eq_or_ne j i with rfl | hji
        · exact fun hcon => hb ((hsuff _).mpr hcon)
        · exact hminE j hj (by simp [hji, hjrest])


/-- `[n]`, then each feature dropped in turn whenever the oracle still calls
the result sufficient. -/
def greedyMinimalExplanation (n : ℕ) (suff : Finset (Fin n) → Bool) : Finset (Fin n) :=
  (List.finRange n).foldl (aux_greedyStep suff) Finset.univ


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Alg. 1] (Minimal Explanation Search): the greedy loop over any oracle
correct at `f`, `x`, `ε`, `l` returns a minimal sufficient explanation, given
the base classification and a nonnegative perturbation radius. -/
theorem isMinSuffExplanation_greedyMinimalExplanation
    {f : Vec ℝ n → Vec ℝ m} {x : Vec ℝ n} {ε : ℝ} (hε : 0 ≤ ε) {l : Fin m}
    {suff : Finset (Fin n) → Bool} (hsuff : ∀ E, suff E = true ↔ IsSuffExplanation f x ε E l)
    (hl : IsSuffExplanation f x ε Finset.univ l) :
    IsMinSuffExplanation f x ε (greedyMinimalExplanation n suff) l :=
  aux_greedyFold_inv hε hsuff (List.finRange n) hl
    (fun j _ hj => absurd (List.mem_finRange j) hj)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
