import CORALean.Specification.Specification
import CORALean.Global.LinProg.LinProg
import CORALean.Specification.VerifyAnswer

/-!
# [1, Alg. 3]: a GJK-style search for a separating or an intersecting direction

The two conclusive exits of `Alg. 3` — line 4-5 (`safe`) and line 12-13
(`unsafe`) — folded over a caller-supplied direction sequence `ℓ` and a fuel
bound, since the search loop need not terminate. Everything else the printed
algorithm does — the Gram-Schmidt direction search of lines 18-25, and the
`falsifiable` flag with the `Δt`-halving restart of lines 7, 14-16 — only ever
changes which direction is tried next, never whether a taken exit is sound, so
none of it is modelled here.

`ℓ i` is read against one reachable set `O` and one unsafe set `U`: the paper's
`R̂(t)` (a `SupportBound`, line 4) and `R̲(t)` (a `SupportWitness`, line 10)
become one bound and one witness on the same `O`, nothing below needing them
to come from different approximations.

## References

* [1] M. Wetzlinger, N. Kochdumper, S. Bak and M. Althoff. "Fully-Automated
      Verification of Linear Systems Using Reachability Analysis with Support
      Functions". HSCC, 2023, Article 5.
-/

-- Authors:       Tobias Ladner
-- Written:       16-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open scoped Classical Pointwise

variable {α : Type} [AddCommGroup α] [Module ℝ α] {O U : Set α}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- [1, Alg. 3, l. 10]: the difference between a reachable-set witness point
and an unsafe-set witness point along `d`, fed into `P̲`. -/
noncomputable def aux_diffPoint (wO : ∀ d : α →ₗ[ℝ] ℝ, SupportWitness O d)
    (wU : ∀ d : α →ₗ[ℝ] ℝ, SupportWitness U d) (d : α →ₗ[ℝ] ℝ) : α :=
  (wO d).mem.choose - (wU (-d)).mem.choose

/-- Both witness points lie in their own sets, so the difference lies in `O - U`. -/
theorem aux_diffPoint_mem_sub (wO : ∀ d : α →ₗ[ℝ] ℝ, SupportWitness O d)
    (wU : ∀ d : α →ₗ[ℝ] ℝ, SupportWitness U d) (d : α →ₗ[ℝ] ℝ) :
    aux_diffPoint wO wU d ∈ O - U :=
  Set.sub_mem_sub (wO d).mem.choose_spec.1 (wU (-d)).mem.choose_spec.1

/-- [1, Alg. 3, l. 4-13] for one direction `ℓ i`: `safe` once the bounds
separate, `violated` once the accumulated hull reaches the origin, else the
new point is folded in. A reached answer is carried forward, extra fuel harmless. -/
noncomputable def aux_verifyConvexStep (bO : ∀ d : α →ₗ[ℝ] ℝ, SupportBound O d)
    (bU : ∀ d : α →ₗ[ℝ] ℝ, SupportBound U d) (wO : ∀ d : α →ₗ[ℝ] ℝ, SupportWitness O d)
    (wU : ∀ d : α →ₗ[ℝ] ℝ, SupportWitness U d) (ℓ : ℕ → α →ₗ[ℝ] ℝ) :
    VerifyAnswer × Set α → ℕ → VerifyAnswer × Set α
  | (.safe, V), _ => (.safe, V)
  | (.violated, V), _ => (.violated, V)
  | (.undecided, V), i =>
      if (bO (ℓ i)).val + (bU (-(ℓ i))).val < 0 then (.safe, V)
      else
        let V' := insert (aux_diffPoint wO wU (ℓ i)) V
        if (0 : α) ∈ convexHull ℝ V' then (.violated, V') else (.undecided, V')

/-- The loop's invariant: the accumulated points stay inside `O - U`, a
`violated` answer already carries the origin in their hull, and a `safe` one
already carries a separating direction — preserved by every further step. -/
theorem aux_verifyConvexFold_inv (bO : ∀ d : α →ₗ[ℝ] ℝ, SupportBound O d)
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
      aux_verifyConvexFold_inv bO bU wO wU ℓ rest hV hunsafe hsafe
  | i :: rest, .violated, V, hV, hunsafe, hsafe =>
      aux_verifyConvexFold_inv bO bU wO wU ℓ rest hV hunsafe hsafe
  -- Still undecided: unfold one step and case on the two tests it runs.
  | i :: rest, .undecided, V, hV, _, _ => by
      rw [List.foldl_cons]
      simp only [aux_verifyConvexStep]
      by_cases hsep : (bO (ℓ i)).val + (bU (-(ℓ i))).val < 0
      · -- the bounds separate along `ℓ i`: `safe`, certified by `ℓ i` itself
        rw [if_pos hsep]
        exact aux_verifyConvexFold_inv bO bU wO wU ℓ rest hV (fun h => by cases h)
          (fun _ => ⟨ℓ i, hsep⟩)
      · rw [if_neg hsep]
        set V' := insert (aux_diffPoint wO wU (ℓ i)) V with hV'def
        have hV' : V' ⊆ O - U := Set.insert_subset (aux_diffPoint_mem_sub wO wU (ℓ i)) hV
        by_cases hhull : (0 : α) ∈ convexHull ℝ V'
        · -- the new point brings the origin into the hull: `violated`
          rw [if_pos hhull]
          exact aux_verifyConvexFold_inv bO bU wO wU ℓ rest hV' (fun _ => hhull)
            (fun h => by cases h)
        · -- still undecided: fold `V'` in and keep going
          rw [if_neg hhull]
          exact aux_verifyConvexFold_inv bO bU wO wU ℓ rest hV' (fun h => by cases h)
            (fun h => by cases h)


-- =====================================  MAIN DEFINITION  ====================================== --

/-- [1, Alg. 3]: fold `aux_verifyConvexStep` over `fuel` directions drawn from
`ℓ`, starting undecided with nothing accumulated. -/
noncomputable def verifyConvex (bO : ∀ d : α →ₗ[ℝ] ℝ, SupportBound O d)
    (bU : ∀ d : α →ₗ[ℝ] ℝ, SupportBound U d) (wO : ∀ d : α →ₗ[ℝ] ℝ, SupportWitness O d)
    (wU : ∀ d : α →ₗ[ℝ] ℝ, SupportWitness U d) (ℓ : ℕ → α →ₗ[ℝ] ℝ) (fuel : ℕ) :
    VerifyAnswer :=
  ((List.range fuel).foldl (aux_verifyConvexStep bO bU wO wU ℓ)
    (.undecided, (∅ : Set α))).1

/-- A `safe` answer came from the bounds already separating along some
direction the search tried. -/
theorem exists_separating_of_verifyConvex_eq_safe (bO : ∀ d : α →ₗ[ℝ] ℝ, SupportBound O d)
    (bU : ∀ d : α →ₗ[ℝ] ℝ, SupportBound U d) (wO : ∀ d : α →ₗ[ℝ] ℝ, SupportWitness O d)
    (wU : ∀ d : α →ₗ[ℝ] ℝ, SupportWitness U d) (ℓ : ℕ → α →ₗ[ℝ] ℝ) (fuel : ℕ)
    (h : verifyConvex bO bU wO wU ℓ fuel = .safe) :
    ∃ c : α →ₗ[ℝ] ℝ, (bO c).val + (bU (-c)).val < 0 :=
  (aux_verifyConvexFold_inv bO bU wO wU ℓ (List.range fuel)
    (Set.empty_subset _) (fun h => by cases h) (fun h => by cases h)).2.2 h

/-- An `unsafe` answer came from a finite set of accumulated `O - U` points
whose hull already reaches the origin. -/
theorem exists_convexHull_of_verifyConvex_eq_unsafe (bO : ∀ d : α →ₗ[ℝ] ℝ, SupportBound O d)
    (bU : ∀ d : α →ₗ[ℝ] ℝ, SupportBound U d) (wO : ∀ d : α →ₗ[ℝ] ℝ, SupportWitness O d)
    (wU : ∀ d : α →ₗ[ℝ] ℝ, SupportWitness U d) (ℓ : ℕ → α →ₗ[ℝ] ℝ) (fuel : ℕ)
    (h : verifyConvex bO bU wO wU ℓ fuel = .violated) :
    ∃ V : Set α, V ⊆ O - U ∧ (0 : α) ∈ convexHull ℝ V :=
  let inv := aux_verifyConvexFold_inv bO bU wO wU ℓ (List.range fuel)
    (Set.empty_subset _) (fun h => by cases h) (fun h => by cases h)
  ⟨_, inv.1, inv.2.1 h⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
