module

public import CORALean.Global.SupportConstraints
public import Mathlib.Analysis.Convex.Radon
public import Mathlib.Analysis.Convex.Function
public import Mathlib.Data.Real.Basic

@[expose] public section

/-!
# A convex program has at most `d` support constraints

[1, Thm. 1], after Calafiore and Campi: a convex problem in `d` variables, `min f(z)` over the
convex `Z` and the convex constraints `Z_t`, `t ∈ F`, has at most `d` support constraints
[1, Def. 3] (`supportConstraints`), the value `w(G) = f(ẑ_G)` read at a solution `ẑ_G` of each
problem. Only the optimality of `ẑ_F` and the feasibility of each `ẑ_{F - l}` are used, not
uniqueness. By Helly's theorem: below the level `c = max_l w(F - l) < w(F)`, the sublevel set and
the `Z_t` have no common point, so some `d + 1` of them have none; a family missing the sublevel
set holds `ẑ_F`, and one missing a support constraint `l` holds `ẑ_{F - l}`, so those `d + 1` are
the sublevel set and every support constraint. The proof of [1, Thm. 3] rests on it.

## Inputs
* `Θ` – domain of the objective
* `f` – objective function
* `Z` – constraint sets
* `sol` – solution map on constraint subsets
* `F` – constraint subset

## Hypotheses
* `hf` – the objective is convex on the domain
* `hZ` – every constraint set is convex
* `hF` – the solution is feasible and optimal for the subset
* `hFl` – each solution with one constraint removed is feasible for the rest

## Conclusion
* the number of support constraints is at most the dimension

## References

* [1] [M. C. Campi, G. Calafiore and S. Garatti. "Interval predictor models: Identification and
      reliability". Automatica,
      2009.](../../../references/2009/campi-automatica-interval-predictor-models.md)
-/

-- Authors:       Claude Opus 5.5
-- Written:       11-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {E : Type} [AddCommGroup E] [Module ℝ E] [FiniteDimensional ℝ E] {N : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem supportConstraints_length_le (Θ : Set E) (f : E → ℝ) (hf : ConvexOn ℝ Θ f)
    (Z : Fin N → Set E) (hZ : ∀ t, Convex ℝ (Z t)) (sol : Finset (Fin N) → E) (F : Finset (Fin N))
    (hF : sol F ∈ Θ ∧ (∀ t ∈ F, sol F ∈ Z t) ∧ ∀ z ∈ Θ, (∀ t ∈ F, z ∈ Z t) → f (sol F) ≤ f z)
    (hFl : ∀ l ∈ F, sol (F.erase l) ∈ Θ ∧ ∀ t ∈ F.erase l, sol (F.erase l) ∈ Z t) : -- --- CONCL ---
    (supportConstraints (fun G => f (sol G)) F).length ≤ Module.finrank ℝ E := by -- --- PROOF ---
  classical
  set S := (supportConstraints (fun G => f (sol G)) F).toFinset with hS
  have hnd : (supportConstraints (fun G => f (sol G)) F).Nodup :=
    (List.nodup_finRange N).filter _
  have hmem : ∀ l, l ∈ S ↔ l ∈ F ∧ f (sol (F.erase l)) < f (sol F) := by
    intro l; simp [hS, supportConstraints]
  rw [← List.toFinset_card_of_nodup hnd, ← hS]
  by_contra hcard
  push Not at hcard
  have hSne : S.Nonempty := Finset.card_pos.mp (by omega)
  -- the level `c`, the largest value without one support constraint, is below `w(F)`
  set c := S.sup' hSne fun l => f (sol (F.erase l))
  have hc : c < f (sol F) := (Finset.sup'_lt_iff hSne).mpr fun l hl => ((hmem l).mp hl).2
  let K : Option (Fin N) → Set E := fun i => i.elim {z | z ∈ Θ ∧ f z ≤ c} Z
  have hKc : ∀ i ∈ F.insertNone, Convex ℝ (K i) := by
    rintro (_ | t) _
    · exact hf.convex_le c
    · exact hZ t
  -- no point is feasible below the level
  have hempty : ¬ (⋂ i ∈ F.insertNone, K i).Nonempty := by
    rintro ⟨z, hz⟩
    simp only [Set.mem_iInter] at hz
    have h0 := hz none (Finset.mem_insertNone.mpr (by simp))
    have hfeas : ∀ t ∈ F, z ∈ Z t := fun t ht => hz (some t) (Finset.mem_insertNone.mpr (by simpa))
    exact absurd (hF.2.2 z h0.1 hfeas) (not_le.mpr (lt_of_le_of_lt h0.2 hc))
  -- so some `d + 1` of the sets have no common point
  have hhelly := mt (Convex.helly_theorem' (𝕜 := ℝ) hKc) hempty
  push Not at hhelly
  obtain ⟨I, hIs, hIcard, hIe⟩ := hhelly
  -- that family holds the sublevel set and every support constraint
  have hnone : none ∈ I := by
    by_contra hn
    refine (Set.nonempty_iff_ne_empty.mp ⟨sol F, ?_⟩) hIe
    simp only [Set.mem_iInter]
    rintro (_ | t) hi
    · exact absurd hi hn
    · have := Finset.mem_insertNone.mp (hIs hi); exact hF.2.1 t (by simpa using this)
  -- a family missing a support constraint `l` holds the solution without it
  have hsome : ∀ l ∈ S, some l ∈ I := by
    intro l hl
    by_contra hn
    have hlF := ((hmem l).mp hl).1
    refine (Set.nonempty_iff_ne_empty.mp ⟨sol (F.erase l), ?_⟩) hIe
    simp only [Set.mem_iInter]
    rintro (_ | t) hi
    · exact ⟨(hFl l hlF).1, Finset.le_sup' (fun l => f (sol (F.erase l))) hl⟩
    · have htF : t ∈ F := by simpa using Finset.mem_insertNone.mp (hIs hi)
      have htl : t ≠ l := by rintro rfl; exact hn hi
      exact (hFl l hlF).2 t (Finset.mem_erase.mpr ⟨htl, htF⟩)
  have hsub : S.insertNone ⊆ I := by
    rintro (_ | l) hi
    · exact hnone
    · exact hsome l (by simpa using Finset.mem_insertNone.mp hi)
  have := Finset.card_le_card hsub
  rw [Finset.card_insertNone] at this
  omega

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
