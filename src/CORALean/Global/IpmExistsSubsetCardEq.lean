module

public import CORALean.Global.SupportConstraintsLengthLe

@[expose] public section

/-!
# `d` of the constraints give the same solution

The covering step of [1, Thm. 3] (Appendix B, Eq. B.2), used by [1, Thm. 4] too: for a convex
Problem 1′ in `d` variables with a unique solution for every set of at least `d` constraints, any
`F` of at least `d` constraints holds `d` constraints `H` with `Î_H = Î_F`. While more than `d`
are left one of them is not a support constraint (`supportConstraints_length_le`), and removing
it keeps the solution, which stays feasible, optimal and so, being unique, the solution.

## Inputs
* `𝒬` – set of candidate predictors
* `μQ` – cost of a candidate
* `I` – predictor family
* `sol` – solution map
* `x` – data
* `F` – subset of constraints

## Hypotheses
* `hμ` – the cost is convex
* `hI` – the predictor membership sets are convex
* `hd` – the dimension is the given one
* `hsol` – every subset of at least that many constraints has a unique optimal solution
* `hF` – the subset has at least that many constraints

## Conclusion
* some subset of that size has the same solution as the whole subset

## References

* [1] M. C. Campi, G. Calafiore and S. Garatti. "Interval predictor models: Identification and
      reliability". Automatica, 2009.
-/

-- Authors:       Claude Opus 5.5
-- Written:       11-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {E Φ Y : Type} [AddCommGroup E] [Module ℝ E] [FiniteDimensional ℝ E] {N d : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem ipm_exists_subset_card_eq {𝒬 : Set E} {μQ : E → ℝ} (hμ : ConvexOn ℝ 𝒬 μQ)
    {I : E → Φ → Set Y} (hI : ∀ ϕ y, Convex ℝ {Q | y ∈ I Q ϕ}) (hd : Module.finrank ℝ E = d)
    {sol : Finset (Fin N) → (Fin N → Φ × Y) → E}
    (hsol : ∀ F x, d ≤ F.card → sol F x ∈ 𝒬 ∧ (∀ t ∈ F, (x t).2 ∈ I (sol F x) (x t).1) ∧
      ∀ Q ∈ 𝒬, (∀ t ∈ F, (x t).2 ∈ I Q (x t).1) → Q ≠ sol F x → μQ (sol F x) < μQ Q)
    (x : Fin N → Φ × Y) (F : Finset (Fin N)) (hF : d ≤ F.card) : -- --- CONCL ---
    ∃ H ⊆ F, H.card = d ∧ sol H x = sol F x := by -- --- PROOF ---
  classical
  obtain ⟨n, hn⟩ := Nat.exists_eq_add_of_le hF
  induction n generalizing F with
  | zero => exact ⟨F, subset_rfl, by omega, rfl⟩
  | succ n ih =>
    obtain ⟨hF1, hF2, hF3⟩ := hsol F x hF
    have hlen := supportConstraints_length_le 𝒬 μQ hμ (fun t => {Q | (x t).2 ∈ I Q (x t).1})
      (fun t => hI _ _) (fun G => sol G x) F
      ⟨hF1, hF2, fun z hz hzF => by
        by_cases h : z = sol F x
        · rw [h]
        · exact (hF3 z hz hzF h).le⟩
      fun l hl => by
        obtain ⟨h1, h2, -⟩ := hsol (F.erase l) x (by rw [Finset.card_erase_of_mem hl]; omega)
        exact ⟨h1, h2⟩
    -- some constraint of `F` is not a support constraint, as `|F| > d`
    have hlt : (supportConstraints (fun G => μQ (sol G x)) F).toFinset.card < F.card :=
      (List.toFinset_card_le _).trans_lt (by omega)
    obtain ⟨l, hlF, hl⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
    have hns : ¬ μQ (sol (F.erase l) x) < μQ (sol F x) := fun h =>
      hl (by simp [supportConstraints, hlF, h])
    have hcard : (F.erase l).card = d + n := by rw [Finset.card_erase_of_mem hlF]; omega
    -- the solution without it is the same
    have heq : sol (F.erase l) x = sol F x := by
      by_contra hne
      obtain ⟨-, -, h3⟩ := hsol (F.erase l) x (by omega)
      exact hns (h3 (sol F x) hF1 (fun t ht => hF2 t (Finset.mem_of_mem_erase ht)) (Ne.symm hne))
    obtain ⟨H, hHF, hHc, hHs⟩ := ih (F.erase l) (by omega) hcard
    exact ⟨H, hHF.trans (Finset.erase_subset _ _), hHc, hHs.trans heq⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
