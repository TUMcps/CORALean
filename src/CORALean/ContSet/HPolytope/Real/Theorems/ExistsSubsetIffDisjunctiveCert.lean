import CORALean.ContSet.HPolytope.Real.Definitions.AHPolytope
import CORALean.ContSet.HPolytope.Real.Theorems.MemIneqsOfCert
import CORALean.ContSet.HPolytope.Real.Theorems.EqZeroOfMulVecNonpos
import CORALean.ContSet.HPolytope.Real.Theorems.IneqsSubsetIff
import Mathlib.Algebra.BigOperators.Pi

/-!
# Disjunctive containment, as a mixed-integer linear program

`[1, Prop. 4]`: `x̄ + X Px` lies in one of `P₁, …, P_N` iff there are `Λᵢ ≥ 0`,
`δᵢ ∈ {0, 1}`, `βᵢ`, `Γᵢ` with `Λᵢ Hx = Hᵢ Γᵢ`, `Λᵢ hx ≤ δᵢ hᵢ - Hᵢ βᵢ`, `∑ δᵢ = 1`,
`∑ βᵢ = x̄`, `∑ Γᵢ = X` (`[1, Prop. 4, Eq. 31]`). "If": the summands with `δᵢ = 0` land in
`{Hᵢ y ≤ 0}`, which is `{0}` only for a nonempty bounded `Pᵢ`
(`eq_zero_of_mulVec_nonpos`). "Only if": `[1, Lemma 1]`, needing `Px` nonempty. The
printed statement asks neither; `exists_subset_iff_disjunctive_cert_counterexample` breaks
"if" at an empty `Pᵢ`, and the `[1, Lemma 1]` counterexample breaks "only if" at `N = 1`.

## References

* [1] S. Sadraddini and R. Tedrake. "Linear Encodings for Polytope Containment Problems". In
      Proc. of the 58th IEEE Conference on Decision and Control (CDC), pp. 4367-4372, 2019.
      arXiv:1903.05214.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {n nx qx N : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem HPolytope.exists_subset_iff_disjunctive_cert {qy : Fin N → ℕ} {xbar : Vec ℝ n}
    {X : Mat ℝ n nx} {Hx : Mat ℝ qx nx} {hx : Vec ℝ qx} {Hy : (i : Fin N) → Mat ℝ (qy i) n}
    {hy : (i : Fin N) → Vec ℝ (qy i)} (hnex : (HPolytope.ineqs Hx hx).construct.Nonempty)
    (hne : ∀ i, (HPolytope.ineqs (Hy i) (hy i)).construct.Nonempty)
    (hb : ∀ i, Bornology.IsBounded (HPolytope.ineqs (Hy i) (hy i)).construct) :
    (∃ i, HPolytope.ahPolytope xbar X (HPolytope.ineqs Hx hx)
        ⊆ (HPolytope.ineqs (Hy i) (hy i)).construct) ↔
      ∃ (Λ : (i : Fin N) → Mat ℝ (qy i) qx) (δ : Fin N → ℝ) (β : Fin N → Vec ℝ n)
        (Γ : Fin N → Mat ℝ n nx), (∀ i j k, 0 ≤ Λ i j k) ∧ (∀ i, δ i = 0 ∨ δ i = 1) ∧
        (∀ i, Λ i * Hx = Hy i * Γ i) ∧ (∀ i, Λ i *ᵥ hx ≤ δ i • hy i - Hy i *ᵥ β i) ∧
        ∑ i, δ i = 1 ∧ ∑ i, β i = xbar ∧ ∑ i, Γ i = X := by -- --- PROOF ---
  classical
  constructor
  -- `[1, Lemma 1]` at the chosen `i₀`, every other summand zero
  · rintro ⟨i₀, hsub⟩
    have hPx : (HPolytope.ineqs Hx hx).construct
        ⊆ (HPolytope.ineqs (Hy i₀ * X) (hy i₀ - Hy i₀ *ᵥ xbar)).construct := by
      intro p hp
      have h := HPolytope.mem_ineqs_iff.mp (hsub ⟨p, hp, rfl⟩)
      refine HPolytope.mem_ineqs_iff.mpr fun k => ?_
      have hk := h k
      rw [mulVec_add, Pi.add_apply, mulVec_mulVec] at hk
      rw [Pi.sub_apply]
      linarith
    -- everything is `0` off `i₀`, so each condition is checked at `i₀` or is trivial
    obtain ⟨Λ₀, hΛ₀, h1, h2⟩ := (HPolytope.ineqs_subset_iff hnex).mp hPx
    refine ⟨Pi.single (M := fun i => Mat ℝ (qy i) qx) i₀ Λ₀, Pi.single i₀ 1, Pi.single i₀ xbar,
      Pi.single i₀ X, fun i j k => ?_, fun i => ?_, fun i => ?_, fun i => ?_, by simp, by simp,
      by simp⟩
    · by_cases h : i = i₀
      · subst h; simpa using hΛ₀ j k
      · simp [Pi.single_eq_of_ne h]
    · by_cases h : i = i₀
      · subst h; simp
      · simp [Pi.single_eq_of_ne h]
    · by_cases h : i = i₀
      · subst h; simpa using h1
      · simp [Pi.single_eq_of_ne h]
    · by_cases h : i = i₀
      · subst h
        simpa [one_smul] using h2
      · simp [Pi.single_eq_of_ne h]
  -- the one summand with `δ = 1` carries the inbody; the others vanish
  · rintro ⟨Λ, δ, β, Γ, hΛ, hδ, h1, h2, hsum, hc, hX⟩
    have hδ0 : ∀ i, 0 ≤ δ i := fun i => by rcases hδ i with h | h <;> simp [h]
    obtain ⟨i₀, hi₀⟩ : ∃ i, δ i = 1 := by
      by_contra hno
      push Not at hno
      have : ∑ i, δ i = 0 :=
        Finset.sum_eq_zero fun i _ => (hδ i).resolve_right (hno i)
      linarith
    have hothers : ∀ j, j ≠ i₀ → δ j = 0 := by
      intro j hj
      refine (hδ j).resolve_right fun hj1 => ?_
      have := Finset.add_le_sum (f := δ) (fun i _ => hδ0 i) (Finset.mem_univ i₀)
        (Finset.mem_univ j) (Ne.symm hj)
      linarith
    refine ⟨i₀, ?_⟩
    rintro _ ⟨p, hp, rfl⟩
    -- `rᵢ = Γᵢ p + βᵢ` satisfies `Hᵢ rᵢ ≤ δᵢ hᵢ`
    have hr : ∀ i, Γ i *ᵥ p - -β i ∈ (HPolytope.ineqs (Hy i) (δ i • hy i)).construct :=
      fun i => HPolytope.mem_ineqs_of_cert (hΛ i) (h1 i)
        (by simpa [sub_eq_add_neg, mulVec_neg] using h2 i) hp
    have hzero : ∀ j, j ≠ i₀ → Γ j *ᵥ p - -β j = 0 := by
      intro j hj
      refine HPolytope.eq_zero_of_mulVec_nonpos (hne j) (hb j) fun k => ?_
      simpa [hothers j hj] using HPolytope.mem_ineqs_iff.mp (hr j) k
    have hx' : xbar + X *ᵥ p = Γ i₀ *ᵥ p - -β i₀ := by
      rw [← hc, ← hX, Matrix.sum_mulVec, ← Finset.sum_add_distrib,
        Finset.sum_eq_single i₀ (fun j _ hj => by rw [← hzero j hj]; abel) (by simp)]
      abel
    rw [hx']
    simpa [hi₀] using hr i₀

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
