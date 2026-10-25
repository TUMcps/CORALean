module

public import CORALean.ContDynamics.Conform.Operations.SearchOutliers
public import CORALean.ContDynamics.Conform.Theorems.NotIsBoundaryPointIff
public import CORALean.ContDynamics.Conform.Theorems.ConvexFitsUnder

@[expose] public section

/-!
# The boundary-point search finds the optimal outliers

[1, Sec. 5.1.1]: the least leaf cost of the search tree is the least cost of (19) or (20) over
all removals of at most `k` points, and some such removal attains it. `sol S` is an optimum of
the program on the points `S`, `cost S` its value, `bd S` the boundary points of `sol S`
([1, Prop. 8]). Removing points none of which is a boundary point of `sol S` does not lower the
cost: each admits a neighbourhood of `sol S` (`not_isBoundaryPoint_iff`), so `sol S` is a local,
by convexity (`convex_fitsUnder`) a global, optimum. The paper defers the method to Campi et
al.'s Alg. 1; no non-degeneracy is assumed.

## Inputs
* `P` – data point type
* `C` – constraint set per point
* `γ` – cost coefficients
* `sol` – optimum per set of points
* `bd` – boundary points per set of points

## Hypotheses
* `hC` – constraint sets convex

## Conclusion
* the search returns the least cost over removals of at most `k` points

## References

* [1] L. Lützow, M. Eichelbeck, M. J. Kochenderfer and M. Althoff. "Zono-Conformal Prediction:
      Zonotope-Based Uncertainty Quantification for Regression and Classification Tasks". Journal of
      Machine Learning Research, 2025.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix

variable {ι : Type}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- A finite family of positive reals has a positive lower bound. -/
theorem aux_exists_pos_le {X : Type} (s : Finset X) (f : X → ℝ) (hf : ∀ x ∈ s, 0 < f x) :
    ∃ η > 0, ∀ x ∈ s, η ≤ f x := by
  rcases s.eq_empty_or_nonempty with hs | hs
  · exact ⟨1, one_pos, fun x hx => by simp [hs] at hx⟩
  · exact ⟨s.inf' hs f, (Finset.lt_inf'_iff hs).mpr hf, fun x hx => Finset.inf'_le f hx⟩


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Sec. 5.1.1]: `searchOutliers` is the least cost over removals of at most `k` points. -/
theorem Conform.searchOutliers_optimal [Fintype ι] [DecidableEq ι] {P : Type} [DecidableEq P]
    (C : P → Set (ι → ℝ)) (hC : ∀ m, Convex ℝ (C m)) (γ : ι → ℝ) (sol : Finset P → ι → ℝ)
    (bd : Finset P → Finset P) : -- --- CONCL ---
    let Feas : Finset P → (ι → ℝ) → Prop := fun S a =>
      (∀ j, 0 ≤ a j) ∧ ∀ m ∈ S, Conform.FitsUnder (C m) a
    let cost : Finset P → ℝ := fun S => ∑ j, γ j * sol S j
    (∀ S, Feas S (sol S) ∧ ∀ a, Feas S a → cost S ≤ ∑ j, γ j * a j) →
    (∀ S m, m ∈ bd S ↔ m ∈ S ∧ Conform.IsBoundaryPoint (C m) (sol S)) →
    ∀ k S, (∀ T ⊆ S, T.card ≤ k → Conform.searchOutliers cost bd k S ≤ cost (S \ T)) ∧
      ∃ T ⊆ S, T.card ≤ k ∧ Conform.searchOutliers cost bd k S = cost (S \ T) := by -- --- PROOF ---
  intro Feas cost hsol hbd
  -- fewer points never cost more
  have hmono : ∀ S S', S' ⊆ S → cost S' ≤ cost S := fun S S' h =>
    (hsol S').2 _ ⟨(hsol S).1.1, fun m hm => (hsol S).1.2 m (h hm)⟩
  -- removing points that are not boundary points of `sol S` does not lower the cost
  have hkey : ∀ S T, T ⊆ S → (∀ m ∈ T, ¬ Conform.IsBoundaryPoint (C m) (sol S)) →
      cost S ≤ cost (S \ T) := by
    intro S T hTS hT
    obtain ⟨⟨ha0, hafit⟩, -⟩ := hsol S
    obtain ⟨⟨ha'0, ha'fit⟩, -⟩ := hsol (S \ T)
    set a := sol S
    set a' := sol (S \ T)
    -- a strictly fitting `β m` for every `m ∈ T`, and a common slack `η`
    have hstrict : ∀ m ∈ T, ∃ b ∈ C m, (∀ j, |b j| ≤ a j) ∧ ∀ j, 0 < a j → |b j| < a j :=
      fun m hm => (Conform.not_isBoundaryPoint_iff (hC m) (hafit m (hTS hm))).mp (hT m hm)
    choose! b hbC hb hbs using hstrict
    obtain ⟨η, hη, hηle⟩ := aux_exists_pos_le (T ×ˢ Finset.univ.filter fun j => 0 < a j)
      (fun p => a p.2 - |b p.1 p.2|) fun p hp => by
        simp only [Finset.mem_product, Finset.mem_filter, Finset.mem_univ, true_and] at hp
        linarith [hbs p.1 hp.1 p.2 hp.2]
    -- a step `t` towards `a'` small enough to stay within every slack
    set Dn := 1 + ∑ j, |a' j - a j|
    have hDn : 0 < Dn :=
      add_pos_of_pos_of_nonneg one_pos (Finset.sum_nonneg fun j _ => abs_nonneg _)
    set t := min 1 (η / Dn)
    have ht0 : 0 < t := lt_min one_pos (div_pos hη hDn)
    have ht1 : t ≤ 1 := min_le_left _ _
    have htη : ∀ j, t * |a' j - a j| ≤ η := fun j => by
      have hj : |a' j - a j| ≤ Dn := by
        have := Finset.single_le_sum (fun i _ => abs_nonneg (a' i - a i)) (Finset.mem_univ j)
        linarith
      calc t * |a' j - a j| ≤ η / Dn * Dn :=
            mul_le_mul (min_le_right _ _) hj (abs_nonneg _) (div_pos hη hDn).le
        _ = η := div_mul_cancel₀ η hDn.ne'
    -- the point `(1 - t) a + t a'` is feasible for `S`
    have hfeas : Feas S ((1 - t) • a + t • a') := by
      refine ⟨fun j => ?_, fun m hm => ?_⟩
      · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
        nlinarith [ha0 j, ha'0 j]
      · by_cases hmT : m ∈ T
        · refine ⟨b m, hbC m hmT, fun j => ?_⟩
          simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
          rcases (ha0 j).lt_or_eq with hj | hj
          · have h1 := hηle (m, j) (by simp [hmT, hj])
            have h2 := htη j
            have h3 := neg_abs_le (a' j - a j)
            simp only at h1
            nlinarith
          · have h1 := hb m hmT j
            rw [← hj] at h1 ⊢
            nlinarith [ha'0 j]
        · exact Conform.convex_fitsUnder (hC m) (hafit m hm)
            (ha'fit m (Finset.mem_sdiff.mpr ⟨hm, hmT⟩)) (by linarith) ht0.le (by ring)
    -- so `γᵀ a ≤ γᵀ((1 - t) a + t a')`, i.e. `t γᵀa ≤ t γᵀa'`
    have hle := (hsol S).2 _ hfeas
    have hlin : ∑ j, γ j * ((1 - t) • a + t • a') j
        = (1 - t) * cost S + t * cost (S \ T) := by
      simp only [cost, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, mul_add,
        Finset.sum_add_distrib]
      congr 1 <;> refine Finset.sum_congr rfl fun j _ => by ring
    rw [hlin] at hle
    -- divide by `t > 0`
    nlinarith
  -- the search never exceeds its root's cost
  have hroot : ∀ k S, Conform.searchOutliers cost bd k S ≤ cost S := by
    intro k
    induction k with
    | zero => intro S; exact le_rfl
    | succ k ih =>
      intro S
      simp only [Conform.searchOutliers]
      split_ifs with h
      · obtain ⟨b, hb⟩ := h
        exact (Finset.inf'_le _ hb).trans ((ih _).trans (hmono _ _ (Finset.erase_subset _ _)))
      · exact le_rfl
  -- induction on the depth: at depth `0` only `T = ∅` is allowed
  intro k
  induction k with
  | zero =>
    intro S
    refine ⟨fun T _ hT => ?_, ⟨∅, Finset.empty_subset _, le_rfl, by simp [Conform.searchOutliers]⟩⟩
    rw [Finset.card_eq_zero.mp (Nat.le_zero.mp hT), Finset.sdiff_empty]
    exact le_rfl
  | succ k ih =>
    intro S
    refine ⟨fun T hTS hT => ?_, ?_⟩
    · by_cases hex : ∃ b ∈ T, b ∈ bd S
      · -- remove a boundary point of `T` first
        obtain ⟨b, hbT, hbS⟩ := hex
        have hne : (bd S).Nonempty := ⟨b, hbS⟩
        have h1 : Conform.searchOutliers cost bd (k + 1) S
            ≤ Conform.searchOutliers cost bd k (S.erase b) := by
          simp only [Conform.searchOutliers, dif_pos hne]
          exact Finset.inf'_le _ hbS
        have h2 := (ih (S.erase b)).1 (T.erase b) (Finset.erase_subset_erase b hTS)
          (by rw [Finset.card_erase_of_mem hbT]; omega)
        -- removing `b` first, then the rest of `T`, removes `T`
        have hset : S.erase b \ T.erase b = S \ T := by
          ext x
          simp only [Finset.mem_sdiff, Finset.mem_erase]
          constructor
          · rintro ⟨⟨hxb, hx⟩, hn⟩; exact ⟨hx, fun hxT => hn ⟨hxb, hxT⟩⟩
          · rintro ⟨hx, hxT⟩; exact ⟨⟨fun e => hxT (e ▸ hbT), hx⟩, fun h => hxT h.2⟩
        rw [hset] at h2
        exact h1.trans h2
      · -- no point of `T` is a boundary point: the root's cost is already at most
        push Not at hex
        exact (hroot _ S).trans (hkey S T hTS fun m hm hbm => hex m hm ((hbd S m).mpr
          ⟨hTS hm, hbm⟩))
    · by_cases hne : (bd S).Nonempty
      · obtain ⟨b, hbS, hbmin⟩ := Finset.exists_mem_eq_inf' hne
          (fun b => Conform.searchOutliers cost bd k (S.erase b))
        obtain ⟨T', hT'S, hT'k, hT'eq⟩ := (ih (S.erase b)).2
        have hbS' : b ∈ S := ((hbd S b).mp hbS).1
        refine ⟨insert b T', Finset.insert_subset hbS' (hT'S.trans (Finset.erase_subset _ _)),
          (Finset.card_insert_le _ _).trans (by omega), ?_⟩
        simp only [Conform.searchOutliers, dif_pos hne]
        rw [hbmin, hT'eq]
        congr 1
        ext x
        simp only [Finset.mem_sdiff, Finset.mem_erase, Finset.mem_insert]
        tauto
      · refine ⟨∅, Finset.empty_subset _, Nat.zero_le _, ?_⟩
        simp only [Conform.searchOutliers, dif_neg hne, Finset.sdiff_empty]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
