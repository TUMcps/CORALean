module

public import CORALean.ContSet.Zonotope.Real.Definitions.IsBisectInv
public import CORALean.ContSet.Zonotope.Real.Operations.BisectStep
public import CORALean.ContSet.Zonotope.Real.Theorems.SplitPivotSpec
public import CORALean.ContSet.Zonotope.Real.Theorems.SegmentMeetsVlineIff

@[expose] public section

/-!
# A pass of the dichotomic search keeps the invariant and shrinks `G`

[1, Alg. 4], lines 15-26. The lower half `G<` of the split is either kept, `[P; P + s₁]` meeting
the line, or passed, and then the line is between the abscissae of `P + s₁` and `P + s`, because
the abscissa moves monotonically along `σ`; the order conditions carry over from the split. Each
half is nonempty (`splitPivot_spec`), so `G` shrinks, and when `|G| ≤ 1` the pass changes nothing.

## Inputs
* `Z` – planar zonotope
* `γ` – abscissa of the vertical line
* `right` – direction flag
* `σ` – search direction
* `st` – loop state

## Hypotheses
* `hH` – generators point upward
* `hσ` – direction matches the flag
* `hinv` – invariant holds on the state

## Conclusion
* the step keeps the invariant and shrinks the generator set

## References

* [1] A. Girard and C. Le Guernic. "Zonotope/Hyperplane Intersection for Hybrid Systems Reachability
      Analysis". Hybrid Systems: Computation and Control, 2008.
-/

-- Authors:       Claude Opus 5.5
-- Written:       11-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The sum of generators pointing along `σ` points along `σ`. -/
private theorem Zonotope.aux_sum_horizontal (Z : Zonotope (Vec ℝ 2)) {σ : ℝ} {H : Finset (Fin Z.h)}
    (hH : ∀ i ∈ H, 0 < σ * Z.G i 0) (hne : H.Nonempty) :
    0 < σ * (∑ i ∈ H, (2 : ℝ) • Z.G i) 0 := by
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_pos (fun i hi => by linarith [hH i hi]) hne


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zonotope.bisectInv_step (Z : Zonotope (Vec ℝ 2))
    (hH : ∀ j, 0 ≤ Z.G j 1 ∧ (0 < Z.G j 1 ∨ 0 ≤ Z.G j 0)) (γ : ℝ) (right : Bool) {σ : ℝ}
    (hσ : σ = if right then 1 else -1) (st : Vec ℝ 2 × Finset (Fin Z.h) × Vec ℝ 2)
    (hinv : Z.IsBisectInv γ σ st) : -- --- CONCL ---
    Z.IsBisectInv γ σ (Z.bisectStep γ right st) ∧
    (1 < st.2.1.card → (Z.bisectStep γ right st).2.1.card < st.2.1.card) ∧
    (st.2.1.card ≤ 1 → Z.bisectStep γ right st = st) := by -- --- PROOF ---
  classical
  obtain ⟨P, G, s⟩ := st
  -- with at most one generator the pass does nothing
  by_cases hcard : 1 < G.card
  swap
  · have : Z.bisectStep γ right (P, G, s) = (P, G, s) := by
      -- then the pass keeps one of the halves
      unfold Zonotope.bisectStep
      simp only
      rw [if_neg hcard]
    rw [this]
    exact ⟨hinv, fun h => absurd h hcard, fun _ => rfl⟩
  -- otherwise split `G` at the pivot, both halves nonempty
  obtain ⟨B, hBG, hBA, hGA, hP, hs, hc, hd, he, hf⟩ := hinv
  simp only at hBG hBA hGA hP hs hc hd he hf
  obtain ⟨n1, n2, hun, hdis, hord⟩ := Zonotope.splitPivot_spec Z hH right hσ G hGA hcard hs
  set p := Z.splitPivot right G s with hp
  have hsub1 : p.1 ⊆ G := hun ▸ Finset.subset_union_left
  have hsub2 : p.2 ⊆ G := hun ▸ Finset.subset_union_right
  have hcardG : G.card = p.1.card + p.2.card := by
    rw [← hun]; exact Finset.card_union_of_disjoint hdis
  have hsum : s = ∑ i ∈ p.1, (2 : ℝ) • Z.G i + ∑ i ∈ p.2, (2 : ℝ) • Z.G i := by
    rw [hs, ← Finset.sum_union hdis, hun]
  unfold Zonotope.bisectStep
  simp only [hcard, if_true]
  rw [← hp]
  have hn1 : 0 < p.1.card := Finset.card_pos.mpr n1
  have hn2 : 0 < p.2.card := Finset.card_pos.mpr n2
  refine ⟨?_, fun _ => ?_, fun h => absurd h (not_le.mpr hcard)⟩
  · by_cases hint : (segment ℝ P (P + ∑ i ∈ p.1, (2 : ℝ) • Z.G i) ∩ {z | z 0 = γ}).Nonempty
    · -- the lower half meets the line: keep it
      rw [if_pos hint]
      refine ⟨B, Finset.disjoint_of_subset_right hsub1 hBG, hBA,
        fun i hi => hGA i (hsub1 hi), hP, rfl, fun b hb i hi => hc b hb i (hsub1 hi),
        fun i hi r hr hrB hrp => ?_, (Zonotope.segment_meets_vline_iff _ _ γ).mp hint,
        fun _ => n1⟩
      by_cases hrG : r ∈ G
      · have : r ∈ p.2 := by
          rw [← hun] at hrG
          exact (Finset.mem_union.mp hrG).resolve_left hrp
        exact hord i hi r this
      · exact hd i (hsub1 hi) r hr hrB hrG
    · -- it does not: pass it and go on with the upper half
      rw [if_neg hint]
      -- the line is not on the lower half, so the upper half is next
      have hdisj1 : Disjoint B p.1 := Finset.disjoint_of_subset_right hsub1 hBG
      have hs' : s - ∑ i ∈ p.1, (2 : ℝ) • Z.G i = ∑ i ∈ p.2, (2 : ℝ) • Z.G i := by
        rw [hsum]; abel
      have hx1 : 0 < σ * (∑ i ∈ p.1, (2 : ℝ) • Z.G i) 0 :=
        Zonotope.aux_sum_horizontal Z (fun i hi => hGA i (hsub1 hi)) n1
      have hx2 : 0 < σ * (s - ∑ i ∈ p.1, (2 : ℝ) • Z.G i) 0 := by
        rw [hs']; exact Zonotope.aux_sum_horizontal Z (fun i hi => hGA i (hsub2 hi)) n2
      -- the invariant for the upper half, with the lower half passed
      refine ⟨B ∪ p.1, Finset.disjoint_union_left.mpr
          ⟨Finset.disjoint_of_subset_right hsub2 hBG, hdis⟩,
        fun i hi => (Finset.mem_union.mp hi).elim (hBA i) (fun h => hGA i (hsub1 h)),
        fun i hi => hGA i (hsub2 hi), ?_, hs'.symm ▸ rfl, ?_, ?_, ?_, fun _ => n2⟩
      -- the vertex, then the order of the passed generators against the upper half
      · show P + ∑ i ∈ p.1, (2 : ℝ) • Z.G i = _
        rw [hP, Finset.sum_union hdisj1]; abel
      · intro b hb i hi
        rcases Finset.mem_union.mp hb with hb | hb
        · exact hc b hb i (hsub2 hi)
        · exact hord b hb i hi
      · intro i hi r hr hrB hrp
        refine hd i (hsub2 hi) r hr (fun h => hrB (Finset.mem_union_left _ h)) (fun h => ?_)
        rw [← hun] at h
        rcases Finset.mem_union.mp h with h | h
        · exact hrB (Finset.mem_union_right _ h)
        · exact hrp h
      · -- the line is between the abscissae of `P + s₁` and `P + s`, by monotonicity
        show min ((P + ∑ i ∈ p.1, (2 : ℝ) • Z.G i) 0)
            ((P + ∑ i ∈ p.1, (2 : ℝ) • Z.G i + (s - ∑ i ∈ p.1, (2 : ℝ) • Z.G i)) 0) ≤ γ ∧
          γ ≤ max ((P + ∑ i ∈ p.1, (2 : ℝ) • Z.G i) 0)
            ((P + ∑ i ∈ p.1, (2 : ℝ) • Z.G i + (s - ∑ i ∈ p.1, (2 : ℝ) • Z.G i)) 0)
        have hPs : P + ∑ i ∈ p.1, (2 : ℝ) • Z.G i + (s - ∑ i ∈ p.1, (2 : ℝ) • Z.G i) = P + s := by
          abel
        rw [hPs]
        rw [Zonotope.segment_meets_vline_iff] at hint
        simp only [Pi.add_apply, Pi.sub_apply] at hint hx1 hx2 he ⊢
        rcases (show σ = 1 ∨ σ = -1 by cases right <;> simp [hσ]) with h | h <;> rw [h] at hx1 hx2
        · rw [min_eq_left (by linarith), max_eq_right (by linarith)] at he
          rw [min_eq_left (by linarith), max_eq_right (by linarith)] at hint
          rw [min_eq_left (by linarith), max_eq_right (by linarith)]
          constructor <;> by_contra hcon <;> push Not at hcon <;>
            exact absurd ⟨he.1, by linarith⟩ hint
        · rw [min_eq_right (by linarith), max_eq_left (by linarith)] at he
          rw [min_eq_right (by linarith), max_eq_left (by linarith)] at hint
          rw [min_eq_right (by linarith), max_eq_left (by linarith)]
          constructor <;> by_contra hcon <;> push Not at hcon <;>
            exact absurd ⟨by linarith, he.2⟩ hint
  · -- the half kept is a proper part of `G`
    by_cases hint : (segment ℝ P (P + ∑ i ∈ p.1, (2 : ℝ) • Z.G i) ∩ {z | z 0 = γ}).Nonempty
    · rw [if_pos hint]; show p.1.card < G.card; omega
    · rw [if_neg hint]; show p.2.card < G.card; omega


end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
