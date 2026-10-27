module

public import CORALean.ContSet.HPolytope.Real.Operations.BilliardEnd
public import CORALean.Global.BilliardReflectLaw
public import Mathlib.Tactic.Linarith
public import Mathlib.Data.List.MinMax

@[expose] public section

/-!
# The billiard walk never leaves the polytope

`[1, Alg., steps 3-4]` ends the trajectory "at the end of the trajectory of length `ℓ`", and
`[1, Thm. 1]` takes it to lie in `Q`. From an interior point, any direction and any length
`ℓ ≥ 0`, the point `HPolytope.billiardEnd` returns satisfies every inequality: a segment runs
to the first hyperplane, so it stays inside, and a reflection at a point on one hyperplane only
points the new direction inward, `(aᵢ, d') = -(aᵢ, d) < 0` by the reflection law. That is why
the walk is checked for corners: at a point on two hyperplanes the reflected direction can
point out of the second.

## Inputs
* `P` – H-polytope
* `R` – natural number
* `x` – point
* `d` – direction
* `ℓ` – real number

## Hypotheses
* `hx` – `x` is strictly inside every inequality
* `hℓ` – `0 ≤ ℓ`

## Conclusion
* the billiard walk never leaves the polytope

## References

* [1] [B. T. Polyak and E. N. Gryazina. "Billiard walk - a new sampling algorithm for control and
      optimization". IFAC Proceedings Volumes,
      2014.](../../../../../../references/2014/polyak-ifac-billiard-walk.md)
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E]


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

-- a row is its length times the inner product with its unit normal
private theorem HPolytope.aux_row_eq_mul_inner (P : HPolytope E) (i : Fin P.m) : -- --- CONCL ---
    ∃ c : ℝ, 0 ≤ c ∧ (∀ z, P.A i z = c * inner ℝ z (P.facetNormal i)) ∧
      (c ≠ 0 → ‖P.facetNormal i‖ = 1) := by -- --- PROOF ---
  set a : E := (InnerProductSpace.toDual ℝ E).symm (LinearMap.toContinuousLinearMap (P.A i))
    with ha
  have hA : ∀ z, P.A i z = inner ℝ a z := fun z => by
    rw [ha, InnerProductSpace.toDual_symm_apply]; rfl
  refine ⟨‖a‖, norm_nonneg _, fun z => ?_, fun hc => ?_⟩
  · -- `s = ‖a‖⁻¹ a`
    by_cases h0 : a = 0
    · simp [hA, h0]
    · have hn : ‖a‖ ≠ 0 := norm_ne_zero_iff.mpr h0
      simp only [HPolytope.facetNormal, ← ha, inner_smul_right, hA]
      rw [real_inner_comm]; field_simp
  · simp only [HPolytope.facetNormal, ← ha, norm_smul, norm_inv, norm_norm]
    exact inv_mul_cancel₀ hc

-- the segment lemma: up to `t̄` every row holds
omit [FiniteDimensional ℝ E] [CompleteSpace E] in
private theorem HPolytope.aux_segment (P : HPolytope E) (x d : E)
    (hI : ∀ i, P.A i x ≤ P.b i ∧ (P.A i x = P.b i → P.A i d < 0)) (t : ℝ) (ht : 0 ≤ t)
    (hmin : ∀ j, 0 < P.hitTime x d j → t ≤ P.hitTime x d j) : -- --- CONCL ---
    ∀ j, P.A j (x + t • d) ≤ P.b j := by -- --- PROOF ---
  intro j
  have hlin : P.A j (x + t • d) = P.A j x + t * P.A j d := by simp
  rw [hlin]
  rcases le_or_gt (P.A j d) 0 with h | h
  · -- a row moving away: it only gets slacker
    nlinarith [(hI j).1, mul_nonneg ht (neg_nonneg.mpr h)]
  · -- a row moving toward: `t ≤ tⱼ`
    have hs : P.A j x < P.b j := by
      rcases (hI j).1.lt_or_eq with h1 | h1
      · exact h1
      · exact absurd ((hI j).2 h1) (not_lt.mpr h.le)
    have hp : 0 < P.hitTime x d j := div_pos (by linarith) h
    have := hmin j hp
    unfold HPolytope.hitTime at this
    rw [le_div_iff₀ h] at this
    linarith

-- the walk, from a state whose only tight rows point inward
private theorem HPolytope.aux_billiardEnd_mem (P : HPolytope E) (R : ℕ) : -- --- CONCL ---
    ∀ (x d : E) (ℓ : ℝ), (∀ i, P.A i x ≤ P.b i ∧ (P.A i x = P.b i → P.A i d < 0)) → 0 ≤ ℓ →
      ∀ y, P.billiardEnd R x d ℓ = some y → ∀ i, P.A i y ≤ P.b i := by -- --- PROOF ---
  induction R using Nat.strong_induction_on with
  | _ R ih =>
  intro x d ℓ hI hℓ y hy
  -- what the search for `t̄` returns
  have hspec : ∀ i, P.chordHighIndex x d = some i →
      0 < P.hitTime x d i ∧ ∀ j, 0 < P.hitTime x d j → P.hitTime x d i ≤ P.hitTime x d j := by
    intro i hi
    have hmem := List.argmin_mem hi
    simp only [List.mem_filter, List.mem_finRange, true_and, decide_eq_true_eq] at hmem
    refine ⟨hmem, fun j hj => List.le_of_mem_argmin ?_ hi⟩
    simpa using hj
  have hnone : P.chordHighIndex x d = none → ∀ j, ¬ 0 < P.hitTime x d j := by
    intro h j hj
    have h2 := List.argmin_eq_none.mp h
    have : j ∈ (List.finRange P.m).filter fun i => decide (0 < P.hitTime x d i) := by simpa using hj
    simp [h2] at this
  unfold HPolytope.billiardEnd at hy
  cases hc : P.chordHighIndex x d with
  | none =>
    -- the ray never leaves: no row to reach
    rw [hc] at hy
    simp only [Option.some.injEq] at hy
    subst hy
    exact HPolytope.aux_segment P x d hI ℓ hℓ fun j hj => absurd hj (hnone hc j)
  | some i =>
    rw [hc] at hy
    obtain ⟨hpos, hmin⟩ := hspec i hc
    by_cases hle : ℓ ≤ P.hitTime x d i
    · -- the trajectory ends on this segment
      simp only [hle, if_true, Option.some.injEq] at hy
      subst hy
      exact HPolytope.aux_segment P x d hI ℓ hℓ fun j hj => hle.trans (hmin j hj)
    · simp only [hle, if_false] at hy
      cases R with
      | zero => simp at hy
      | succ R =>
        -- a reflection: the boundary point `y'` and the unit normal `s`
        simp only at hy
        split_ifs at hy with hsm
        -- the segment to `t̄` stays inside
        have hseg := HPolytope.aux_segment P x d hI _ hpos.le hmin
        refine ih R (Nat.lt_succ_self R) _ _ _ (fun j => ⟨hseg j, fun htight => ?_⟩)
          (by linarith [not_le.mp hle]) y hy
        -- only row `i` is tight at the boundary point
        have hji : j = i := by
          by_contra hne
          exact (hsm j hne).ne htight
        subst hji
        -- row `i` points outward along `d`
        have hAd : 0 < P.A j d := by
          unfold HPolytope.hitTime at hpos
          rcases div_pos_iff.mp hpos with ⟨_, h⟩ | ⟨h, _⟩
          · exact h
          · exact absurd h (not_lt.mpr (sub_nonneg.mpr (hI j).1))
        -- and inward along the reflected direction
        obtain ⟨c, hc0, hrow, hnorm⟩ := HPolytope.aux_row_eq_mul_inner P j
        have hcne : c ≠ 0 := by
          rintro rfl
          simp [hrow] at hAd
        have h1 := (billiardReflect_law (P.facetNormal j) d (hnorm hcne)).1
        rw [hrow, h1]
        rw [hrow] at hAd
        nlinarith


-- =======================================  MAIN THEOREM  ======================================= --

theorem HPolytope.billiardEnd_mem (P : HPolytope E) (R : ℕ) (x d : E) (ℓ : ℝ)
    (hx : ∀ i, P.A i x < P.b i) (hℓ : 0 ≤ ℓ) :
    ∀ y ∈ P.billiardEnd R x d ℓ,
      ∀ i, P.A i y ≤ P.b i := fun y hy =>
  HPolytope.aux_billiardEnd_mem P R x d ℓ
    (fun i => ⟨(hx i).le, fun h => absurd h (hx i).ne⟩) hℓ y hy

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
