module

public import CORALean.ContSet.Zonotope.Float.Operations.QuadMapTriFiltered
public import CORALean.ContSet.Zonotope.Float.Theorems.CompactZerosExact
public import CORALean.ContSet.Zonotope.Float.Theorems.MemNominalSet
public import CORALean.ContSet.Zonotope.Float.Theorems.QuadMapTriOuter

@[expose] public section

/-!
# Float `quadMapTriFiltered` encloses the quadratic image

`quadMapTri` holds the image (`quadMapTri_outer`). `compactZeros` keeps its set
(`compactZeros_exact`). The box keeps the center and the error box; where every coordinate of the
generators but `k` is certified zero, a point `c + Σ βⱼ gⱼ` is `c + t g` with `g` the row sums of
`|gⱼ|` in coordinate `k` (an upper bound, `sum_le_sumUp`) and `t = (Σ βⱼ gⱼₖ) / gₖ`, `|t| ≤ 1`.

## Inputs
* `Q` – quadratic form per output coordinate
* `Z` – zonotope

## Hypotheses
* none

## Conclusion
* the filtered quadratic map holds the quadratic image of the zonotope
-/

-- Authors:       Claude Opus 5.5
-- Written:       16-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Pointwise FloatOps SoundFloatArithmetic InflatedContSet

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n m : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- A certified zero coordinate of the generators is zero as reals. -/
private theorem Zonotope.aux_quadMapTriFiltered_zeroRow (Z : Zonotope (Vec 𝕋 m)) {i : Fin m}
    (h : Z.step_quadMapTriFilteredZeroRow i = true) (j : Fin Z.h) : -- --- CONCL ---
    toReal (Z.G j i) = 0 := by -- --- PROOF ---
  simp only [Zonotope.step_quadMapTriFilteredZeroRow, List.all_eq_true, List.mem_finRange,
    Bool.and_eq_true, forall_const] at h
  have h₁ := toReal_le_of_le (h j).1
  have h₂ := toReal_le_of_le (h j).2
  rw [toReal_zero] at h₁ h₂
  exact le_antisymm h₁ h₂

/-- With at most one coordinate of the generators not certified zero, the nominal zonotope lies
in the nominal zonotope of its box. -/
private theorem Zonotope.aux_quadMapTriFiltered_box (Z : Zonotope (Vec 𝕋 m))
    (hrows : (Finset.univ.filter fun i =>
      Z.step_quadMapTriFilteredZeroRow i = false).card ≤ 1) : -- --- CONCL ---
    nominalSet Z ⊆ nominalSet Z.step_quadMapTriFilteredBox := by -- --- PROOF ---
  intro y hy
  obtain ⟨β, hβ, hyβ⟩ := Zonotope.mem_nominalSet_iff.mp hy
  refine Zonotope.mem_nominalSet_iff.mpr ?_
  by_cases hk : ∃ k, Z.step_quadMapTriFilteredZeroRow k = false
  · obtain ⟨k, hk⟩ := hk
    -- every other coordinate is certified zero
    have hother : ∀ i, i ≠ k → Z.step_quadMapTriFilteredZeroRow i = true := by
      intro i hi
      by_contra hne
      have hmem : ∀ l, Z.step_quadMapTriFilteredZeroRow l = false →
          l ∈ Finset.univ.filter fun i => Z.step_quadMapTriFilteredZeroRow i = false :=
        fun l hl => Finset.mem_filter.mpr ⟨Finset.mem_univ l, hl⟩
      exact hi (Finset.card_le_one.mp hrows i (hmem i (by simpa using hne)) k (hmem k hk))
    -- the coordinate `k`: its sum against `β` and its bound
    set s := ∑ j, toReal (Z.G j k) * β j with hs
    set g := toReal (sumUp fun j => absolute (Z.G j k)) with hg
    have hsg : |s| ≤ g := by
      calc |s| ≤ ∑ j, |toReal (Z.G j k) * β j| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ j, |toReal (Z.G j k)| := Finset.sum_le_sum fun j _ => by
            rw [abs_mul]
            exact mul_le_of_le_one_right (abs_nonneg _) (hβ j)
        _ = ∑ j, toReal (absolute (Z.G j k)) := by simp only [toReal_absolute]
        _ ≤ g := sum_le_sumUp _
    have hg0 : 0 ≤ g := le_trans (abs_nonneg s) hsg
    -- the factor t = s / g of the one generator, in [-1, 1]
    refine ⟨fun _ => if g = 0 then 0 else s / g, fun _ => ?_, fun i => ?_⟩
    · split_ifs with h
      · simp
      · rw [abs_div, abs_of_nonneg hg0]
        exact div_le_one_of_le₀ hsg hg0
    · show y i = toReal (Z.c i) + ∑ _j : Fin 1,
          toReal (if Z.step_quadMapTriFilteredZeroRow i then zero
            else sumUp fun j => absolute (Z.G j i)) * (if g = 0 then 0 else s / g)
      rw [hyβ i, Fin.sum_univ_one]
      -- the coordinate k is c + g t, every other one its center
      by_cases hik : i = k
      · subst hik
        rw [if_neg (by simp [hk]), ← hg, ← hs]
        split_ifs with h
        · have : |s| ≤ 0 := h ▸ hsg
          rw [abs_nonpos_iff.mp this, h, zero_mul]
        · rw [mul_div_cancel₀ s h]
      · have hz := Zonotope.aux_quadMapTriFiltered_zeroRow Z (hother i hik)
        rw [if_pos (hother i hik), toReal_zero, zero_mul]
        simp [hz]
  · -- every coordinate is certified zero: the point is the center
    push Not at hk
    refine ⟨fun _ => 0, fun _ => by simp, fun i => ?_⟩
    have hz := Zonotope.aux_quadMapTriFiltered_zeroRow Z (by simpa using hk i)
    show y i = toReal (Z.c i) + ∑ _j : Fin 1, _ * 0
    rw [hyβ i]
    simp [hz]


-- =======================================  MAIN THEOREM  ======================================= --

/-- `{xᵀQ⁽ⁱ⁾x | x ∈ Z} ⊆ Z.quadMapTriFiltered Q`. -/
theorem Zonotope.quadMapTriFiltered_outer (Q : Fin m → Mat 𝕋 n n)
    (Z : Zonotope (Vec 𝕋 n)) : -- --- CONCL ---
    Real.PolyZonotope.quadEval (fun k => toRealMat (Q k)) '' Z.toSet
      ⊆ (Z.quadMapTriFiltered Q).toSet := by -- --- PROOF ---
  refine (Zonotope.quadMapTri_outer Q Z).trans ?_
  dsimp only [Zonotope.quadMapTriFiltered]
  split_ifs with h
  · -- the box: the same center and error box, the nominal part in the box's
    show nominalSet (Z.quadMapTri Q) + (I_error (Z.quadMapTri Q)).toSet ⊆
      nominalSet (Z.quadMapTri Q).step_quadMapTriFilteredBox +
        (I_error (Z.quadMapTri Q).step_quadMapTriFilteredBox).toSet
    exact Set.add_subset_add (Zonotope.aux_quadMapTriFiltered_box _ h.2) le_rfl
  · rw [Zonotope.compactZeros_exact]

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
