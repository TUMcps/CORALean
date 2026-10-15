module

public import CORALean.ContSet.ConZonotope.Float.Operations.Rescale
public import CORALean.ContSet.ConZonotope.Float.Theorems.AnchorSlabOuter
public import CORALean.ContSet.ConZonotope.Float.Theorems.MemNominalSet
public import CORALean.ContSet.HPolytope.Float.Theorems.MemConstruct
public import CORALean.ContSet.Interval.Float.Theorems.PlusOuter
public import CORALean.ContSet.Interval.Float.Theorems.SubMemResidual
public import CORALean.ContSet.Zonotope.Float.Theorems.MemGeneratorError

@[expose] public section

/-!
# The float `rescale` encloses the constrained zonotope

When every feasible coefficient vector lies in `[ξL, ξU]` (over ℝ: the box contains
`B∞(A, b)`), each one is `ξm + diag(ξr) δ` with `|δ| ≤ 1`, since the float radius reaches both
ends from the float midpoint. The point at `ξ` is then the rescaled nominal point at `δ` plus
the old error, the centre's rounding and the generators' rounding against `δ`, which is what
the new error box holds; and `δ` meets the rescaled rows, whose right-hand sides were widened by
the same rounding. Outer: the exact layer's `rescale_exact` is an equality, this is not.
-/

-- Authors:       Claude Opus 5.5, Claude Sonnet 5.5
-- Written:       04-October-2026
-- Last update:   15-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Matrix FloatOps SoundFloatArithmetic InflatedContSet

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- A product rounded down is off by at most the rounded gap to the one rounded up. -/
theorem ConZonotope.aux_mulDown_gap (a r : 𝕋) :
    |toReal a * toReal r - toReal (mulDown a r)|
      ≤ toReal (subUp (mulUp a r) (mulDown a r)) := by -- --- PROOF ---
  have h1 := mulDown_le_mul a r
  have h2 := mul_le_mulUp a r
  have h3 := sub_le_subUp (mulUp a r) (mulDown a r)
  rw [abs_le]
  constructor <;> linarith

/-- A row `M diag(r)` rounded down, against `|δ| ≤ 1`, is off by at most its summed gaps. -/
theorem ConZonotope.aux_row_gap {h : ℕ} (a r : Vec 𝕋 h) (δ : Vec ℝ h) (hδ : ∀ j, |δ j| ≤ 1) :
    |∑ j, (toReal (a j) * toReal (r j) - toReal (mulDown (a j) (r j))) * δ j| ≤
      toReal (sumUp fun j => subUp (mulUp (a j) (r j)) (mulDown (a j) (r j))) := by -- --- PROOF ---
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) (le_trans (Finset.sum_le_sum fun j _ => ?_)
    (sum_le_sumUp _))
  rw [abs_mul]
  calc _ ≤ toReal (subUp (mulUp (a j) (r j)) (mulDown (a j) (r j))) * 1 :=
        mul_le_mul (ConZonotope.aux_mulDown_gap _ _) (hδ j) (abs_nonneg _)
          (le_trans (abs_nonneg _) (ConZonotope.aux_mulDown_gap _ _))
    _ = _ := mul_one _

/-- A row against `ξm + diag(r) δ` splits into the row against `ξm`, the row rounded down
against `δ`, and the rounding against `δ`. -/
theorem ConZonotope.aux_row_split {h : ℕ} (a m r : Vec 𝕋 h) (δ ξ : Vec ℝ h)
    (hξ : ∀ j, ξ j = toReal (m j) + toReal (r j) * δ j) :
    ∑ j, toReal (a j) * ξ j = ∑ j, toReal (a j) * toReal (m j)
      + ∑ j, toReal (mulDown (a j) (r j)) * δ j
      + ∑ j, (toReal (a j) * toReal (r j) - toReal (mulDown (a j) (r j)))
        * δ j := by -- --- PROOF ---
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [hξ j]
  ring


-- =======================================  MAIN THEOREM  ======================================= --

theorem ConZonotope.rescale_outer (cZ : ConZonotope 𝕋 (Vec 𝕋 n)) (ξL ξU : Vec 𝕋 cZ.h)
    (hB : ∀ ξ : Vec ℝ cZ.h, (∀ j, |ξ j| ≤ 1) → ξ ∈ cZ.P.nominal.construct →
      ∀ j, toReal (ξL j) ≤ ξ j ∧ ξ j ≤ toReal (ξU j)) :
    cZ.construct ⊆ (cZ.rescale ξL ξU).construct := by -- --- PROOF ---
  intro x hx
  -- the equality rows as a slab first, which `anchorSlab` contains
  refine ConZonotope.anchorSlab_outer _ _ _ _ ?_
  obtain ⟨y, hy', e, he, rfl⟩ := hx
  obtain ⟨ξ, hξ, hP, hy⟩ := ConZonotope.mem_nominalSet_iff.mp hy'
  set ξm : Vec 𝕋 cZ.h := fun j => half (addDown (ξU j) (ξL j)) with hξm
  set ξr : Vec 𝕋 cZ.h := fun j => maximum (subUp (ξU j) (ξm j)) (subUp (ξm j) (ξL j)) with hξr
  -- the radius reaches both ends of the box from the midpoint
  have hdev : ∀ j, |ξ j - toReal (ξm j)| ≤ toReal (ξr j) := by
    intro j
    have h1 := sub_le_subUp (ξU j) (ξm j)
    have h2 := sub_le_subUp (ξm j) (ξL j)
    have h3 : toReal (ξr j) = max (toReal (subUp (ξU j) (ξm j))) (toReal (subUp (ξm j) (ξL j))) :=
      toReal_maximum _ _
    have h4 := le_max_left (toReal (subUp (ξU j) (ξm j))) (toReal (subUp (ξm j) (ξL j)))
    have h5 := le_max_right (toReal (subUp (ξU j) (ξm j))) (toReal (subUp (ξm j) (ξL j)))
    have hb := hB ξ hξ hP j
    rw [abs_le]
    constructor <;> linarith
  -- the rescaled coefficients, `0` where the box is a point
  set δ : Vec ℝ cZ.h := fun j =>
    if toReal (ξr j) = 0 then 0 else (ξ j - toReal (ξm j)) / toReal (ξr j) with hδdef
  have hδ : ∀ j, |δ j| ≤ 1 := by
    intro j
    simp only [hδdef]
    split_ifs with h0
    · simp
    · have hpos : 0 < toReal (ξr j) :=
        lt_of_le_of_ne (le_trans (abs_nonneg _) (hdev j)) (Ne.symm h0)
      rw [abs_div, abs_of_pos hpos, div_le_one hpos]
      exact hdev j
  -- and they map back onto the old ones
  have hξδ : ∀ j, ξ j = toReal (ξm j) + toReal (ξr j) * δ j := by
    intro j
    simp only [hδdef]
    split_ifs with h0
    · have := hdev j
      rw [h0] at this
      have : ξ j - toReal (ξm j) = 0 := abs_nonpos_iff.mp this
      rw [h0]; linarith
    · field_simp
      ring
  -- the generators' rounding against `δ`, entrywise
  have hgen : ∀ i j, |toReal (cZ.G j i) * toReal (ξr j) - toReal (mulDown (cZ.G j i) (ξr j))|
      ≤ toReal (subUp (mulUp (cZ.G j i) (ξr j)) (mulDown (cZ.G j i) (ξr j))) :=
    fun i j => ConZonotope.aux_mulDown_gap _ _
  -- the stored centre's rounding
  have hcen : ∀ i, toReal (addDown (cZ.c i) (dotDown (fun j => cZ.G j i) ξm))
        ≤ toReal (cZ.c i) + ∑ j, toReal (cZ.G j i) * toReal (ξm j)
      ∧ toReal (cZ.c i) + ∑ j, toReal (cZ.G j i) * toReal (ξm j)
        ≤ toReal (addUp (cZ.c i) (dotUp (fun j => cZ.G j i) ξm)) := by
    intro i
    have h1 := dotDown_le (fun j => cZ.G j i) ξm
    have h2 := le_dotUp (fun j => cZ.G j i) ξm
    have h3 := addDown_le_add (cZ.c i) (dotDown (fun j => cZ.G j i) ξm)
    have h4 := add_le_addUp (cZ.c i) (dotUp (fun j => cZ.G j i) ξm)
    constructor <;> linarith
  obtain ⟨hin, heq⟩ := HPolytope.mem_nominal_iff.mp hP
  -- the rounding each constraint row pays against `δ`, summed upward
  set gapA : Fin cZ.P.m → 𝕋 := fun k =>
    sumUp fun j => subUp (mulUp (cZ.P.A k j) (ξr j)) (mulDown (cZ.P.A k j) (ξr j))
  set gapE : Fin cZ.P.me → 𝕋 := fun k =>
    sumUp fun j => subUp (mulUp (cZ.P.Ae k j) (ξr j)) (mulDown (cZ.P.Ae k j) (ξr j))
  refine ⟨fun i => toReal (addDown (cZ.c i) (dotDown (fun j => cZ.G j i) ξm))
      + ∑ j, toReal (mulDown (cZ.G j i) (ξr j)) * δ j,
    ConZonotope.mem_nominalSet_iff.mpr ⟨δ, hδ, ?hP, fun _ => rfl⟩,
    _, Interval.plus_outer _ _ ⟨_, Interval.plus_outer _ _ ⟨e, he, _,
      Interval.sub_mem_residual
        (stored := fun i => addDown (cZ.c i) (dotDown (fun j => cZ.G j i) ξm)) hcen,
      rfl⟩, _, Zonotope.mem_generatorError hgen hδ, rfl⟩, ?_⟩
  case hP =>
    refine HPolytope.mem_stackRows_nominal_iff.mpr
      ⟨HPolytope.mem_nominal_iff.mpr ⟨fun k => ?_, fun k => k.elim0⟩,
        HPolytope.mem_slab_nominal_iff.mpr fun k => ⟨?_, ?_⟩⟩
    · -- an inequality row: the old row at `ξ`, less the part at `ξm`, plus the rounding
      have hk := hin k
      have hs := ConZonotope.aux_row_split (cZ.P.A k) ξm ξr δ ξ hξδ
      have hg := le_of_abs_le (ConZonotope.aux_row_gap (cZ.P.A k) ξr δ hδ)
      have hneg := neg_le_of_abs_le (ConZonotope.aux_row_gap (cZ.P.A k) ξr δ hδ)
      have hd := dotDown_le (cZ.P.A k) ξm
      have hsub := sub_le_subUp (cZ.P.b k) (dotDown (cZ.P.A k) ξm)
      have hadd := add_le_addUp (subUp (cZ.P.b k) (dotDown (cZ.P.A k) ξm)) (gapA k)
      simp only [mulVec, dotProduct, toRealMat] at hk
      show ∑ j, toReal (mulDown (cZ.P.A k j) (ξr j)) * δ j ≤ toReal (addUp
        (subUp (cZ.P.b k) (dotDown (cZ.P.A k) ξm)) (gapA k))
      linarith
    · -- an equality row, read from below
      have hk := (heq k).ge
      have hs := ConZonotope.aux_row_split (cZ.P.Ae k) ξm ξr δ ξ hξδ
      have hg := le_of_abs_le (ConZonotope.aux_row_gap (cZ.P.Ae k) ξr δ hδ)
      have hu := le_dotUp (cZ.P.Ae k) ξm
      have hsub := subDown_le_sub (cZ.P.be k) (dotUp (cZ.P.Ae k) ξm)
      have hsub' := subDown_le_sub (subDown (cZ.P.be k) (dotUp (cZ.P.Ae k) ξm)) (gapE k)
      simp only [mulVec, dotProduct, toRealMat] at hk
      show toReal (subDown (subDown (cZ.P.be k) (dotUp (cZ.P.Ae k) ξm)) (gapE k))
        ≤ ∑ j, toReal (mulDown (cZ.P.Ae k j) (ξr j)) * δ j
      linarith
    · -- and from above
      have hk := (heq k).le
      have hs := ConZonotope.aux_row_split (cZ.P.Ae k) ξm ξr δ ξ hξδ
      have hneg := neg_le_of_abs_le (ConZonotope.aux_row_gap (cZ.P.Ae k) ξr δ hδ)
      have hd := dotDown_le (cZ.P.Ae k) ξm
      have hsub := sub_le_subUp (cZ.P.be k) (dotDown (cZ.P.Ae k) ξm)
      have hadd := add_le_addUp (subUp (cZ.P.be k) (dotDown (cZ.P.Ae k) ξm)) (gapE k)
      simp only [mulVec, dotProduct, toRealMat] at hk
      show ∑ j, toReal (mulDown (cZ.P.Ae k j) (ξr j)) * δ j ≤ toReal (addUp
        (subUp (cZ.P.be k) (dotDown (cZ.P.Ae k) ξm)) (gapE k))
      linarith
  · -- the point: the rescaled one plus the old error and the two roundings
    funext i
    have hs := ConZonotope.aux_row_split (fun j => cZ.G j i) ξm ξr δ ξ hξδ
    have hyi := hy i
    show (toReal (addDown (cZ.c i) (dotDown (fun j => cZ.G j i) ξm))
        + ∑ j, toReal (mulDown (cZ.G j i) (ξr j)) * δ j)
      + ((e i + (toReal (cZ.c i) + ∑ j, toReal (cZ.G j i) * toReal (ξm j)
          - toReal (addDown (cZ.c i) (dotDown (fun j => cZ.G j i) ξm))))
        + ∑ j, (toReal (cZ.G j i) * toReal (ξr j) - toReal (mulDown (cZ.G j i) (ξr j))) * δ j)
      = y i + e i
    rw [hyi, hs]
    ring

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
