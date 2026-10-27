module

public import CORALean.ContSet.Zonotope.Real.Theorems.SectionEqIccWalkEdges
public import CORALean.ContSet.Zonotope.Real.Theorems.MemShearConstruct
public import CORALean.ContSet.Zonotope.Real.Theorems.MemShearWalkEdges
public import CORALean.ContSet.Zonotope.Real.Operations.Shear
public import Mathlib.Tactic.Ring
public import CORALean.ContSet.Zonotope.Real.Theorems.Basic
public import Mathlib.Analysis.Normed.Group.Basic
public import Mathlib.Topology.MetricSpace.Pseudo.Pi

@[expose] public section

/-!
# The boundary of a sorted zonogon lies on the walk edges

A point of the zonogon that is on no walk edge is interior. On each line `x - κ y = γ` through the
point the section is the segment between two edges (`section_eq_Icc_walkEdges` for the sheared
zonogon, whose edges are the sheared edges), so a point on no edge is strictly inside it, and the
zonogon contains a stretch of the line on both sides. Two lines, `κ = 1` and `κ = -1`, give the
four corners of a square about the point, and the zonogon is convex. Hence the frontier is among
the edges of the two chains of [1, Alg. 3].

## Inputs
* `Z` – planar zonotope

## Hypotheses
* `hh` – at least one generator
* `h1` – generators point upward
* `h2` – generators sorted by angle

## Conclusion
* the frontier lies in the walk edges

## References

* [1] [A. Girard and C. Le Guernic. "Zonotope/Hyperplane Intersection for Hybrid Systems
      Reachability Analysis". Hybrid Systems: Computation and Control,
      2008.](../../../../../../references/2008/girard-hscc-zonotope-hyperplane.md)
-/

-- Authors:       Claude Opus 5.5
-- Written:       11-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The shear keeps the generators in the upper half-plane. -/
private theorem Zonotope.aux_shear_half_plane (Z : Zonotope (Vec ℝ 2)) (κ : ℝ)
    (hH : ∀ j, 0 ≤ Z.G j 1 ∧ (0 < Z.G j 1 ∨ 0 ≤ Z.G j 0)) (j : Fin Z.h) : -- --- CONCL ---
    0 ≤ (Z.shear κ).G j 1 ∧ (0 < (Z.shear κ).G j 1 ∨ 0 ≤ (Z.shear κ).G j 0) := by -- --- PROOF ---
  obtain ⟨h0, h1⟩ := hH j
  refine ⟨h0, ?_⟩
  simp only [Zonotope.shear, Matrix.cons_val_zero, Matrix.cons_val_one]
  rcases h0.eq_or_lt with hy | hy
  · -- on the x-axis the shear is the identity
    right
    have hx : 0 ≤ Z.G j 0 := h1.resolve_left (by rw [← hy]; exact lt_irrefl 0)
    rw [← hy]
    linarith
  · exact Or.inl hy


/-- The shear keeps the cross product of the generators. -/
private theorem Zonotope.aux_shear_cross (Z : Zonotope (Vec ℝ 2)) (κ : ℝ) (i j : Fin Z.h) :
    (Z.shear κ).G i 0 * (Z.shear κ).G j 1 - (Z.shear κ).G i 1 * (Z.shear κ).G j 0
      = Z.G i 0 * Z.G j 1 - Z.G i 1 * Z.G j 0 := by
  simp only [Zonotope.shear, Matrix.cons_val_zero, Matrix.cons_val_one]
  ring


/-- A point of the zonogon off the walk edges has a stretch of every non-horizontal line in it. -/
private theorem Zonotope.aux_oblique (Z : Zonotope (Vec ℝ 2)) (hh : 0 < Z.h)
    (h1 : ∀ j, 0 ≤ Z.G j 1 ∧ (0 < Z.G j 1 ∨ 0 ≤ Z.G j 0))
    (h2 : ∀ i j : Fin Z.h, i < j → 0 ≤ Z.G i 0 * Z.G j 1 - Z.G i 1 * Z.G j 0) (κ : ℝ)
    {q : Vec ℝ 2} (hq : q ∈ Z.construct) (hnE : q ∉ Z.walkEdges) : -- --- CONCL ---
    ∃ t : ℝ, 0 < t ∧
      ∀ s : ℝ, |s| ≤ t → (![q 0 + κ * s, q 1 + s] : Vec ℝ 2) ∈ Z.construct := by -- --- PROOF ---
  -- the section of the sheared zonogon through `q`
  have hqs : (![q 0 - κ * q 1, q 1] : Vec ℝ 2) ∈ (Z.shear κ).construct := by
    rw [Z.mem_shear_construct]
    convert hq using 1
    ext k; fin_cases k <;> simp
  -- the sheared zonogon is sorted too, so the section theorem applies to it
  have hsh1 := fun j => Z.aux_shear_half_plane κ h1 j
  have hsh2 : ∀ i j : Fin (Z.shear κ).h, i < j →
      0 ≤ (Z.shear κ).G i 0 * (Z.shear κ).G j 1 - (Z.shear κ).G i 1 * (Z.shear κ).G j 0 :=
    fun i j hij => (Z.aux_shear_cross κ i j).symm ▸ h2 i j hij
  obtain ⟨yl, yh, hyl, hyh, hS⟩ := (Z.shear κ).section_eq_Icc_walkEdges hh hsh1 hsh2
    (q 0 - κ * q 1) ⟨q 1, hqs⟩
  -- `q` is neither end, since it is on no edge
  have hmem : q 1 ∈ Set.Icc yl yh := by rw [← hS]; exact hqs
  have hback : ∀ y : ℝ, (![q 0 - κ * q 1, y] : Vec ℝ 2) ∈ (Z.shear κ).walkEdges →
      (![q 0 - κ * q 1 + κ * y, y] : Vec ℝ 2) ∈ Z.walkEdges := fun y hy =>
    (Z.mem_shear_walkEdges κ _).mp hy
  have hl : yl < q 1 := lt_of_le_of_ne hmem.1 fun h => hnE (by
    have := hback yl hyl
    rw [h] at this
    convert this using 1
    ext k; fin_cases k <;> simp)
  have hh' : q 1 < yh := lt_of_le_of_ne hmem.2 fun h => hnE (by
    have := hback yh hyh
    rw [← h] at this
    convert this using 1
    ext k; fin_cases k <;> simp)
  -- a stretch of the section about `q`, which is the stretch of the line
  refine ⟨min (q 1 - yl) (yh - q 1), lt_min (by linarith) (by linarith), fun s hs => ?_⟩
  have hs' := abs_le.mp hs
  have hin : q 1 + s ∈ Set.Icc yl yh :=
    ⟨by linarith [min_le_left (q 1 - yl) (yh - q 1)],
      by linarith [min_le_right (q 1 - yl) (yh - q 1)]⟩
  rw [← hS, Set.mem_setOf_eq, Z.mem_shear_construct] at hin
  convert hin using 1
  ext k; fin_cases k
  · simp; ring
  · simp


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zonotope.frontier_subset_walkEdges (Z : Zonotope (Vec ℝ 2)) (hh : 0 < Z.h)
    (h1 : ∀ j, 0 ≤ Z.G j 1 ∧ (0 < Z.G j 1 ∨ 0 ≤ Z.G j 0))
    (h2 : ∀ i j : Fin Z.h, i < j → 0 ≤ Z.G i 0 * Z.G j 1 - Z.G i 1 * Z.G j 0) : -- --- CONCL ---
    frontier Z.construct ⊆ Z.walkEdges := by -- --- PROOF ---
  intro q hq
  by_contra hnE
  have hqZ : q ∈ Z.construct := Z.isClosed_construct.frontier_subset hq
  -- a stretch of the lines `x - y = γ` and `x + y = γ` through `q`, on both sides
  obtain ⟨t₁, ht₁, hs₁⟩ := Z.aux_oblique hh h1 h2 1 hqZ hnE
  obtain ⟨t₂, ht₂, hs₂⟩ := Z.aux_oblique hh h1 h2 (-1) hqZ hnE
  set δ := min t₁ t₂ with hδ
  have hδpos : 0 < δ := lt_min ht₁ ht₂
  have hδ1 : δ ≤ t₁ := min_le_left _ _
  have hδ2 : δ ≤ t₂ := min_le_right _ _
  -- the four corners of the square about `q` are in the zonogon
  have c1 : (![q 0 + δ, q 1 + δ] : Vec ℝ 2) ∈ Z.construct := by
    simpa using hs₁ δ (by rw [abs_of_pos hδpos]; exact hδ1)
  have c2 : (![q 0 - δ, q 1 - δ] : Vec ℝ 2) ∈ Z.construct := by
    simpa [sub_eq_add_neg] using hs₁ (-δ) (by rw [abs_neg, abs_of_pos hδpos]; exact hδ1)
  have c3 : (![q 0 - δ, q 1 + δ] : Vec ℝ 2) ∈ Z.construct := by
    simpa [sub_eq_add_neg] using hs₂ δ (by rw [abs_of_pos hδpos]; exact hδ2)
  have c4 : (![q 0 + δ, q 1 - δ] : Vec ℝ 2) ∈ Z.construct := by
    simpa [sub_eq_add_neg] using hs₂ (-δ) (by rw [abs_neg, abs_of_pos hδpos]; exact hδ2)
  -- so is the whole square, a convex combination of them
  have hsq : ∀ a b : ℝ, |a| ≤ δ → |b| ≤ δ → (![q 0 + a, q 1 + b] : Vec ℝ 2) ∈ Z.construct := by
    intro a b ha hb
    have ha' := abs_le.mp ha
    have hb' := abs_le.mp hb
    have h4 : 0 < 4 * δ ^ 2 := by positivity
    have := Z.convex_construct.sum_mem (t := Finset.univ) (w := ![(δ + a) * (δ + b) / (4 * δ ^ 2),
        (δ - a) * (δ - b) / (4 * δ ^ 2), (δ - a) * (δ + b) / (4 * δ ^ 2),
        (δ + a) * (δ - b) / (4 * δ ^ 2)])
      (z := ![![q 0 + δ, q 1 + δ], ![q 0 - δ, q 1 - δ], ![q 0 - δ, q 1 + δ],
        ![q 0 + δ, q 1 - δ]]) ?_ ?_ ?_
    · convert this using 1
      ext k; fin_cases k
      · simp [Fin.sum_univ_four]; field_simp; ring
      · simp [Fin.sum_univ_four]; field_simp; ring
    · intro i _
      fin_cases i <;> simp <;> apply div_nonneg <;> nlinarith
    · simp [Fin.sum_univ_four]; field_simp; ring
    · intro i _
      fin_cases i <;> simpa
  -- hence `q` is interior, against its being on the frontier
  refine hq.2 (mem_interior_iff_mem_nhds.mpr (Metric.mem_nhds_iff.mpr ⟨δ, hδpos, fun p hp => ?_⟩))
  have hd := (dist_pi_lt_iff hδpos).mp hp
  have h0 := Real.dist_eq (p 0) (q 0) ▸ hd 0
  have h1' := Real.dist_eq (p 1) (q 1) ▸ hd 1
  have := hsq (p 0 - q 0) (p 1 - q 1) h0.le h1'.le
  convert this using 1
  ext k; fin_cases k <;> simp

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
