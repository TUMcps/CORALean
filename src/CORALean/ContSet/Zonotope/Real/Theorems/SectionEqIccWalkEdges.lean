module

public import CORALean.ContSet.Zonotope.Real.Theorems.ExistsEdgeLeastSection
public import CORALean.ContSet.Zonotope.Real.Theorems.SectionConvex
public import CORALean.ContSet.Zonotope.Real.Theorems.MemWalkEdgesIff
public import CORALean.ContSet.Zonotope.Real.Theorems.WalkEdgesCentralSymm
public import CORALean.ContSet.Zonotope.Real.Theorems.WalkEdgesSubsetConstruct
public import CORALean.ContSet.Zonotope.Real.Theorems.CentralSymmMemConstruct

@[expose] public section

/-!
# A vertical section of a zonogon is the segment between two walk edges

For generators in the half-plane `y > 0 ∨ (y = 0 ∧ x ≥ 0)` sorted by angle, the intersection of
the zonogon with a line `x = γ` is `{γ} × [y_l; y_h]` and both ends lie on edges of the walk. The
lower end is `exists_edge_least_section` at `σ = 1` (the line to the right of the lowest corner,
the walk in increasing angle) or `σ = -1` (to its left, the walk back in decreasing angle, the
second block); the upper end is the lower end of the section at `2 c_x - γ`, reflected through the
centre. It is the output specification of [1, Alg. 3] and [1, Alg. 4], with the ends on edges.

## References

* [1] A. Girard and C. Le Guernic. "Zonotope/Hyperplane Intersection for Hybrid Systems
      Reachability Analysis". In Hybrid Systems: Computation and Control (HSCC), LNCS 4981,
      Springer, 2008, pp. 215-228.
-/

-- Authors:       Claude Opus 5.5
-- Written:       11-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The lowest point of a nonempty section is on a walk edge. -/
theorem Zonotope.aux_section_low (Z : Zonotope (Vec ℝ 2)) (hh : 0 < Z.h)
    (h1 : ∀ j, 0 ≤ Z.G j 1 ∧ (0 < Z.G j 1 ∨ 0 ≤ Z.G j 0))
    (h2 : ∀ i j : Fin Z.h, i < j → 0 ≤ Z.G i 0 * Z.G j 1 - Z.G i 1 * Z.G j 0) (γ : ℝ)
    (hne : ∃ y, (![γ, y] : Vec ℝ 2) ∈ Z.construct) :
    ∃ y : ℝ, (![γ, y] : Vec ℝ 2) ∈ Z.walkEdges ∧ (![γ, y] : Vec ℝ 2) ∈ Z.construct ∧
      ∀ y', (![γ, y'] : Vec ℝ 2) ∈ Z.construct → y ≤ y' := by -- --- PROOF ---
  by_cases hlt : Z.corner (fun _ => false) 0 < γ
  · -- to the right of the lowest corner: the first block, in increasing angle
    obtain ⟨a, y, hseg, hy, hmin⟩ := Z.exists_edge_least_section hh h1 (σ := 1) (Or.inl rfl)
      (r := fun j => (j.val : ℤ))
      (fun i j (hij : (i.val : ℤ) = (j.val : ℤ)) => Fin.ext (by exact_mod_cast hij))
      (fun i j (hij : (i.val : ℤ) < (j.val : ℤ)) => by
        have : i < j := Fin.lt_def.mpr (by exact_mod_cast hij)
        simpa using h2 i j this) γ (by simpa using hlt.le) hne
    refine ⟨y, (Z.mem_walkEdges_iff _).mpr ⟨a, Or.inl ?_⟩, hy, hmin⟩
    have e1 : (fun j : Fin Z.h => decide ((j.val : ℤ) < (a.val : ℤ)))
        = fun j => decide (j.val < a.val) := funext fun j => by simp
    have e2 : (fun j : Fin Z.h => decide ((j.val : ℤ) ≤ (a.val : ℤ)))
        = fun j => decide (j.val < a.val + 1) := funext fun j => by simp [Nat.lt_succ_iff]
    rwa [e1, e2] at hseg
  · -- to the left: the second block, back in decreasing angle
    obtain ⟨a, y, hseg, hy, hmin⟩ := Z.exists_edge_least_section hh h1 (σ := -1) (Or.inr rfl)
      (r := fun j => -(j.val : ℤ))
      (fun i j (hij : -(i.val : ℤ) = -(j.val : ℤ)) => Fin.ext (by omega))
      (fun i j (hij : -(i.val : ℤ) < -(j.val : ℤ)) => by
        have : j < i := Fin.lt_def.mpr (by omega)
        have := h2 j i this
        linarith) γ (by simp only [neg_mul, one_mul]; linarith [not_lt.mp hlt]) hne
    refine ⟨y, (Z.mem_walkEdges_iff _).mpr ⟨a, Or.inr ?_⟩, hy, hmin⟩
    have e1 : (fun j : Fin Z.h => decide (-(j.val : ℤ) < -(a.val : ℤ)))
        = fun j => !decide (j.val < a.val + 1) := funext fun j => by
      have : (-(j.val : ℤ) < -(a.val : ℤ)) ↔ ¬ (j.val < a.val + 1) := by omega
      simp only [this, decide_not]
    have e2 : (fun j : Fin Z.h => decide (-(j.val : ℤ) ≤ -(a.val : ℤ)))
        = fun j => !decide (j.val < a.val) := funext fun j => by
      have : (-(j.val : ℤ) ≤ -(a.val : ℤ)) ↔ ¬ (j.val < a.val) := by omega
      simp only [this, decide_not]
    rw [e1, e2, segment_symm] at hseg
    exact hseg


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zonotope.section_eq_Icc_walkEdges (Z : Zonotope (Vec ℝ 2)) (hh : 0 < Z.h)
    (h1 : ∀ j, 0 ≤ Z.G j 1 ∧ (0 < Z.G j 1 ∨ 0 ≤ Z.G j 0))
    (h2 : ∀ i j : Fin Z.h, i < j → 0 ≤ Z.G i 0 * Z.G j 1 - Z.G i 1 * Z.G j 0) (γ : ℝ)
    (hne : ∃ y, (![γ, y] : Vec ℝ 2) ∈ Z.construct) :
    ∃ yl yh : ℝ, (![γ, yl] : Vec ℝ 2) ∈ Z.walkEdges ∧ (![γ, yh] : Vec ℝ 2) ∈ Z.walkEdges ∧
      {y : ℝ | (![γ, y] : Vec ℝ 2) ∈ Z.construct} = Set.Icc yl yh := by -- --- PROOF ---
  obtain ⟨yl, hyl, hylZ, hlow⟩ := Z.aux_section_low hh h1 h2 γ hne
  -- the section at the reflected abscissa, through the centre
  have hrefl : ∀ y : ℝ, (![γ, y] : Vec ℝ 2) ∈ Z.construct →
      (![2 * Z.c 0 - γ, 2 * Z.c 1 - y] : Vec ℝ 2) ∈ Z.construct := fun y hy => by
    have := Z.central_symm_mem_construct hy
    convert this using 1
    ext k; fin_cases k <;> simp
  obtain ⟨y₀, hy₀⟩ := hne
  obtain ⟨yl', hyl', -, hlow'⟩ := Z.aux_section_low hh h1 h2 (2 * Z.c 0 - γ) ⟨_, hrefl y₀ hy₀⟩
  have hpt : (![γ, 2 * Z.c 1 - yl'] : Vec ℝ 2) = (2 : ℝ) • Z.c - ![2 * Z.c 0 - γ, yl'] := by
    ext k; fin_cases k <;> simp
  have hyh : (![γ, 2 * Z.c 1 - yl'] : Vec ℝ 2) ∈ Z.walkEdges := by
    rw [hpt]; exact Z.walkEdges_central_symm hyl'
  refine ⟨yl, 2 * Z.c 1 - yl', hyl, hyh, Set.Subset.antisymm (fun y hy => ⟨hlow y hy, ?_⟩) ?_⟩
  · have := hlow' _ (hrefl y hy)
    linarith
  · exact (Z.section_convex γ).ordConnected.out
      (show yl ∈ _ from hylZ) (show 2 * Z.c 1 - yl' ∈ _ from Z.walkEdges_subset_construct hyh)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
