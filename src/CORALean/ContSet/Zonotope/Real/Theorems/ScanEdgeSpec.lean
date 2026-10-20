module

public import CORALean.ContSet.Zonotope.Real.Operations.ScanEdge
public import Mathlib.Topology.Order.Compact
public import Mathlib.Topology.Instances.Real.Lemmas
public import Mathlib.Analysis.Convex.Segment

@[expose] public section

/-!
# What one scanned edge contributes

Line 11-15 of [1, Alg. 3] lowers `m` to the least `y` at which the edge meets `L_γ` and raises `M`
to the greatest, and changes nothing when it does not: `m` stays below every `y` of the edge on
the line, `M` above, and each is its old value or such a `y`. The set of such `y` is a compact
interval, so its infimum and supremum are attained.

## Inputs
* `γ` – abscissa of the vertical line
* `P` – edge start
* `Q` – edge end
* `mM` – current interval

## Hypotheses
* none

## Conclusion
* the updated interval widens correctly to cover the edge

## References

* [1] A. Girard and C. Le Guernic. "Zonotope/Hyperplane Intersection for Hybrid Systems
      Reachability Analysis". In Hybrid Systems: Computation and Control (HSCC), LNCS 4981,
      Springer, 2008, pp. 215-228.
-/

-- Authors:       Claude Opus 5.5
-- Written:       11-October-2026
-- Last update:   14-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The `y` at which a segment meets the vertical line form a compact set. -/
theorem Zonotope.aux_hits_compact (γ : ℝ) (P Q : Vec ℝ 2) :
    IsCompact {y : ℝ | (![γ, y] : Vec ℝ 2) ∈ segment ℝ P Q} := by -- --- PROOF ---
  -- the parameters on the line, and `y` as a continuous function of them
  have hT : IsCompact {t : ℝ | t ∈ Set.Icc (0 : ℝ) 1 ∧ P 0 + t * (Q 0 - P 0) = γ} :=
    isCompact_Icc.inter_right (isClosed_eq (by fun_prop) continuous_const)
  have himg := hT.image (f := fun t : ℝ => P 1 + t * (Q 1 - P 1)) (by fun_prop)
  convert himg using 1
  ext y
  rw [Set.mem_setOf_eq, segment_eq_image']
  constructor
  · rintro ⟨t, ht, h⟩
    have h0 := congrFun h 0
    have h1 := congrFun h 1
    simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul] at h0 h1
    exact ⟨t, ⟨ht, h0⟩, h1⟩
  · rintro ⟨t, ⟨ht, h0⟩, h1⟩
    refine ⟨t, ht, ?_⟩
    ext k; fin_cases k
    · simpa using h0
    · simpa using h1


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zonotope.scanEdge_spec (γ : ℝ) (P Q : Vec ℝ 2) (mM : Interval EReal) : -- --- CONCL ---
    (Zonotope.scanEdge γ P Q mM).inf ≤ mM.inf ∧ mM.sup ≤ (Zonotope.scanEdge γ P Q mM).sup ∧
    (∀ y : ℝ, (![γ, y] : Vec ℝ 2) ∈ segment ℝ P Q →
      (Zonotope.scanEdge γ P Q mM).inf ≤ y ∧ (y : EReal) ≤ (Zonotope.scanEdge γ P Q mM).sup) ∧
    ((Zonotope.scanEdge γ P Q mM).inf = mM.inf ∨ ∃ y : ℝ, (![γ, y] : Vec ℝ 2) ∈ segment ℝ P Q ∧
      (Zonotope.scanEdge γ P Q mM).inf = y) ∧
    ((Zonotope.scanEdge γ P Q mM).sup = mM.sup ∨ ∃ y : ℝ, (![γ, y] : Vec ℝ 2) ∈ segment ℝ P Q ∧
      (Zonotope.scanEdge γ P Q mM).sup = y) := by -- --- PROOF ---
  classical
  by_cases hn : (segment ℝ P Q ∩ {z | z 0 = γ}).Nonempty
  · -- the edge meets the line: `m` and `M` are updated with its least and greatest `y`
    obtain ⟨z, hz, hz0⟩ := hn
    have hzy : (![γ, z 1] : Vec ℝ 2) = z := by
      ext k; fin_cases k
      · exact hz0.symm
      · rfl
    have hcpt := Zonotope.aux_hits_compact γ P Q
    have hne : {y : ℝ | (![γ, y] : Vec ℝ 2) ∈ segment ℝ P Q}.Nonempty :=
      ⟨z 1, by simpa [hzy] using hz⟩
    have hym := hcpt.sInf_mem hne
    have hyM := hcpt.sSup_mem hne
    -- the update is by the least and greatest `y` of the edge on the line
    have hsc : Zonotope.scanEdge γ P Q mM
        = ⟨min mM.inf (sInf {y : ℝ | (![γ, y] : Vec ℝ 2) ∈ segment ℝ P Q} : ℝ),
          max mM.sup (sSup {y : ℝ | (![γ, y] : Vec ℝ 2) ∈ segment ℝ P Q} : ℝ)⟩ := by
      unfold Zonotope.scanEdge
      rw [if_pos ⟨z, hz, hz0⟩]
    rw [hsc]
    -- the bounds, then the attained values
    refine ⟨min_le_left _ _, le_max_left _ _, fun y hy => ⟨?_, ?_⟩, ?_, ?_⟩
    · exact (min_le_right _ _).trans (EReal.coe_le_coe_iff.mpr (csInf_le hcpt.bddBelow hy))
    · exact (EReal.coe_le_coe_iff.mpr (le_csSup hcpt.bddAbove hy)).trans (le_max_right _ _)
    · rcases min_choice mM.inf (sInf {y : ℝ | (![γ, y] : Vec ℝ 2) ∈ segment ℝ P Q} : ℝ) with h | h
      · exact Or.inl h
      · exact Or.inr ⟨_, hym, h⟩
    · rcases max_choice mM.sup (sSup {y : ℝ | (![γ, y] : Vec ℝ 2) ∈ segment ℝ P Q} : ℝ) with h | h
      · exact Or.inl h
      · exact Or.inr ⟨_, hyM, h⟩
  · -- it does not: nothing changes, and no `y` of the edge is on the line
    have hsc : Zonotope.scanEdge γ P Q mM = mM := by
      unfold Zonotope.scanEdge
      rw [if_neg hn]
    rw [hsc]
    refine ⟨le_rfl, le_rfl, fun y hy => absurd ⟨_, hy, rfl⟩ hn, Or.inl rfl, Or.inl rfl⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
