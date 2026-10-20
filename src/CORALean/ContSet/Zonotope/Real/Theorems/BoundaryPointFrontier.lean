module

public import CORALean.ContSet.Zonotope.Real.Operations.BoundaryPoint
public import CORALean.ContSet.Zonotope.Real.Theorems.Basic
public import CORALean.ContSet.Zonotope.Real.Theorems.IsBounded

@[expose] public section

/-!
# `Zonotope.boundaryPoint` lies on the boundary

For a nonzero direction and a start point in the zonotope, the returned point is in the zonotope
and no point further along the ray is: it is on the frontier. This is the guarantee CORA's
documentation gives (`x` is the boundary point in direction `dir`); the LP's solution is not
modelled, only what it must satisfy.

## Inputs
* `Z` – zonotope
* `dir` – direction
* `start` – starting point

## Hypotheses
* `hdir` – direction nonzero
* `hs` – start lies in `Z`

## Conclusion
* the boundary point lies on the frontier of `Z`
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [NormedAddCommGroup α] [NormedSpace ℝ α]


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

private theorem aux_step_props (Z : Zonotope α) {dir start : α} (hdir : dir ≠ 0)
    (hs : start ∈ Z.construct) : -- --- CONCL ---
    sSup {t : ℝ | 0 ≤ t ∧ start + t • dir ∈ Z.construct} ∈
        {t : ℝ | 0 ≤ t ∧ start + t • dir ∈ Z.construct} ∧
      BddAbove {t : ℝ | 0 ≤ t ∧ start + t • dir ∈ Z.construct} := by -- --- PROOF ---
  have hbdd : BddAbove {t : ℝ | 0 ≤ t ∧ start + t • dir ∈ Z.construct} := by
    obtain ⟨R, hR⟩ := isBounded_iff_forall_norm_le.mp Z.isBounded_construct
    refine ⟨(R + ‖start‖) / ‖dir‖, fun t ht => ?_⟩
    have hd : 0 < ‖dir‖ := norm_pos_iff.mpr hdir
    rw [le_div_iff₀ hd]
    have h1 : ‖t • dir‖ = t * ‖dir‖ := by rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht.1]
    have h2 : ‖t • dir‖ ≤ ‖start + t • dir‖ + ‖start‖ := by
      calc ‖t • dir‖ = ‖(start + t • dir) - start‖ := by rw [add_sub_cancel_left]
        _ ≤ ‖start + t • dir‖ + ‖start‖ := norm_sub_le _ _
    linarith [hR _ ht.2]
  have hclosed : IsClosed {t : ℝ | 0 ≤ t ∧ start + t • dir ∈ Z.construct} :=
    isClosed_Ici.inter (Z.isClosed_construct.preimage (by fun_prop))
  have hne : {t : ℝ | 0 ≤ t ∧ start + t • dir ∈ Z.construct}.Nonempty :=
    ⟨0, le_refl _, by simpa using hs⟩
  exact ⟨hclosed.csSup_mem hne hbdd, hbdd⟩


/-- The boundary point is in the zonotope. -/
private theorem aux_boundaryPoint_mem (Z : Zonotope α) {dir start : α} (hdir : dir ≠ 0)
    (hs : start ∈ Z.construct) : Z.boundaryPoint dir start ∈ Z.construct :=
  (aux_step_props Z hdir hs).1.2

/-- Nothing further along the ray is in the zonotope. -/
private theorem aux_boundaryPoint_not_mem (Z : Zonotope α) {dir start : α} (hdir : dir ≠ 0)
    (hs : start ∈ Z.construct) {ε : ℝ} (hε : 0 < ε) :
    Z.boundaryPoint dir start + ε • dir ∉ Z.construct := by -- --- PROOF ---
  intro h
  obtain ⟨hmem, hbdd⟩ := aux_step_props Z hdir hs
  have hle := le_csSup hbdd (a := sSup {t : ℝ | 0 ≤ t ∧ start + t • dir ∈ Z.construct} + ε)
    ⟨by linarith [hmem.1], by
      simpa [Zonotope.boundaryPoint, add_smul, add_assoc] using h⟩
  linarith


-- =======================================  MAIN THEOREM  ======================================= --

/-- The boundary point is on the frontier of the zonotope. -/
theorem Zonotope.boundaryPoint_mem_frontier (Z : Zonotope α) {dir start : α}
    (hdir : dir ≠ 0) (hs : start ∈ Z.construct) :
    Z.boundaryPoint dir start ∈ frontier Z.construct := by -- --- PROOF ---
  refine ⟨by rw [Z.isClosed_construct.closure_eq]; exact aux_boundaryPoint_mem Z hdir hs,
    ?_⟩
  intro hint
  have hnhds := mem_interior_iff_mem_nhds.mp hint
  have hcont : Filter.Tendsto (fun ε : ℝ => Z.boundaryPoint dir start + ε • dir)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (Z.boundaryPoint dir start)) := by
    have : Filter.Tendsto (fun ε : ℝ => Z.boundaryPoint dir start + ε • dir) (nhds 0)
        (nhds (Z.boundaryPoint dir start + (0 : ℝ) • dir)) :=
      (continuous_const.add (continuous_id.smul continuous_const)).tendsto 0
    simpa using this.mono_left nhdsWithin_le_nhds
  obtain ⟨ε, hε, hεpos⟩ := ((hcont.eventually hnhds).and self_mem_nhdsWithin).exists
  exact aux_boundaryPoint_not_mem Z hdir hs hεpos hε

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
