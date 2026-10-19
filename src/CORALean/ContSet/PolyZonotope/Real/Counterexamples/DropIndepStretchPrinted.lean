module

public import CORALean.ContSet.PolyZonotope.Real.Operations.DropIndepStretch

@[expose] public section

/-!
# [1, Prop. 2]'s printed stretch `1 + γⱼ` undershoots

[1, Prop. 2] stretches the `n` picked generators by `1 + γⱼ`, `γ = P⁻¹ g^{(i)}`, where
`dropIndepStretch` stretches by `1 + |γⱼ|`. One dimension is enough: one dependent
generator `g = 1` on the factor `α` (so `P = [1]`) and one independent generator
`g^{(i)} = -1`, so `γ = -1`. The printed stretch is `1 + γ = 0`, which leaves `{0}`, while
the set is `α + β·(-1)`, which holds `2` at `α = 1`, `β = -1`. Every hypothesis of
`dropIndepStretch_outer` (`hk`, `hE`, `hPinv`) holds there.

## References

* [1] M. Althoff. "Reachability Analysis of Nonlinear Systems using Conservative
      Polynomialization and Non-Convex Sets". HSCC 2013.
-/

-- Authors:       Claude Opus 5.5
-- Written:       08-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Prop. 2] as printed: stretching the picked generators by `1 + γⱼ` does not
over-approximate. -/
theorem PolyZonotope.dropIndepStretch_printed_counterexample : -- --- CONCL ---
    ¬ ∀ (n : ℕ) (pZ : PolyZonotope (Vec ℝ n)) (r dI : ℕ)
      (partD : Split (Fin pZ.h) into (Fin n) ⊕ (Fin r))
      (partI : Split (Fin pZ.q) into (Fin dI) ⊕ (Fin 1))
      (k : Fin n → Fin pZ.p), Function.Injective k →
      (∀ j k' l, (k' = k j ∨ l = partD.left j) →
        pZ.E k' l = if k' = k j ∧ l = partD.left j then 1 else 0) →
      IsUnit (pZ.dropIndepMat partD).det →
      pZ.construct ⊆ { pZ.dropIndepStretch partD partI with
        G := fun l => match partD.index.symm l with
          | ⟨true, j⟩ => (1 + ((pZ.dropIndepMat partD)⁻¹ *ᵥ pZ.GI (partI.right 0)) j) • pZ.G l
          | ⟨false, _⟩ => pZ.G l }.construct := by -- --- PROOF ---
  intro h
  have sub1 : ∀ x y : Fin (1 + 0), x = y := fun x y => Fin.ext (by omega)
  have sub2 : ∀ x y : Fin 1, x = y := fun x y => Subsingleton.elim x y
  -- one dependent generator `1` on `α` makes `P` the `1 × 1` identity
  have hP : (⟨1, 1, 1, 0, fun _ _ => 1, fun _ _ => 1, fun _ _ => -1⟩ :
      PolyZonotope (Vec ℝ 1)).dropIndepMat (Partition.split 1 0) = 1 := by
    ext i j
    fin_cases i
    fin_cases j
    simp [PolyZonotope.dropIndepMat]
  -- the picked generator sits on the `true` side of the partition
  have hsymm : (Partition.split 1 0).index.symm (0 : Fin (1 + 0))
      = (⟨true, (0 : Fin 1)⟩ : Σ b, Pair (Fin 1) (Fin 0) b) := by
    have := (Partition.split 1 0).index.symm_apply_apply ⟨true, (0 : Fin 1)⟩
    rwa [show (Partition.split 1 0).index ⟨true, (0 : Fin 1)⟩ = 0 from sub1 _ _] at this
  -- all of `dropIndepStretch_outer`'s hypotheses hold, and `2` is in the set
  have hsub := h 1 ⟨1, 1, 1, 0, fun _ _ => 1, fun _ _ => 1, fun _ _ => -1⟩ 0 0
    (Partition.split 1 0) (Partition.split 0 1) (fun _ => 0)
    (fun _ _ _ => sub2 _ _)
    (fun j k' l _ => by
      rw [if_pos ⟨sub2 _ _, sub1 _ _⟩])
    (by rw [hP]; simp)
    (show (fun _ => 2 : Vec ℝ 1) ∈ (⟨1, 1, 1, 0, fun _ _ => 1, fun _ _ => 1, fun _ _ => -1⟩ :
        PolyZonotope (Vec ℝ 1)).construct from
      ⟨fun _ => 1, fun _ => -1, fun _ => by simp, fun _ => by simp, by
        funext i
        fin_cases i
        simp [PolyZonotope.monomial]
        norm_num⟩)
  -- the printed factor is `1 + γ = 0`, so the set is `{0}`
  obtain ⟨a, β, ha, hβ, hx⟩ := hsub
  have h0 := congrFun hx 0
  simp [PolyZonotope.monomial, PolyZonotope.dropIndepStretch, hP, hsymm] at h0

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
