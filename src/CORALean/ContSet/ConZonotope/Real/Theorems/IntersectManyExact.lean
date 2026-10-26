module

public import CORALean.ContSet.ConZonotope.Real.Operations.IntersectMany
public import CORALean.ContSet.HPolytope.Real.Theorems.MemIntersection
public import CORALean.ContSet.HPolytope.Real.Theorems.Basic
public import CORALean.ContSet.HPolytope.Real.Operations.Basic
public import CORALean.Global.Entrywise

@[expose] public section

/-!
# `ConZonotope.intersectMany` is exactly the intersection of the sets

[1, Lemma 4]: the coefficient vector splits into the first set's block and one block per further
set. The agreement rows say the points `cⱼ + Gⱼ βⱼ` all equal the first, and each block meets its
own constraints, so a point of every set has coefficients for all of them, and conversely a
coefficient vector of the combined set gives each set its own block. "Unlike for zonotopes, Lemma 4
computes the intersection exactly" ([1]): equality, not an enclosure.

## Inputs
* `cs` – the d + 1 constrained zonotopes

## Hypotheses
* none

## Conclusion
* the result is exactly the intersection of all of them

## References

* [1] A. Alanwar, V. Gaßmann, X. He, H. Said, H. Sandberg, K. H. Johansson and M. Althoff.
      "Privacy-Preserving Set-Based Estimation Using Partially Homomorphic Encryption".
      European Journal of Control, 2023.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       09-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {n d : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- A fold of `intersection` is every polytope at once. -/
private theorem ConZonotope.aux_mem_foldl_intersection {α : Type} [AddCommGroup α] [Module ℝ α]
    {m : ℕ} (g : Fin m → HPolytope α) (init : HPolytope α) (x : α) : -- --- CONCL ---
    x ∈ (Fin.foldl m (fun P i => P.intersection (g i)) init).construct ↔
      x ∈ init.construct ∧ ∀ i, x ∈ (g i).construct := by -- --- PROOF ---
  induction m generalizing init with
  | zero => simp [Fin.foldl_zero]
  | succ m ih =>
    rw [Fin.foldl_succ, ih (fun i => g i.succ) (init.intersection (g 0)),
      HPolytope.mem_intersection_iff, Fin.forall_fin_succ]
    tauto

/-- The coefficients of set `j + 1` inside the stacked vector. -/
private def ConZonotope.aux_block (cs : Fin (d + 1) → ConZonotope (Vec ℝ n))
    (β : Vec ℝ ((cs 0).h + ∑ j : Fin d, (cs j.succ).h)) (j : Fin d) : Vec ℝ (cs j.succ).h :=
  fun t => β (Fin.natAdd (cs 0).h (finSigmaFinEquiv (⟨j, t⟩ : (j : Fin d) × Fin (cs j.succ).h)))

/-- Row `(j, a)` of the agreement block reads the first point against the `j`-th. -/
private theorem ConZonotope.aux_row (cs : Fin (d + 1) → ConZonotope (Vec ℝ n))
    (β : Vec ℝ ((cs 0).h + ∑ j : Fin d, (cs j.succ).h)) (j : Fin d) (a : Fin n) : -- --- CONCL ---
    ∑ u : Fin (∑ j : Fin d, (cs j.succ).h),
        (-(if (finSigmaFinEquiv.symm u).1 = j then (1 : ℝ) else 0)
          * (cs (finSigmaFinEquiv.symm u).1.succ).G (finSigmaFinEquiv.symm u).2 a)
          * β (Fin.natAdd (cs 0).h u)
      = -∑ t, (cs j.succ).G t a * ConZonotope.aux_block cs β j t := by -- --- PROOF ---
  -- sum over the sigma type, where only the `j`-th summand survives
  let F : (j : Fin d) × Fin (cs j.succ).h → ℝ := fun s =>
    (-(if s.1 = j then (1 : ℝ) else 0) * (cs s.1.succ).G s.2 a)
      * β (Fin.natAdd (cs 0).h (finSigmaFinEquiv s))
  -- the summands over the stacked index are those of the sigma type
  have hF : ∀ u : Fin (∑ j : Fin d, (cs j.succ).h),
      (-(if (finSigmaFinEquiv.symm u).1 = j then (1 : ℝ) else 0)
          * (cs (finSigmaFinEquiv.symm u).1.succ).G (finSigmaFinEquiv.symm u).2 a)
          * β (Fin.natAdd (cs 0).h u) = F (finSigmaFinEquiv.symm u) := by
    intro u
    simp only [F, Equiv.apply_symm_apply]
  rw [Finset.sum_congr rfl fun u _ => hF u, Equiv.sum_comp finSigmaFinEquiv.symm F,
    Fintype.sum_sigma, Finset.sum_eq_single j]
  · simp [F, ConZonotope.aux_block, Finset.sum_neg_distrib]
  · intro j' _ hj'
    simp [F, hj']
  · intro h; exact absurd (Finset.mem_univ j) h

private theorem ConZonotope.aux_mem_intersectMany_P_iff (cs : Fin (d + 1) → ConZonotope (Vec ℝ n))
    (β : Vec ℝ ((cs 0).h + ∑ j : Fin d, (cs j.succ).h)) : -- --- CONCL ---
    β ∈ (ConZonotope.intersectMany cs).P.construct ↔
      ((fun t => β (Fin.castAdd _ t)) ∈ (cs 0).P.construct ∧
        ∀ j, ConZonotope.aux_block cs β j ∈ (cs j.succ).P.construct) ∧
      ∀ j a, (∑ t, (cs 0).G t a * β (Fin.castAdd _ t))
          - ∑ t, (cs j.succ).G t a * ConZonotope.aux_block cs β j t
        = (cs j.succ).c a - (cs 0).c a := by -- --- PROOF ---
  unfold ConZonotope.intersectMany
  rw [HPolytope.mem_intersection_iff, ConZonotope.aux_mem_foldl_intersection,
    HPolytope.mem_eqs_iff]
  -- the rows of the equation block, one per `(j, a)`
  have hrow : ∀ j a, ∑ k, (Fin.append (fun t => (cs 0).G t a)
      (fun u => -(if (finSigmaFinEquiv.symm u).1 = j then (1 : ℝ) else 0)
        * (cs (finSigmaFinEquiv.symm u).1.succ).G (finSigmaFinEquiv.symm u).2 a) k) * β k
      = (∑ t, (cs 0).G t a * β (Fin.castAdd _ t))
          - ∑ t, (cs j.succ).G t a * ConZonotope.aux_block cs β j t := by
    intro j a
    rw [Fin.sum_univ_add]
    simp only [Fin.append_left, Fin.append_right]
    rw [ConZonotope.aux_row, sub_eq_add_neg]
  -- the comap memberships are the block extractions by definition
  constructor
  · rintro ⟨⟨h0, hj⟩, hq⟩
    refine ⟨⟨h0, hj⟩, fun j a => ?_⟩
    have := hq (finProdFinEquiv (j, a))
    simp only [Matrix.mulVec, dotProduct, Equiv.symm_apply_apply] at this
    rw [← hrow j a]
    exact this
  · rintro ⟨⟨h0, hj⟩, hq⟩
    refine ⟨⟨h0, hj⟩, fun q => ?_⟩
    simp only [Matrix.mulVec, dotProduct]
    rw [hrow]
    exact hq _ _

/-- Only the first generator block survives; the others are pinned to it. -/
private theorem ConZonotope.aux_value_intersectMany (cs : Fin (d + 1) → ConZonotope (Vec ℝ n))
    (β : Vec ℝ ((cs 0).h + ∑ j : Fin d, (cs j.succ).h)) : -- --- CONCL ---
    (ConZonotope.intersectMany cs).c
        + ∑ l : Fin ((cs 0).h + ∑ j : Fin d, (cs j.succ).h),
            β l • (ConZonotope.intersectMany cs).G l
      = (cs 0).c + ∑ t, β (Fin.castAdd _ t) • (cs 0).G t := by -- --- PROOF ---
  rw [Fin.sum_univ_add]
  simp only [ConZonotope.intersectMany, Fin.append_left, Fin.append_right, Pi.zero_apply,
    smul_zero, Finset.sum_const_zero, add_zero]


-- =======================================  MAIN THEOREM  ======================================= --

theorem ConZonotope.intersectMany_exact
    (cs : Fin (d + 1) → ConZonotope (Vec ℝ n)) : -- --- CONCL ---
    (ConZonotope.intersectMany cs).construct = ⋂ i, (cs i).construct := by -- --- PROOF ---
  ext x
  rw [Set.mem_iInter]
  constructor
  · -- forward: the first block is the first set's coefficients, the others come from the rows
    rintro ⟨β, hβ, hP, hx⟩ i
    obtain ⟨⟨hP0, hPj⟩, hrows⟩ := (ConZonotope.aux_mem_intersectMany_P_iff cs β).mp hP
    have hx0 : x = (cs 0).c + ∑ t, β (Fin.castAdd _ t) • (cs 0).G t := by
      exact hx.trans (ConZonotope.aux_value_intersectMany cs β)
    refine Fin.cases ?_ (fun j => ?_) i
    · exact ⟨fun t => β (Fin.castAdd _ t), fun t => hβ _, hP0, hx0⟩
    · refine ⟨ConZonotope.aux_block cs β j, fun t => hβ _, hPj j, ?_⟩
      funext a
      rw [Entrywise.add_sum_smul_apply]
      have e0 : x a = (cs 0).c a + ∑ t, (cs 0).G t a * β (Fin.castAdd _ t) := by
        rw [hx0, Entrywise.add_sum_smul_apply]
      have hr := hrows j a
      linarith
  · -- back: each set's own coefficients, side by side, are a coefficient vector of the whole
    intro hx
    choose βs hβs hPs hxs using hx
    let γ : (j : Fin d) × Fin (cs j.succ).h → ℝ := fun s => βs s.1.succ s.2
    refine ⟨Fin.append (βs 0) fun u => γ (finSigmaFinEquiv.symm u), ?_, ?_, ?_⟩
    · refine Fin.addCases (fun l => ?_) (fun l => ?_)
      · rw [Fin.append_left]; exact hβs 0 l
      · rw [Fin.append_right]; exact hβs _ _
    -- the blocks read back as the sets' own coefficients, and the rows as their points
    · have hb : ∀ j, ConZonotope.aux_block cs
          (Fin.append (βs 0) fun u => γ (finSigmaFinEquiv.symm u)) j = βs j.succ := by
        intro j
        funext t
        simp only [ConZonotope.aux_block, Fin.append_right]
        rw [Equiv.symm_apply_apply]
      -- the first block, the others, and the agreement rows
      refine (ConZonotope.aux_mem_intersectMany_P_iff cs _).mpr ⟨⟨?_, fun j => ?_⟩, fun j a => ?_⟩
      · have : (fun t => Fin.append (βs 0) (fun u => γ (finSigmaFinEquiv.symm u))
            (Fin.castAdd _ t)) = βs 0 := funext fun t => Fin.append_left _ _ t
        rw [this]; exact hPs 0
      · rw [hb]; exact hPs _
      · rw [hb]
        -- both points are `x`, so their coordinates agree
        have e0 : x a = (cs 0).c a + ∑ t, (cs 0).G t a * βs 0 t := by
          rw [hxs 0, Entrywise.add_sum_smul_apply]
        have ej : x a = (cs j.succ).c a + ∑ t, (cs j.succ).G t a * βs j.succ t := by
          rw [hxs j.succ, Entrywise.add_sum_smul_apply]
        simp only [Fin.append_left]
        linarith
    · have hv := ConZonotope.aux_value_intersectMany cs
        (Fin.append (βs 0) fun u => γ (finSigmaFinEquiv.symm u))
      simp only [Fin.append_left] at hv
      exact (hxs 0).trans hv.symm

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
