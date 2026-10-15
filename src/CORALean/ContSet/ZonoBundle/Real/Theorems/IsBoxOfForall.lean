module

public import CORALean.ContSet.ZonoBundle.Real.ZonoBundle
public import CORALean.ContSet.Zonotope.Real.Operations.IsBox
public import Mathlib.Data.Finset.Lattice.Fold

@[expose] public section

/-!
# A bundle of boxes is a box

What `aux_isInterval` should test: the intersection of axis-aligned boxes is the box of the
coordinatewise largest lower bound and smallest upper bound, so a bundle all of whose members are
boxes denotes a box. Testing the first member only (`ZonoBundle.isIntervalCora`) is not enough
(`isIntervalCora_counterexample`).
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem ZonoBundle.isBox_of_forall (zB : ZonoBundle (Vec ℝ n)) (hk : 0 < zB.k)
    (h : ∀ i, (zB.Z i).IsBox) :
    ∃ I : Interval (Vec ℝ n), zB.construct = I.construct := by -- --- PROOF ---
  -- the box of the largest lower and smallest upper bounds
  choose Is hIs using h
  have hne : (Finset.univ : Finset (Fin zB.k)).Nonempty := ⟨⟨0, hk⟩, Finset.mem_univ _⟩
  refine ⟨⟨fun j => Finset.univ.sup' hne fun i => (Is i).inf j,
    fun j => Finset.univ.inf' hne fun i => (Is i).sup j⟩, ?_⟩
  ext x
  have hc : ∀ (J : Interval (Vec ℝ n)) (x : Vec ℝ n),
      x ∈ J.construct ↔ ∀ j, J.inf j ≤ x j ∧ x j ≤ J.sup j := fun _ _ => Iff.rfl
  simp only [ZonoBundle.construct, Set.mem_iInter, hIs, hc]
  constructor
  · -- inside every member: above every lower bound, below every upper bound
    intro hx j
    exact ⟨Finset.sup'_le _ _ fun i _ => (hx i j).1, Finset.le_inf' _ _ fun i _ => (hx i j).2⟩
  · -- and the extreme bounds are bounds
    intro hx i j
    exact ⟨(Finset.le_sup' (fun i => (Is i).inf j) (Finset.mem_univ i)).trans (hx j).1,
      (hx j).2.trans (Finset.inf'_le (fun i => (Is i).sup j) (Finset.mem_univ i))⟩


end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
