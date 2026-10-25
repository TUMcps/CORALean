module

public import CORALean.ContSet.Taylm.Real.Operations.BnbLoop
public import CORALean.ContSet.Taylm.Real.Theorems.SplitAtCovers
public import CORALean.ContSet.Taylm.Real.Theorems.ListMinLe
public import CORALean.ContSet.Taylm.Real.Theorems.LeListMax

@[expose] public section

/-!
# The branch and bound loop encloses the range

Whatever the selection of boxes and however many steps run, the boxes cover the domain (each split
keeps the cover, `splitAt_covers`), so a point lies in some box, whose interval holds the value,
and the union holds that interval. The soundness of [1, Alg. 1] for any sound way `bnd` of bounding
a box.

## Inputs
* `bnd` – bounding function on a box
* `g` – bounded function
* `ε` – tolerance
* `X` – domain box
* `t` – point

## Hypotheses
* `hb` – bounds hold on every box containing the point
* `ht` – point lies in the domain box

## Conclusion
* the loop's enclosure contains the function's value at the point

## References

* [1] M. Althoff, D. Grebenyuk and N. Kochdumper. "Implementation of Taylor Models in CORA 2018".
      ARCH18. 5th International Workshop on Applied Verification of Continuous and Hybrid Systems,
      2018.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   14-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Taylm.bnbLoop_mem {bnd : (Fin n → Interval ℝ) → Interval ℝ} {g : Vec ℝ n → ℝ}
    (hb : ∀ B t, Taylm.IsInBox B t → (bnd B).inf ≤ g t ∧ g t ≤ (bnd B).sup) (ε : ℝ)
    {X : Fin n → Interval ℝ} {t : Vec ℝ n} (ht : Taylm.IsInBox X t) : -- --- CONCL ---
    ∀ (fuel : ℕ) (l : List (Fin n → Interval ℝ)), Taylm.Covers X l →
      (Taylm.bnbLoop bnd ε fuel l).inf ≤ g t ∧
        g t ≤ (Taylm.bnbLoop bnd ε fuel l).sup := by -- --- PROOF ---
  -- the union of a covering list holds the value
  have hunion : ∀ l, Taylm.Covers X l →
      Taylm.listMin (fun B => (bnd B).inf) l ≤ g t ∧ g t ≤ Taylm.listMax (fun B => (bnd B).sup) l :=
          by
    intro l hl
    obtain ⟨B, hB, htB⟩ := hl t ht
    have := hb B t htB
    exact ⟨le_trans (Taylm.listMin_le (fun B => (bnd B).inf) hB) this.1,
      le_trans this.2 (Taylm.le_listMax (fun B => (bnd B).sup) hB)⟩
  -- a step keeps the cover
  have hstep : ∀ l, Taylm.Covers X l → Taylm.Covers X (Taylm.bnbStep bnd l) := by
    intro l hl
    simp only [Taylm.bnbStep]
    split_ifs
    · exact Taylm.splitAt_covers _ hl
    · exact Taylm.splitAt_covers _ (Taylm.splitAt_covers _ hl)
  intro fuel
  induction fuel with
  | zero => intro l hl; exact hunion l hl
  | succ k ih =>
    intro l hl
    simp only [Taylm.bnbLoop]
    split_ifs
    · exact hunion _ (hstep l hl)
    · exact ih _ (hstep l hl)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
