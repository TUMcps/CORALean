module

public import CORALean.ContSet.HPolytope.Float.Operations.ReduceOverDomain
public import CORALean.ContSet.Interval.Float.Theorems.MulBetweenCorners

@[expose] public section

/-!
# Every scaled row is within the reduced row's reach over the domain

For a point of the domain and any row `i` scaled by its `rowScale` `S`, the deviation
`Σⱼ (S Aᵢⱼ - A_reducedⱼ) xⱼ` lies between the two rounded ends of `(A - A_reduced)' * dom`: each
scaled entry is inside the rounded hull `A` (`minimumOver_le`, `le_maximumOver`), so its
deviation from `A_reduced` is inside the rounded difference, and each product inside its rounded
corners (`mul_between_corners`). The float counterpart of the exact layer's
`reduceOverDomain_rows`; `reduceOverDomain_outer` and `reduceOverDomain_inner` both read it.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem HPolytope.reduceOverDomain_rows (p : ℕ) (P : HPolytope 𝕋 (Vec 𝕋 n))
    (dom : Interval (Vec 𝕋 n))
    {x : Vec ℝ n} (hx : x ∈ dom.construct) (i : Fin P.m) :
    let Ainf : Vec 𝕋 n := fun j => minimumOver fun i => mulDown (P.A i j) (P.rowScale p i)
    let Asup : Vec 𝕋 n := fun j => maximumOver fun i => mulUp (P.A i j) (P.rowScale p i)
    let Ared : Vec 𝕋 n := fun j => half (addDown (Ainf j) (Asup j))
    toReal (sumDown fun j => Interval.mulLo (subDown (Ainf j) (Ared j))
        (subUp (Asup j) (Ared j)) (dom.inf j) (dom.sup j))
      ≤ ∑ j, (toReal (P.rowScale p i) * toReal (P.A i j) - toReal (Ared j)) * x j
    ∧ ∑ j, (toReal (P.rowScale p i) * toReal (P.A i j) - toReal (Ared j)) * x j
      ≤ toReal (sumUp fun j => Interval.mulHi (subDown (Ainf j) (Ared j))
        (subUp (Asup j) (Ared j)) (dom.inf j) (dom.sup j)) := by -- --- PROOF ---
  intro Ainf Asup Ared
  -- each scaled entry's deviation from the reduced row, inside its rounded difference
  have hdev : ∀ j, toReal (subDown (Ainf j) (Ared j))
        ≤ toReal (P.rowScale p i) * toReal (P.A i j) - toReal (Ared j)
      ∧ toReal (P.rowScale p i) * toReal (P.A i j) - toReal (Ared j)
        ≤ toReal (subUp (Asup j) (Ared j)) := by
    intro j
    have h1 := minimumOver_le (fun i => mulDown (P.A i j) (P.rowScale p i)) i
    have h2 := le_maximumOver (fun i => mulUp (P.A i j) (P.rowScale p i)) i
    have h3 := mulDown_le_mul (P.A i j) (P.rowScale p i)
    have h4 := mul_le_mulUp (P.A i j) (P.rowScale p i)
    have h5 := subDown_le_sub (Ainf j) (Ared j)
    have h6 := sub_le_subUp (Asup j) (Ared j)
    simp only [Ainf, Asup] at h5 h6 ⊢
    constructor <;> linarith
  have hxj : ∀ j, toReal (dom.inf j) ≤ x j ∧ x j ≤ toReal (dom.sup j) := hx
  -- each product inside its rounded corners, then the sums rounded once more
  have hprod := fun j => Interval.mul_between_corners (hdev j).1 (hdev j).2 (hxj j).1 (hxj j).2
  exact ⟨le_trans (sumDown_le_sum _) (Finset.sum_le_sum fun j _ => (hprod j).1),
    le_trans (Finset.sum_le_sum fun j _ => (hprod j).2) (sum_le_sumUp _)⟩

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
