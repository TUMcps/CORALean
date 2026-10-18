module

public import CORALean.ContSet.HPolytope.Float.Theorems.MemConstruct
public import CORALean.ContSet.HPolytope.Float.Theorems.ReduceOverDomainRows
public import CORALean.ContSet.HPolytope.Float.Theorems.RowScalePos

@[expose] public section

/-!
# A point under the float inner reduction meets every row of the polytope in the domain

For a point of the domain under the reduced row with the lower bound, every row `i` scaled by
its positive `rowScale` is the reduced row plus a deviation that `reduceOverDomain_rows` bounds
from above, so it stays under the lower end of the scaled right-hand sides, which is under row
`i`'s own scaled right-hand side; dividing by the scale gives the row. Inner over the domain,
as over ℝ, for a polytope without equality rows and without an error box: a box would enlarge the
polytope, and an inner statement cannot read it as an outer one.
-/

-- Authors:       Claude Opus 5.5, Claude Sonnet 5.5
-- Written:       04-October-2026
-- Last update:   15-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Matrix FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem HPolytope.reduceOverDomain_inner (p : ℕ) (P : HPolytope 𝕋 (Vec 𝕋 n)) (hP : P.ErrFree)
    (hme : P.me = 0)
    (dom : Interval (Vec 𝕋 n)) : -- --- STMT ---
    (P.reduceOverDomain p dom false).construct ∩ dom.construct ⊆
      P.construct ∩ dom.construct := by -- --- PROOF ---
  rintro x ⟨hR, hd⟩
  refine ⟨(HPolytope.mem_construct_iff hP).mpr ⟨fun i => ?_, fun r => absurd r.isLt (by omega)⟩, hd⟩
  set Ainf : Vec 𝕋 n := fun j => minimumOver fun i => mulDown (P.A i j) (P.rowScale p i)
  set Asup : Vec 𝕋 n := fun j => maximumOver fun i => mulUp (P.A i j) (P.rowScale p i)
  set bInf : 𝕋 := minimumOver fun i => mulDown (P.b i) (P.rowScale p i)
  set Ared : Vec 𝕋 n := fun j => half (addDown (Ainf j) (Asup j))
  set prodSup : 𝕋 := sumUp fun j =>
    Interval.mulHi (subDown (Ainf j) (Ared j)) (subUp (Asup j) (Ared j)) (dom.inf j) (dom.sup j)
  obtain ⟨-, hhi⟩ := HPolytope.reduceOverDomain_rows p P dom hd i
  -- the reduced row, under its stored lower bound
  have hred : ∑ j, toReal (Ared j) * x j ≤ toReal (subDown bInf prodSup) :=
    ((HPolytope.mem_construct_iff (HPolytope.errFree_of_origin rfl rfl rfl)).mp hR).1
      (⟨0, Nat.one_pos⟩ : Fin 1)
  have hsub := subDown_le_sub bInf prodSup
  -- the scaled right-hand side is above the hull's bottom
  have hS := HPolytope.rowScale_pos p P i
  have hb1 := mulDown_le_mul (P.b i) (P.rowScale p i)
  have hb2 := minimumOver_le (fun i => mulDown (P.b i) (P.rowScale p i)) i
  -- the scaled row is the reduced row plus the deviation
  have hsplit : toReal (P.rowScale p i) * (toRealMat P.A *ᵥ x) i = ∑ j, toReal (Ared j) * x j
      + ∑ j, (toReal (P.rowScale p i) * toReal (P.A i j) - toReal (Ared j)) * x j := by
    simp only [mulVec, dotProduct, toRealMat, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j _ => by ring
  simp only [bInf] at hb2 hsub hred
  have hscaled : toReal (P.rowScale p i) * (toRealMat P.A *ᵥ x) i
      ≤ toReal (P.rowScale p i) * toReal (P.b i) := by
    rw [mul_comm (toReal (P.b i)) (toReal (P.rowScale p i))] at hb1
    linarith
  exact le_of_mul_le_mul_left hscaled hS

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
