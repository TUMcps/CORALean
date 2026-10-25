module

public import CORALean.ContSet.HPolytope.Float.Theorems.MemConstruct
public import CORALean.ContSet.HPolytope.Float.Theorems.AbsorbRoundingOuter
public import CORALean.ContSet.HPolytope.Float.Theorems.ReduceOverDomainRows
public import CORALean.ContSet.HPolytope.Float.Theorems.RowScalePos

@[expose] public section

/-!
# The float `'outer'` reduction keeps every point of the polytope in the domain

A point of `P` in the domain meets row `0` of `P`; scaled by the row's positive `rowScale` it
still does, and the scaled row is the reduced row plus the deviation that
`reduceOverDomain_rows` bounds from below. So the reduced row stays under the upper end of the
scaled right-hand sides less the lower end of the deviation, which is the stored bound. Outer
over the domain, as over ℝ, for a polytope with a row.

## Inputs
* `p` – natural number
* `P` – H-polytope
* `dom` – domain interval

## Hypotheses
* `hm` – `0 < P.m`

## Conclusion
* the float `'outer'` reduction keeps every point of the polytope in the domain
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   15-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Matrix FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem HPolytope.reduceOverDomain_outer (p : ℕ) (P : HPolytope 𝕋 (Vec 𝕋 n)) (hm : 0 < P.m)
    (dom : Interval (Vec 𝕋 n)) : -- --- CONCL ---
    P.construct ∩ dom.construct ⊆
      (P.reduceOverDomain p dom true).construct ∩ dom.construct := by -- --- PROOF ---
  rintro x ⟨hP, hd⟩
  refine ⟨(HPolytope.mem_construct_iff (HPolytope.errFree_of_origin rfl rfl rfl)).mpr
    ⟨fun _ => ?_, fun r => r.elim0⟩, hd⟩
  -- the rows are read with the error box folded in
  have hQ := HPolytope.absorbRounding_outer P hP
  have hmQ : 0 < P.absorbRounding.m := by
    show 0 < P.m + (P.me + P.me)
    omega
  simp only [HPolytope.reduceOverDomain, if_true]
  set Q := P.absorbRounding with hQdef
  have hQe : Q.IsErrFree := HPolytope.errFree_of_origin rfl rfl rfl
  set i₀ : Fin Q.m := ⟨0, hmQ⟩
  set Ainf : Vec 𝕋 n := fun j => minimumOver fun i => mulDown (Q.A i j) (Q.rowScale p i)
  set Asup : Vec 𝕋 n := fun j => maximumOver fun i => mulUp (Q.A i j) (Q.rowScale p i)
  set bSup : 𝕋 := maximumOver fun i => mulUp (Q.b i) (Q.rowScale p i)
  set Ared : Vec 𝕋 n := fun j => half (addDown (Ainf j) (Asup j))
  set prodInf : 𝕋 := sumDown fun j =>
    Interval.mulLo (subDown (Ainf j) (Ared j)) (subUp (Asup j) (Ared j)) (dom.inf j) (dom.sup j)
  obtain ⟨hlo, -⟩ := HPolytope.reduceOverDomain_rows p Q dom hd i₀
  -- row `0`, scaled by its positive scale, and its right-hand side under the hull's top
  have hrow := ((HPolytope.mem_construct_iff hQe).mp hQ).1 i₀
  have hS := HPolytope.rowScale_pos p Q i₀
  have hscaled := mul_le_mul_of_nonneg_left hrow hS.le
  have hb1 := mul_le_mulUp (Q.b i₀) (Q.rowScale p i₀)
  have hb2 := le_maximumOver (fun i => mulUp (Q.b i) (Q.rowScale p i)) i₀
  have hsub := sub_le_subUp bSup prodInf
  -- the reduced row is the scaled row less the deviation
  have hsplit : ∑ j, toReal (Ared j) * x j = toReal (Q.rowScale p i₀) * (toRealMat Q.A *ᵥ x) i₀
      - ∑ j, (toReal (Q.rowScale p i₀) * toReal (Q.A i₀ j) - toReal (Ared j)) * x j := by
    simp only [mulVec, dotProduct, toRealMat, Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun j _ => by ring
  show ∑ j, toReal (Ared j) * x j ≤ toReal (subUp bSup prodInf)
  simp only [bSup] at hb2 hsub
  linarith

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
