import CORALean.ContSet.Fullspace.Real.Operations.Volume

/-!
# `Fullspace.volume` is the Lebesgue volume

`Inf`, CORA's value, is the volume of the whole space in positive dimension. At `n = 0` the
space is a point of volume `1` while CORA answers `NaN`; that case is not claimed.
-/

-- Authors:       Tobias Ladner
-- Written:       01-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n m : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Fullspace.volume_eq (hn : 0 < n) (F : Fullspace n) :
    MeasureTheory.volume (F.construct) = F.volume := by -- --- PROOF ---
  change MeasureTheory.volume (Set.univ : Set (Vec ℝ n)) = ⊤
  have h : (Set.univ : Set (Vec ℝ n)) = Set.univ.pi fun _ : Fin n => (Set.univ : Set ℝ) := by
    ext x; simp
  rw [h, MeasureTheory.volume_pi_pi]
  simp only [Real.volume_univ]
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  exact ENNReal.top_pow hn.ne'

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
