module

public import CORALean.ContSet.HPolytope.Float.Operations.SelectCols
public import CORALean.ContSet.HPolytope.Float.Theorems.MemNominalIff

@[expose] public section

/-!
# What `HPolytope.selectCols` reads

At a point the rows read through `sel` alone, the selected rows read the selected coordinates as
the full rows read the point, so the two nominal parts agree on it, row by row.
-/

-- Authors:       Claude Opus 5.5
-- Written:       19-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Matrix SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n k : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- A point the rows read through `sel` alone is in the nominal part exactly when its selected
coordinates are in the selected one. -/
theorem HPolytope.mem_selectCols_nominal_iff (P : HPolytope 𝕋 (Vec 𝕋 n)) (sel : Fin k → Fin n)
    {x : Vec ℝ n}
    (hA : ∀ i, (toRealMat P.A *ᵥ x) i = ∑ l, toReal (P.A i (sel l)) * x (sel l))
    (hE : ∀ i, (toRealMat P.Ae *ᵥ x) i =
      ∑ l, toReal (P.Ae i (sel l)) * x (sel l)) : -- --- CONCL ---
    (fun l => x (sel l)) ∈ (P.selectCols sel).nominal.construct
      ↔ x ∈ P.nominal.construct := by -- --- PROOF ---
  rw [HPolytope.mem_nominal_iff, HPolytope.mem_nominal_iff]
  -- the selected rows at the selected coordinates are the full rows at the point
  have hA' : ∀ i, (toRealMat (P.selectCols sel).A *ᵥ fun l => x (sel l)) i
      = (toRealMat P.A *ᵥ x) i := fun i => (hA i).symm
  have hE' : ∀ i, (toRealMat (P.selectCols sel).Ae *ᵥ fun l => x (sel l)) i
      = (toRealMat P.Ae *ᵥ x) i := fun i => (hE i).symm
  simp only [hA', hE']
  rfl

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
