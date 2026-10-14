module

public import CORALean.ContSet.Conversion.Real.Operations.Interval_to_Zonotope
public import CORALean.ContSet.PolyZonotope.Real.PolyZonotope
public import CORALean.ContSet.Taylm.Real.Taylm
public import CORALean.ContSet.Taylm.Real.Theorems.PolyOfCons
public import CORALean.ContSet.Taylm.Real.Theorems.PolyOfNil
public import CORALean.ContSet.Conversion.Real.Operations.Taylm_to_PolyZonotope

@[expose] public section

/-!
# An array of Taylor models as a polynomial zonotope: `indep_apply`
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n m : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Taylm.indep_apply (T : Fin m → Taylm n) (β : Fin (Taylm.polyZonotope T).q → ℝ)
    (i : Fin m) :
    (∑ l, β l • (Taylm.polyZonotope T).GI l) i
      = β i * (((T i).remSup - (T i).remInf) / 2) := by -- --- PROOF ---
  change (∑ l : Fin m, β l • (Pi.single l (((T l).remSup - (T l).remInf) / 2) : Vec ℝ m)) i = _
  rw [Finset.sum_apply, Finset.sum_eq_single i]
  · simp
  · intro l _ hl; simp [Ne.symm hl]
  · intro h; exact absurd (Finset.mem_univ i) h

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
