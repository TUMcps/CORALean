module

public import CORALean.ContSet.ConPolyZono.Real.Operations.Relax
public import CORALean.ContSet.PolyZonotope.Real.Operations.MonomialIdentE
public import CORALean.ContSet.PolyZonotope.Real.Theorems.MonomialPlusELeft
public import CORALean.ContSet.PolyZonotope.Real.Theorems.MonomialPlusERight
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Data.Matrix.Mul

@[expose] public section

/-!
# A row of `ConPolyZono.relax`

Row `i` of the relaxed system is the original row at the original factors plus `sᵢ γᵢ`: the
slack factors' monomials are the factors themselves (`identE`), and row `i`'s coefficient on
them is `sᵢ` at `γᵢ` alone.
-/

-- Authors:       Claude Opus 5.5
-- Written:       18-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {α : Type}


-- =======================================  MAIN THEOREM  ======================================= --

/-- A row of the relaxed system: the original row, plus the slack its own factor carries. -/
theorem ConPolyZono.mulVec_relax (cPZ : ConPolyZono α) (s : Vec ℝ cPZ.m)
    (a : Fin (cPZ.p + cPZ.m) → ℝ) (i : Fin cPZ.m) : -- --- STMT ---
    ((cPZ.relax s).A *ᵥ PolyZonotope.monomial (cPZ.relax s).R a) i
      = (cPZ.A *ᵥ PolyZonotope.monomial cPZ.R (fun k => a (Fin.castAdd cPZ.m k))) i
        + s i * a (Fin.natAdd cPZ.p i) := by -- --- PROOF ---
  show ∑ l : Fin (cPZ.q + cPZ.m), Fin.append (cPZ.A i) (Pi.single i (s i)) l
      * PolyZonotope.monomial (PolyZonotope.plusE cPZ.R (PolyZonotope.identE cPZ.m)) a l = _
  rw [Fin.sum_univ_add]
  simp only [Fin.append_left, Fin.append_right, PolyZonotope.monomial_plusE_left,
    PolyZonotope.monomial_plusE_right, PolyZonotope.monomial_identE]
  congr 1
  -- the slack columns: only row `i`'s own factor has a nonzero coefficient
  rw [Finset.sum_eq_single i (fun r _ hr => by rw [Pi.single_eq_of_ne hr, zero_mul])
    (fun h => absurd (Finset.mem_univ i) h), Pi.single_eq_same]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
