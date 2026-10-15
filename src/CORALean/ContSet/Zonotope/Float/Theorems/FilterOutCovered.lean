module

public import CORALean.ContSet.Zonotope.Float.Operations.FilterOut
public import CORALean.ContSet.Zonotope.Float.Theorems.ContainsZonotopeSound

@[expose] public section

/-!
# A deleted cell lies in another cell

A cell `Zonotope.filterOut` deletes is certified by `Zonotope.containsZonotope` to lie in one other
cell, so its set (center, generators and error box) is inside that cell's. This is the float
counterpart of `Zonotope.filterOut_covered`, with the cover a single cell rather than the union of
all the others, and without the interior hypothesis: the certificate covers the cell itself.

Source: [1].

## References

* [1] `contSet/@zonotope/filterOut.m`, CORA (Sep. 2025), by M. Althoff (2008). No paper behind the
      rule was confirmed.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       10-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n m : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zonotope.filterOut_covered (Zs : Fin m → Zonotope (Vec 𝕋 n)) (ind : Fin m)
    (hout : ind ∉ Zonotope.filterOut Zs) :
    ∃ j, j ≠ ind ∧ (Zs ind).construct ⊆ (Zs j).construct := by -- --- PROOF ---
  -- unfold the filter: some other cell passes the containment certificate
  simp only [Zonotope.filterOut, Finset.mem_filter, Finset.mem_univ, true_and,
    List.all_eq_true, List.mem_finRange, forall_const, Bool.or_eq_true, decide_eq_true_eq,
    Bool.not_eq_true', not_forall] at hout
  obtain ⟨j, hj⟩ := hout
  simp only [not_or, Bool.not_eq_false] at hj
  exact ⟨j, hj.1, Zonotope.containsZonotope_sound hj.2⟩

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
