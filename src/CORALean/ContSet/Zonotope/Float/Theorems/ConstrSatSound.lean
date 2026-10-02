import CORALean.ContSet.Zonotope.Float.Operations.ConstrSat
import CORALean.ContSet.Zonotope.Float.Theorems.MtimesOuter
import CORALean.ContSet.Conversion.Float.Zonotope_to_Interval

/-!
# `constrSat` is sound at float

The rounded image `Zonotope.mtimes C Z` contains the real image (`mtimes_outer`), its rounded
box contains that (`interval_contains`), and `ltStrict` on the box's upper bound is a strict
inequality between the real values.
-/

-- Authors:       Tobias Ladner
-- Written:       02-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic Matrix

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n m : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zonotope.constrSat_sound {Z : Zonotope 𝕋 n} {C : Mat 𝕋 m n} {d : Vec 𝕋 m}
    (h : Zonotope.constrSat Z C d = true) :
    ∀ x ∈ Z.construct, ∀ i, (toRealMat C *ᵥ x) i < toReal (d i) := by -- --- PROOF ---
  intro x hx i
  have hmem := (Zonotope.mtimes C Z).interval_contains (Zonotope.mtimes_outer C Z ⟨x, hx, rfl⟩)
  have hle := (hmem i).2
  simp only [Zonotope.constrSat, List.all_eq_true, List.mem_finRange, forall_const] at h
  have := toReal_lt_of_ltStrict (h i)
  exact lt_of_le_of_lt hle this

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
