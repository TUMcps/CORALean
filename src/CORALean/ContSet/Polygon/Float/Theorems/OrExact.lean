import CORALean.ContSet.Polygon.Float.Operations.Or

/-!
# `Polygon.or` is the union

Exactly: the pieces of both.
-/

-- Authors:       Tobias Ladner
-- Written:       02-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Pointwise FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋]


-- =======================================  MAIN THEOREM  ======================================= --

theorem Polygon.or_exact (P Q : Polygon 𝕋) :
    ContSet.construct P ∪ ContSet.construct Q =
      ContSet.construct (Polygon.or P Q) := by -- --- PROOF ---
  ext x
  simp only [Set.mem_union, SetUnion.mem_construct, Polygon.or, List.mem_append]
  constructor
  · rintro (⟨s, hs, hx⟩ | ⟨s, hs, hx⟩)
    · exact ⟨s, Or.inl hs, hx⟩
    · exact ⟨s, Or.inr hs, hx⟩
  · rintro ⟨s, hs | hs, hx⟩
    · exact Or.inl ⟨s, hs, hx⟩
    · exact Or.inr ⟨s, hs, hx⟩

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
