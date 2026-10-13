import CORALean.ContSet.HPolytope.Float.HPolytope

/-!
# `HPolytope.restrict`, over a floating-point scalar

The rows of a polytope picked by two Boolean tests, in their order: CORA's `A(idx,:)`, `b(idx)`,
`Ae(idx,:)`, `be(idx)`, which every step of `compact_` ends with. The others are deleted;
`mem_restrict_iff` says what is left. Nothing rounds.
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The inequality rows `i` with `keepA i` and the equality rows `r` with `keepE r`. -/
def HPolytope.restrict (P : HPolytope 𝕋 (Vec 𝕋 n)) (keepA : Fin P.m → Bool)
    (keepE : Fin P.me → Bool) :
    HPolytope 𝕋 (Vec 𝕋 n) where
  m := ((List.finRange P.m).filter keepA).length
  A := fun k => P.A (((List.finRange P.m).filter keepA).get k)
  b := fun k => P.b (((List.finRange P.m).filter keepA).get k)
  me := ((List.finRange P.me).filter keepE).length
  Ae := fun k => P.Ae (((List.finRange P.me).filter keepE).get k)
  be := ⟨fun k => P.be.inf (((List.finRange P.me).filter keepE).get k),
    fun k => P.be.sup (((List.finRange P.me).filter keepE).get k)⟩

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
