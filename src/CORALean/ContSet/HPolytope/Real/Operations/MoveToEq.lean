module

public import CORALean.ContSet.HPolytope.Real.HPolytope
public import CORALean.ContSet.HPolytope.Real.Operations.Restrict

@[expose] public section

/-!
# `HPolytope.moveToEq`

Keep the inequality rows indexed by `S`, and turn the rows listed in `L` into equality rows
appended after the existing ones: CORA's `Ae = [Ae; A(i,:)]`, `be = [be; b(i)]` followed by
`A = A(~idxMoveToEq,:)` in `priv_compact_toEquality`.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =====================================  MAIN DEFINITION  ====================================== --

noncomputable def HPolytope.moveToEq (P : HPolytope α) (S : Finset (Fin P.m))
    (L : List (Fin P.m)) : HPolytope α where
  m := S.card
  A := fun k => P.A (S.equivFin.symm k).1
  b := fun k => P.b (S.equivFin.symm k).1
  me := P.me + L.length
  Ae := Fin.append P.Ae fun k => P.A (L.get k)
  be := Fin.append P.be fun k => P.b (L.get k)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
