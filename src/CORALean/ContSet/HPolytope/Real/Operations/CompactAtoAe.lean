module

public import CORALean.ContSet.HPolytope.Real.HPolytope
public import Mathlib.Data.List.FinRange
public import Mathlib.Data.Finset.Basic
public import CORALean.ContSet.HPolytope.Real.Operations.Restrict
public import CORALean.ContSet.HPolytope.Real.Operations.NormalizeRows

@[expose] public section

/-!
# `HPolytope.compactAtoAe`

CORA's `compact_(P, 'AtoAe')`: after the unit normalization of `compact_` (`normalizeRows`),
every pair of inequality rows `aᵀx ≤ b`, `-aᵀx ≤ -b` becomes the equality `aᵀx = b`
(`priv_compact_toEquality`, its loop in `aux_atoAeState`), the rows moved are deleted from the
inequalities and the equalities are appended (`aux_moveToEq`).

The test for an inverted pair is exact equality of `[a, b]` and `-[a', b']`; CORA's is
`withinTol(sum, 0, tol)` entrywise, at the default `tol = 1e-9`. The emptiness and fullspace
exits at the end of CORA's `compact_` are not needed here, an empty row set being the fullspace.

## Inputs
* `P` – H-polytope

## Output
* `P` normalized, with each inverted inequality pair turned into an equality
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open scoped Classical

variable {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

section
variable {α : Type} [AddCommGroup α] [Module ℝ α]

noncomputable def HPolytope.aux_moveToEq (P : HPolytope α) (S : Finset (Fin P.m))
    (L : List (Fin P.m)) : HPolytope α where
  m := S.card
  A := fun k => P.A (S.equivFin.symm k).1
  b := fun k => P.b (S.equivFin.symm k).1
  me := P.me + L.length
  Ae := Fin.append P.Ae fun k => P.A (L.get k)
  be := Fin.append P.be fun k => P.b (L.get k)

end


section
variable {α : Type} [AddCommGroup α] [Module ℝ α]

noncomputable def HPolytope.aux_atoAeState (Q : HPolytope α) : Finset (Fin Q.m) × List (Fin Q.m) :=
  (List.finRange Q.m).foldl
    (fun st i =>
      if i ∈ st.1 then st
      else
        let idxInverted := Finset.univ.filter fun j => Q.A j = -Q.A i ∧ Q.b j = -Q.b i
        if idxInverted.Nonempty then (st.1 ∪ idxInverted ∪ {i}, st.2 ++ [i]) else st)
    (∅, [])

end


-- =====================================  MAIN DEFINITION  ====================================== --

noncomputable def HPolytope.compactAtoAe (P : HPolytope (Vec ℝ n)) : HPolytope (Vec ℝ n) :=
  let Q := P.normalizeRows
  let st := Q.aux_atoAeState
  Q.aux_moveToEq (Finset.univ.filter fun i => i ∉ st.1) st.2

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
