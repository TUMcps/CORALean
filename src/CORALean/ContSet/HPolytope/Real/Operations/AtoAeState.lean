module

public import CORALean.ContSet.HPolytope.Real.HPolytope
public import Mathlib.Data.List.FinRange
public import Mathlib.Data.Finset.Basic

@[expose] public section

/-!
# `HPolytope.atoAeState`

The loop of CORA's `priv_compact_toEquality`: over the inequality rows `i = 1, …, m` in order,
skip the row if it has been matched already; otherwise look for the rows `j` with an inverted
`[aⱼ, bⱼ] = -[aᵢ, bᵢ]` (`idxInverted`, which includes `i` itself for a row `0 ≤ 0`), and if
there is one, mark all of them and `i` as moved (`idxMoveToEq`) and append `[aᵢ, bᵢ]` to the
equality rows. The state is the set of moved rows and the list of rows appended, in order. A row
`i` that has an inverted partner already moved by an earlier row, but is not itself marked, is
appended again, as CORA does.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open scoped Classical

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =====================================  MAIN DEFINITION  ====================================== --

noncomputable def HPolytope.atoAeState (Q : HPolytope α) : Finset (Fin Q.m) × List (Fin Q.m) :=
  (List.finRange Q.m).foldl
    (fun st i =>
      if i ∈ st.1 then st
      else
        let idxInverted := Finset.univ.filter fun j => Q.A j = -Q.A i ∧ Q.b j = -Q.b i
        if idxInverted.Nonempty then (st.1 ∪ idxInverted ∪ {i}, st.2 ++ [i]) else st)
    (∅, [])

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
