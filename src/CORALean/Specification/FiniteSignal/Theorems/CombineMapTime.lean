module

public import CORALean.Specification.FiniteSignal.Operations.Combine
public import CORALean.Specification.FiniteSignal.Theorems.Basic
public import CORALean.Specification.FiniteSignal.Theorems.MkMapTime

@[expose] public section

/-!
# Combining float signals, read as reals

Over a float scalar `𝕋` the loop of `combine` compares the next breakpoints of the two signals
exactly (`TimeOrder`), so it takes the same steps as over the reals the stamps denote: the combined
float signal read through `toReal` is the combination of the two real signals.

## Inputs
* `V` – value type
* `W` – result value type
* `op` – value combination
* `sigs` – signals to combine

## Hypotheses
* none

## Conclusion
* the float combination, read as reals, is the real combination
-/

-- Authors:       Claude Opus 5.5
-- Written:       23-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Float SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] [ExactLe 𝕋]


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

omit [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] [ExactLe 𝕋] in
/-- Mapping the time stamps maps the first component of each breakpoint. -/
private theorem aux_pairs_mapTime {T' V : Type} (f : 𝕋 → T') (s : FiniteSignal 𝕋 V) :
    (s.mapTime f).pairs = s.pairs.map (Prod.map f id) := List.zip_map_left

omit [ExactLe 𝕋] in
/-- `combineEmit` reads no time stamp: it commutes with mapping them. -/
private theorem aux_combineEmit_mapTime {V W : Type} [DecidableEq W] (op : V → V → W) (t : 𝕋)
    (v : W) (ls rs : List (𝕋 × V)) (rest : List (𝕋 × W)) : -- --- CONCL ---
    (FiniteSignal.combineEmit op t v ls rs rest).map (Prod.map toReal id) =
      FiniteSignal.combineEmit op (toReal t) v (ls.map (Prod.map toReal id))
        (rs.map (Prod.map toReal id)) (rest.map (Prod.map toReal id)) := by -- --- PROOF ---
  unfold FiniteSignal.combineEmit
  rcases ls with _ | ⟨l', ls⟩ <;> rcases rs with _ | ⟨r', rs⟩ <;>
    simp only [List.map_cons, List.map_nil] <;> try rfl
  split_ifs <;> simp_all

/-- The loop takes the same branch on the float breakpoints as on the reals they denote. -/
private theorem aux_combineLoop_mapTime {V W : Type} [DecidableEq W] (op : V → V → W)
    (ls rs : List (𝕋 × V)) : -- --- CONCL ---
    (FiniteSignal.combineLoop op ls rs).map (Prod.map toReal id) =
      FiniteSignal.combineLoop op (ls.map (Prod.map toReal id))
        (rs.map (Prod.map toReal id)) := by -- --- PROOF ---
  fun_induction FiniteSignal.combineLoop op ls rs with
  | case1 l ls r rs h ih =>
    -- the left signal makes progress
    rw [aux_combineEmit_mapTime, ih, List.map_cons, List.map_cons, FiniteSignal.combineLoop.eq_1]
    simp only [Prod.map_fst, Prod.map_snd, id_eq]
    rw [if_pos (show toReal l.1 < toReal r.1 from h)]
  | case2 l ls r rs h1 h2 ih =>
    -- both signals make progress
    rw [aux_combineEmit_mapTime, ih, List.map_cons, List.map_cons, FiniteSignal.combineLoop.eq_1]
    simp only [Prod.map_fst, Prod.map_snd, id_eq]
    rw [if_neg (show ¬ toReal l.1 < toReal r.1 from h1),
      if_pos (show TimeOrder.Eqv (toReal l.1) (toReal r.1) from h2)]
  | case3 l ls r rs h1 h2 ih =>
    -- the right signal makes progress
    rw [aux_combineEmit_mapTime, ih, List.map_cons, List.map_cons, FiniteSignal.combineLoop.eq_1]
    simp only [Prod.map_fst, Prod.map_snd, id_eq]
    rw [if_neg (show ¬ toReal l.1 < toReal r.1 from h1),
      if_neg (show ¬ TimeOrder.Eqv (toReal l.1) (toReal r.1) from h2)]
  | case4 ls rs h =>
    -- a signal is used up
    rcases ls with _ | ⟨l, ls⟩
    · simp [FiniteSignal.combineLoop]
    · rcases rs with _ | ⟨r, rs⟩
      · simp [FiniteSignal.combineLoop]
      · exact absurd rfl (h l ls r rs rfl)


-- =======================================  MAIN THEOREM  ======================================= --

theorem FiniteSignal.combine?_mapTime {V W : Type} [DecidableEq W] (op : V → V → W)
    (sigs : List (FiniteSignal 𝕋 V)) :
    (FiniteSignal.combine? op sigs).map (FiniteSignal.mapTime toReal) =
      FiniteSignal.combine? op (sigs.map (FiniteSignal.mapTime toReal)) := by
  rcases sigs with _ | ⟨lhs, _ | ⟨rhs, _ | ⟨x, xs⟩⟩⟩ <;> try rfl
  simp only [FiniteSignal.combine?, List.map_cons, List.map_nil, aux_pairs_mapTime,
    ← aux_combineLoop_mapTime, FiniteSignal.mk?_mapTime, List.map_map]
  rfl

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
