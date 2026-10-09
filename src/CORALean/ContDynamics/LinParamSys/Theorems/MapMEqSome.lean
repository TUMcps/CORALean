import Mathlib.Data.Nat.Notation

/-!
# A successful `mapM` into `Option` has one result per entry

The windows `reachFloat` and its input variants return come from a `mapM` over
`List.range N`; this reads off the length and each entry's own computation.
-/

-- Authors:       Tobias Ladner
-- Written:       08-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =======================================  MAIN THEOREM  ======================================= --

/-- A `mapM` into `Option` that succeeds has one result per entry, each the
function's value there. -/
theorem LinParamSys.mapM_eq_some {α β : Type} {f : α → Option β} :
    ∀ {l : List α} {l' : List β}, l.mapM f = some l' →
      ∃ hlen : l'.length = l.length, ∀ (i : ℕ) (hi : i < l'.length),
        f (l[i]'(hlen ▸ hi)) = some l'[i] := by -- --- PROOF ---
  intro l
  induction l with
  | nil =>
    intro l' h
    simp only [List.mapM_nil, Option.pure_def, Option.some.injEq] at h
    subst h
    exact ⟨rfl, fun i hi => absurd hi (Nat.not_lt_zero i)⟩
  | cons a l ih =>
    intro l' h
    simp only [List.mapM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨b, hb, bs, hbs, rfl⟩ := h
    obtain ⟨hlen, hget⟩ := ih hbs
    -- the head is `f a`, the tail the induction's
    refine ⟨by simp [hlen], fun i hi => ?_⟩
    cases i with
    | zero => exact hb
    | succ i => exact hget i (Nat.lt_of_succ_lt_succ hi)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
