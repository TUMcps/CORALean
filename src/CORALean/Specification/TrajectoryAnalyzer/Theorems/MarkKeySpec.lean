module

public import CORALean.Global.LookupReplaceKey
public import CORALean.Global.ReplaceKey
public import CORALean.Specification.FiniteKleeneSignalBuilder.Theorems.OrIndicatorSpec
public import CORALean.Specification.TrajectoryAnalyzer.Definitions.SignalsRepresent
public import CORALean.Specification.TrajectoryAnalyzer.Operations.MarkKey

@[expose] public section

/-!
# What marking a proposition does

If the signals represent `M` and `lo < hi`, marking proposition `k` of the analyzer on the interval
`[lo,hi)` succeeds and the signals then represent `M` plus, for `k` only, the times the interval
covers (`Covers`).

## Inputs
* `aps` – labelled atomic propositions
* `dur` – signal duration
* `sigs` – signal of each proposition
* `M` – times marking each proposition
* `lo` – interval lower bound
* `hi` – interval upper bound
* `p` – proposition with its key

## Hypotheses
* `h` – the signals represent the marked times
* `hlh` – the interval is proper
* `hp` – the proposition belongs to the list

## Conclusion
* marking succeeds and adds the interval to the proposition's times
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open FiniteKleeneSignalBuilder

variable {S : ℕ → Type} {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- Replacing a key keeps the keys. -/
private theorem aux_map_fst_replaceKey {β : Type} (l : List (String × β)) (k : String)
    (v : β) : -- --- CONCL ---
    (replaceKey l k v).map Prod.fst = l.map Prod.fst := by -- --- PROOF ---
  induction l with
  | nil => rfl
  | cons p l ih =>
    simp only [replaceKey, List.map_cons] at ih ⊢
    rw [ih]
    by_cases h : p.1 = k <;> simp [h]


-- =======================================  MAIN THEOREM  ======================================= --

theorem TrajectoryAnalyzer.markKey_spec (aps : List (String × AtomicProposition S n)) (dur : ℝ)
    (sigs : List (String × FiniteSignal ℝ Bool)) (M : String → ℝ → Prop)
    (h : TrajectoryAnalyzer.SignalsRepresent aps dur sigs M) (lo hi : ℝ) (hlh : lo < hi)
    (p : String × AtomicProposition S n) (hp : p ∈ aps) : -- --- CONCL ---
    ∃ sigs', TrajectoryAnalyzer.markKey dur lo hi sigs p.1 = some sigs' ∧
      TrajectoryAnalyzer.SignalsRepresent aps dur sigs'
        (fun k τ => M k τ ∨ (k = p.1 ∧ Covers dur τ lo hi)) := by -- --- PROOF ---
  obtain ⟨hnd, hkeys, hall⟩ := h
  obtain ⟨sig, hlk, hv, hd, hat⟩ := hall p hp
  -- the signal or'ed with the indicator of the interval
  obtain ⟨s', hs', hv', hd', hat'⟩ := (FiniteKleeneSignalBuilder.or_indicator_spec sig hv lo hi).2
    (by exact_mod_cast hlh)
  rw [hd] at hs' hd' hat'
  obtain ⟨ind, hind, hc⟩ := Option.bind_eq_some_iff.mp hs'
  refine ⟨replaceKey sigs p.1 s', by simp [TrajectoryAnalyzer.markKey, hlk, hind, hc], hnd,
    (aux_map_fst_replaceKey sigs p.1 s').trans hkeys, fun q hq => ?_⟩
  -- the other signals are unchanged
  obtain ⟨sq, hlq, hvq, hdq, hatq⟩ := hall q hq
  by_cases hqk : q.1 = p.1
  · refine ⟨s', by rw [lookup_replaceKey, if_pos hqk, hlk]; rfl, hv', hd', fun τ h0 h1 => ?_⟩
    rw [hqk] at hatq hlq
    obtain ⟨x, hx, hxi⟩ := hatq τ h0 h1
    rw [hlk] at hlq
    obtain rfl : sig = sq := Option.some.inj hlq
    obtain ⟨y, hy, hyi⟩ := hat' τ x hx h0 h1
    exact ⟨y, hy, by rw [hyi, hxi]; simp [hqk]⟩
  · refine ⟨sq, by rw [lookup_replaceKey, if_neg hqk, hlq], hvq, hdq, fun τ h0 h1 => ?_⟩
    obtain ⟨x, hx, hxi⟩ := hatq τ h0 h1
    exact ⟨x, hx, by rw [hxi]; simp [hqk]⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
