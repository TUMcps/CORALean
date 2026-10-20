module

public import CORALean.Specification.KleeneSignal.Theorems.UntilSpec
public import CORALean.Specification.Kleene.Instances
public import CORALean.Specification.Kleene.Theorems.Basic

@[expose] public section

/-!
# The until of three-valued signals is monotone

If `Λ₁ ⊑ₜ Λ₁'` and `Λ₂ ⊑ₜ Λ₂'` at every time `t ≥ 0`, then `Λ₁ U_I Λ₂ ⊑ₜ Λ₁' U_I Λ₂'` there:
`U_I` on `U₁`-signals is monotone ([1, Lemma 3]), proved from the direct semantics of [1, Eq. 2]
(`until_spec`).

## Inputs
* `l` – left signal
* `l'` – larger left signal
* `r` – right signal
* `r'` – larger right signal
* `U` – time interval

## Hypotheses
* `hl` – the left signal is valid
* `hl'` – the larger left signal is valid
* `hr` – the right signal is valid
* `hr'` – the larger right signal is valid
* `h1` – the left signal is below its larger one
* `h2` – the right signal is below its larger one

## Conclusion
* the until is below the larger until at all times

## References

* [1] F. Lercher and M. Althoff. "Using Four-Valued Signal Temporal Logic for Incremental
      Verification of Hybrid Systems". CAV, LNCS 14683, pp. 259-281, 2024.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   15-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =======================================  MAIN THEOREM  ======================================= --

theorem KleeneSignal.until_mono (l l' r r' : KleeneSignal ℝ) (hl : l.IsValid) (hl' : l'.IsValid)
    (hr : r.IsValid) (hr' : r'.IsValid) (U : STLInterval)
    (h1 : ∀ t : ℝ, 0 ≤ t → l.at t ≤ l'.at t) (h2 : ∀ t : ℝ, 0 ≤ t → r.at t ≤ r'.at t) :
    ∀ t : ℝ, 0 ≤ t → (l.until U r).at t ≤ (l'.until U r').at t := by -- --- PROOF ---
  intro t ht
  obtain ⟨-, h⟩ := KleeneSignal.until_spec l r hl hr U
  obtain ⟨-, h'⟩ := KleeneSignal.until_spec l' r' hl' hr' U
  have hpos : ∀ t', t' - t ∈ U.set → 0 ≤ t' := fun t' hu => by
    have := STLInterval.zero_le_of_mem_set U _ hu; linarith
  rw [Kleene.le_iff_tt_ff]
  refine ⟨fun htt => ?_, fun hff => ?_⟩
  · obtain ⟨t', hu, hr0, hl0⟩ := ((h t ht).1).1 htt
    refine ((h' t ht).1).2 ⟨t', hu, ((Kleene.le_iff_tt_ff _ _).1 (h2 t' (hpos t' hu))).1 hr0,
      fun x hx1 hx2 => ((Kleene.le_iff_tt_ff _ _).1 (h1 x (by linarith))).1 (hl0 x hx1 hx2)⟩
  · refine ((h t ht).2).2 fun t' hu => ?_
    rcases ((h' t ht).2).1 hff t' hu with h0 | ⟨x, hx1, hx2, hx3⟩
    · exact Or.inl (((Kleene.le_iff_tt_ff _ _).1 (h2 t' (hpos t' hu))).2 h0)
    · exact Or.inr ⟨x, hx1, hx2, ((Kleene.le_iff_tt_ff _ _).1 (h1 x (by linarith))).2 hx3⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
