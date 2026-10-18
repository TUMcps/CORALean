module

public import CORALean.Specification.FourValuedSignal.Theorems.MergeSpec
public import CORALean.Specification.OnlineAnalyzerNode.Operations.Propagate
public import CORALean.Specification.TentativeKleeneSignal.Theorems.GetIntervalSpec
public import CORALean.Specification.TentativeKleeneSignal.Theorems.SetInvalidSpec

@[expose] public section

/-!
# What `propagate` does at an atomic proposition

For an `AP` node and a nonempty `makeValid` interval, `propagate` makes the tentative observations
on the interval final: the node's signal takes the tentative signal's value at every time `t ≥ 0`
of the interval where that is conclusive, and keeps its value elsewhere; the tentative signal is
made invalid on the interval.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   15-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {A : Type}


-- =======================================  MAIN THEOREM  ======================================= --

theorem OnlineAnalyzerNode.propagate_ap_spec (eps : ℝ) (n : OnlineAnalyzerNode A)
    (ch : List (OnlineAnalyzerNode A)) (I : STLInterval) (hk : n.kind = .ap)
    (tent : TentativeKleeneSignal ℝ) (ht : n.tentative = some tent) (hs : n.signal.IsValid)
    (htv : tent.IsValid) (hne : I ≠ .empty) : -- --- STMT ---
    ∃ n', n.propagate eps ch I = some (n', ch) ∧ n'.signal.IsValid ∧
      n'.tentative = some (tent.setInvalid I) ∧ (tent.setInvalid I).IsValid ∧
      ∀ t : ℝ, 0 ≤ t →
        (t ∈ I.set ∧ tent.at t ≠ FourValued.ii → n'.signal.at t = tent.at t) ∧
        (¬ (t ∈ I.set ∧ tent.at t ≠ FourValued.ii) →
          n'.signal.at t = n.signal.at t) := by -- --- PROOF ---
  -- the tentative values on the interval, and the signal they are merged into
  obtain ⟨hfv, hf⟩ := tent.getInterval_spec htv I
  obtain ⟨hmv, hm⟩ := n.signal.merge_spec (tent.getInterval I) hs hfv
  obtain ⟨hsv, -⟩ := tent.setInvalid_spec htv I
  -- the interval is nonempty, so the node does merge
  have hIne : ∃ l u lc rc a b c z, I = STLInterval.nonempty l u lc rc a b c z := by
    cases I with
    | empty => exact absurd rfl hne
    | nonempty l u lc rc a b c z => exact ⟨l, u, lc, rc, a, b, c, z, rfl⟩
  obtain ⟨l, u, lc, rc, a, b, c, z, hIeq⟩ := hIne
  have hprop : n.propagate eps ch I = some ({ n with
      signal := n.signal.merge (tent.getInterval I),
      tentative := some (tent.setInvalid I) }, ch) := by
    subst hIeq
    unfold OnlineAnalyzerNode.propagate
    rw [hk, ht]
  obtain ⟨n', hn'⟩ : ∃ n' : OnlineAnalyzerNode A, n' = { n with
      signal := n.signal.merge (tent.getInterval I),
      tentative := some (tent.setInvalid I) } := ⟨_, rfl⟩
  have hsig : n'.signal = n.signal.merge (tent.getInterval I) := by rw [hn']
  refine ⟨n', by rw [hn']; exact hprop, by rw [hsig]; exact hmv, by rw [hn'], hsv,
    fun t htt => ?_⟩
  rw [hsig]
  -- inside the interval the merged value is the tentative one where conclusive
  obtain ⟨m1, m2⟩ := hm t htt
  obtain ⟨f1, f2⟩ := hf t htt
  by_cases hmem : t ∈ I.set
  · rw [f1 hmem] at m1 m2
    refine ⟨fun h' => m1 h'.2, fun h' => m2 ?_⟩
    by_contra hn
    exact h' ⟨hmem, hn⟩
  · rw [f2 hmem] at m2
    exact ⟨fun h' => absurd h'.1 hmem, fun _ => m2 rfl⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
