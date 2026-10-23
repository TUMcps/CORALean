module

public import CORALean.Specification.FourValuedSignal.Theorems.SetSpec
public import CORALean.Specification.OnlineAnalyzerNode.Operations.ObserveSet
public import CORALean.Specification.TentativeKleeneSignal.Theorems.ObserveSpec

@[expose] public section

/-!
# What an `AP` node observes

An `AP` node with its proposition `ap`, observing a set whose value for `ap` is `val` (`apValue`)
at a time not yet propagated: if the observation is final (`tentative = false`), its satisfaction
signal becomes `val` on the interval and stays as it was elsewhere, and the tentative signal is
untouched; if it is tentative, the satisfaction signal is untouched and the tentative signal
observes `val` in the interval (`TentativeKleeneSignal.observe`).

## Inputs
* `eps` – machine epsilon
* `n` – atomic node
* `set` – observed set
* `interval` – observed time interval
* `loc` – location
* `val` – value of the proposition on the set

## Hypotheses
* `hk` – the node is atomic
* `hnc` – no propagated time is observed again

## Conclusion
* a final observation sets the signal, a tentative one the tentative signal
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   15-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {𝕋 : Type} [Scalar 𝕋] [ExactScalar 𝕋] {S : ℕ → Type} {d : ℕ}
  [∀ k, ContSet (S k) (Vec ℝ k)] [Mtimes (Mat 𝕋) S] [∀ k, Contains (S k) (S k)]
  [∀ k, IsDisjoint (S k) (S k)]


-- =======================================  MAIN THEOREM  ======================================= --

theorem OnlineAnalyzerNode.observeSet_ap_spec (eps : ℝ)
    (n : OnlineAnalyzerNode ℝ (AtomicProposition S d)) (set : S d) (interval : STLInterval ℝ)
    (loc : ℕ) (hk : n.kind = .ap)
    (hnc : OnlineAnalyzerNode.conflicts eps interval.infimum.value interval.infimum.closed
      n.prop = some false) (val : Kleene) : -- --- CONCL ---
    ∀ tent ∈ n.tentative,
      ∀ ap ∈ n.ap,
        OnlineAnalyzerNode.apValue (𝕋 := 𝕋) ap set loc = some val →
        (OnlineAnalyzerNode.observeSet (𝕋 := 𝕋) eps n set interval loc false =
            some { n with signal := n.signal.set interval (FourValued.fromKleene val) } ∧
          (n.signal.IsValid →
            (n.signal.set interval (FourValued.fromKleene val)).IsValid ∧ ∀ t : ℝ, 0 ≤ t →
              (t ∈ interval.set →
                (n.signal.set interval (FourValued.fromKleene val)).at t =
                  FourValued.fromKleene val) ∧
              (t ∉ interval.set →
                (n.signal.set interval (FourValued.fromKleene val)).at t = n.signal.at t))) ∧
        (OnlineAnalyzerNode.observeSet (𝕋 := 𝕋) eps n set interval loc true =
            some { n with tentative := some (tent.observe interval val) } ∧
          (tent.IsValid →
            (tent.observe interval val).IsValid)) := by -- --- PROOF ---
  intro tent (ht : n.tentative = some tent) ap (hap : n.ap = some ap) hval
  refine ⟨⟨?_, fun hs => FourValuedSignal.set_spec n.signal hs interval _⟩,
    ⟨?_, fun hs => (tent.observe_spec hs interval val).1⟩⟩
  -- a final observation sets the satisfaction signal
  · simp [OnlineAnalyzerNode.observeSet, hk, hnc, hap, hval]
  -- a tentative one is stored in the tentative signal
  · simp [OnlineAnalyzerNode.observeSet, hk, hnc, hap, hval, ht]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
