module

public import CORALean.Specification.FourValued.Theorems.Basic
public import CORALean.Specification.OnlineAnalyzerNode.Theorems.ApValueSpec
public import CORALean.Specification.OnlineAnalyzerNode.Theorems.ObserveSetApSpec

@[expose] public section

/-!
# The signal of an `AP` node is sound

After a final observation of a set, the satisfaction signal of an `AP` node is `True` at a time of
the observed interval only if every state of the set satisfies the proposition, and `False` only if
none does: the four-valued semantics of an atomic proposition on a set of states.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   15-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open ContSet

variable {𝕋 : Type} [Scalar 𝕋] [ExactScalar 𝕋] {S : ℕ → Type} {d : ℕ}
  [∀ k, ContSet (S k) (Vec ℝ k)] [Mtimes (Mat 𝕋) S] [∀ k, Contains (S k) (S k)]
  [∀ k, IsDisjoint (S k) (S k)]


-- =======================================  MAIN THEOREM  ======================================= --

theorem OnlineAnalyzerNode.observeSet_ap_sound (eps : ℝ)
    (n : OnlineAnalyzerNode (AtomicProposition S d)) (set : S d) (interval : STLInterval)
    (loc : ℕ) (hk : n.kind = .ap) (ap : AtomicProposition S d) (hap : n.ap = some ap)
    (tent : TentativeKleeneSignal ℝ) (ht : n.tentative = some tent)
    (hnc : OnlineAnalyzerNode.conflicts eps interval.infimum.value interval.infimum.closed
      n.prop = some false) (val : Kleene)
    (hval : OnlineAnalyzerNode.apValue (𝕋 := 𝕋) ap set loc = some val)
    (hs : n.signal.IsValid)
    (n' : OnlineAnalyzerNode (AtomicProposition S d))
    (h : OnlineAnalyzerNode.observeSet (𝕋 := 𝕋) eps n set interval loc false = some n')
    (t : ℝ) (h0 : 0 ≤ t) (hti : t ∈ interval.set) : -- --- STMT ---
    (n'.signal.at t = FourValued.tt → ∀ x ∈ construct set, ap.Holds x loc) ∧
    (n'.signal.at t = FourValued.ff → ∀ x ∈ construct set, ¬ ap.Holds x loc) := by -- --- PROOF ---
  obtain ⟨hm, hsig⟩ := (OnlineAnalyzerNode.observeSet_ap_spec (𝕋 := 𝕋) eps n set interval loc
    hk ap hap tent ht hnc val hval).1
  obtain rfl : { n with signal := n.signal.set interval (FourValued.fromKleene val) } = n' :=
    Option.some.inj (hm.symm.trans h)
  have hat := ((hsig hs).2 t h0).1 hti
  obtain ⟨htt, hff, -⟩ := OnlineAnalyzerNode.apValue_spec (𝕋 := 𝕋) ap set loc
  refine ⟨fun h1 => htt ?_, fun h1 => hff ?_⟩
  · -- the value is true
    rw [hat] at h1
    rw [hval, (FourValued.fromKleene_eq_tt_iff val).mp h1]
  · rw [hat] at h1
    rw [hval, (FourValued.fromKleene_eq_ff_iff val).mp h1]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
