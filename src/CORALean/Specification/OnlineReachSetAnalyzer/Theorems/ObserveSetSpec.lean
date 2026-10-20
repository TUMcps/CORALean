module

public import CORALean.Specification.OnlineReachSetAnalyzer.Operations.ObserveSet
public import CORALean.Specification.OnlineReachSetAnalyzer.Theorems.UpdateNodeSpec

@[expose] public section

/-!
# What `observeSet` does to the analyzer

An empty interval changes nothing. Otherwise the observation is counted, the leaves, the
frequency and the nodes' graph are as before, and if the count is no multiple of the propagation
frequency no propagation takes place: nothing is marked propagated and only the leaf nodes
changed (they observed the set).

## Inputs
* `eps` – machine epsilon
* `obj` – analyzer
* `set` – observed set
* `loc` – location
* `mv` – interval to make final

## Hypotheses
* none

## Conclusion
* an empty interval changes nothing, else the observation is counted
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {𝕋 : Type} [Scalar 𝕋] [ExactScalar 𝕋] {S : ℕ → Type} {d : ℕ}
  [∀ k, ContSet (S k) (Vec ℝ k)] [Mtimes (Mat 𝕋) S] [∀ k, Contains (S k) (S k)]
  [∀ k, IsDisjoint (S k) (S k)]


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- Updating the leaves `ls` changes no node that is not one of them. -/
theorem aux_updateNodes_getElem? {B : Type} (g : B → Option B) : -- --- CONCL ---
    ∀ (ls : List ℕ) (nodes nodes' : List B),
      ls.foldlM (fun ns l => OnlineReachSetAnalyzer.updateNode ns l g) nodes = some nodes' →
      ∀ j, (j + 1) ∉ ls → nodes'[j]? = nodes[j]? := by -- --- PROOF ---
  intro ls
  induction ls with
  | nil => intro nodes nodes' h j _; simp at h; rw [h]
  | cons l ls ih =>
    intro nodes nodes' h j hj
    rw [List.foldlM_cons] at h
    obtain ⟨nodes1, h1, h2⟩ := Option.bind_eq_some_iff.mp h
    -- the first leaf is changed, the others only by the rest
    obtain ⟨hl0, n, n', hn, -, rfl⟩ := (OnlineReachSetAnalyzer.updateNode_eq_some_iff _ _ _ _).mp h1
    have hjl : (j + 1) ≠ l := fun e => hj (e ▸ List.mem_cons_self)
    rw [ih _ _ h2 j (fun hm => hj (List.mem_cons_of_mem _ hm)), List.getElem?_set_ne (by omega)]


-- =======================================  MAIN THEOREM  ======================================= --

theorem OnlineReachSetAnalyzer.observeSet_spec (eps : ℝ) (obj : OnlineReachSetAnalyzer S d)
    (set : S d) (loc : ℕ) (mv : Option STLInterval) : -- --- CONCL ---
    OnlineReachSetAnalyzer.observeSet (𝕋 := 𝕋) eps obj set .empty loc mv = some obj ∧
    ∀ (I : STLInterval) (obj' : OnlineReachSetAnalyzer S d), I ≠ .empty →
      OnlineReachSetAnalyzer.observeSet (𝕋 := 𝕋) eps obj set I loc mv = some obj' →
      obj'.numObservations = obj.numObservations + 1 ∧ obj'.leaves = obj.leaves ∧
        obj'.propagationFrequency = obj.propagationFrequency ∧
        ((obj.numObservations + 1) % obj.propagationFrequency ≠ 0 →
          obj'.propagated = obj.propagated ∧
          ∀ j, (j + 1) ∉ obj.leaves → obj'.nodes[j]? = obj.nodes[j]?) := by -- --- PROOF ---
  refine ⟨rfl, fun I obj' hI h => ?_⟩
  cases I with
  | empty => exact absurd rfl hI
  | nonempty l u lc rc a b c =>
    unfold OnlineReachSetAnalyzer.observeSet at h
    obtain ⟨nodes, hnodes, h⟩ := Option.bind_eq_some_iff.mp h
    dsimp only at h
    by_cases hm : (obj.numObservations + 1) % obj.propagationFrequency = 0
    · -- the propagation runs and keeps these fields
      rw [if_pos hm] at h
      unfold OnlineReachSetAnalyzer.propagate at h
      obtain ⟨st, -, rfl⟩ := Option.map_eq_some_iff.mp h
      exact ⟨rfl, rfl, rfl, fun hne => absurd hm hne⟩
    · rw [if_neg hm] at h
      obtain rfl := Option.some.inj h
      exact ⟨rfl, rfl, rfl, fun _ => ⟨rfl, fun j hj =>
        aux_updateNodes_getElem? _ _ _ _ hnodes j hj⟩⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
