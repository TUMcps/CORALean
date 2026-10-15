module

public import CORALean.Specification.FourValuedSignal.Theorems.SetSpec
public import CORALean.Specification.OnlineAnalyzerNode.Operations.SetPropagated
public import CORALean.Specification.STLInterval.Theorems.LowerStlInterval

@[expose] public section

/-!
# What `setPropagated` does

If `setPropagated` does not throw, the interval of that parent is replaced; and if the node drops
what is propagated, its valid signal is inconclusive at every `t ≥ 0` in `getAllProp` of the new
node and unchanged elsewhere.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {A : Type}


-- =======================================  MAIN THEOREM  ======================================= --

theorem OnlineAnalyzerNode.setPropagated_spec (eps : ℝ) (n n' : OnlineAnalyzerNode A)
    (hv : n.signal.IsValid) (parent : ℕ) (int : STLInterval)
    (h : n.setPropagated eps parent int = some n') :
    n'.signal.IsValid ∧ n'.prop = n.prop.set (n.parents.idxOf parent) int ∧
      (n.dropPropagated = false → n'.signal = n.signal) ∧
      (n.dropPropagated = true → ∀ t : ℝ, 0 ≤ t →
        (t ∈ (n'.getAllProp eps).set → n'.signal.at t = FourValued.ii) ∧
        (t ∉ (n'.getAllProp eps).set → n'.signal.at t = n.signal.at t)) := by -- --- PROOF ---
  unfold OnlineAnalyzerNode.setPropagated at h
  dsimp only at h
  rcases hp : n.prop[n.parents.idxOf parent]? with _ | old
  · rw [hp] at h; simp at h
  · rw [hp] at h
    by_cases hb : ¬ STLInterval.isequal eps old int ∧ STLInterval.contains_ eps old int
    · simp [hb] at h
    · simp only [hb, if_false] at h
      by_cases hd : n.dropPropagated = true
      · -- the signal is made inconclusive on everything propagated
        simp only [hd, if_true, Option.some.injEq] at h
        subst h
        have hI : ∀ f, ((OnlineAnalyzerNode.getAllProp eps
            { n with prop := n.prop.set (n.parents.idxOf parent) int }).fieldsOf = some f) →
            0 ≤ f.lower := by
          intro f hf
          unfold OnlineAnalyzerNode.getAllProp at hf
          exact (STLInterval.lower_stlInterval _ _ _ _ f hf).symm.le
        obtain ⟨hv', hset⟩ := FourValuedSignal.set_spec n.signal hv _ hI FourValued.ii
        exact ⟨hv', rfl, fun h => absurd h (by simp [hd]), fun _ t ht => hset t ht⟩
      · have hd' : n.dropPropagated = false := by simpa using hd
        simp only [hd', Bool.false_eq_true, if_false, Option.some.injEq] at h
        subst h
        exact ⟨hv, rfl, fun _ => rfl, fun h => absurd h (by simp [hd'])⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
