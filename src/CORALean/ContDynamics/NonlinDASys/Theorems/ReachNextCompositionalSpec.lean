import CORALean.ContDynamics.NonlinDASys.Operations.ReachNextCompositional
import CORALean.ContSet.Zonotope.Real.Theorems.MtimesExact

/-!
# What [1, Alg. 2] returns

The result `(R⁽ⁱ⁾ᵈ(t_{k+1}), R(τ_k), Û⁽ⁱ⁾)` of `NonlinDASys.reachNextCompositional` has passed
the test of lines 10-15 for every subsystem, `Υ⁽ⁱ⁾ R(τ_k) ⊆ Λ⁽ⁱ⁾ Û⁽ⁱ⁾` (with an inclusion test
`sub` that is sound), and is built from [1, Alg. 1] run on the final `Û⁽ⁱ⁾`: `R(τ_k)` is
the join of the local sets (line 9) and each subsystem's pair is `subReach` at its `Û⁽ⁱ⁾`,
given that the start state's confirmed subsystems are.

This is the whole of what the loop certifies. That a solution of the coupled system then
stays in `R(τ_k)`, the interface inputs being the other subsystems' states, is the assumption's
validation by the computed sets, which [1] states and does not prove, and is not shown here.

## References

* [1] M. Althoff. "Formal and Compositional Analysis of Power Systems using Reachable Sets".
      IEEE Transactions on Power Systems, 29(5):2270-2280, 2014.
-/

-- Authors:       Tobias Ladner
-- Written:       12-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real Matrix

variable {ns n : ℕ} {m e d : Fin ns → ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Alg. 2]: the returned sets passed the test of lines 10-15 and come from Alg. 1 on `Û⁽ⁱ⁾`. -/
theorem NonlinDASys.reachNextCompositional_spec
    (subReach : ∀ i, Zonotope (Vec ℝ (m i)) → Zonotope (Vec ℝ (e i)) × Zonotope (Vec ℝ (d i)))
    (Φ : ∀ i, Mat ℝ n (d i)) (Υ : ∀ i, Mat ℝ (m i) n) (Λ : ∀ i, Mat ℝ (m i) (m i)) (lamU : ℝ)
    (sub : ∀ {k : ℕ}, Zonotope (Vec ℝ k) → Zonotope (Vec ℝ k) → Bool)
    (hsub : ∀ {k : ℕ} (A B : Zonotope (Vec ℝ k)), sub A B = true → A.construct ⊆ B.construct)
    (fuel : ℕ) (s : NonlinDASys.CompositionalState m e d)
    (hs : ∀ i, s.inputEnclosure i = true → (s.Rnext i, s.Rloc i) = subReach i (s.Uhat i))
    {Rn : ∀ i, Zonotope (Vec ℝ (e i))} {R : Zonotope (Vec ℝ n)} {Uh : ∀ i, Zonotope (Vec ℝ (m i))}
    (h : NonlinDASys.reachNextCompositional subReach Φ Υ Λ lamU sub fuel s = some (Rn, R, Uh)) :
    (∀ i, sub (Zonotope.mtimes (Υ i) R) (Zonotope.mtimes (Λ i) (Uh i)) = true) ∧
    (∀ i, (Υ i *ᵥ ·) '' R.construct ⊆ (Λ i *ᵥ ·) '' (Uh i).construct) ∧
    ∃ Rloc : ∀ i, Zonotope (Vec ℝ (d i)),
      R = NonlinDASys.composeSubsystems Φ Rloc ∧
        ∀ i, (Rn i, Rloc i) = subReach i (Uh i) := by -- --- PROOF ---
  induction fuel generalizing s with
  | zero => simp [NonlinDASys.reachNextCompositional] at h
  | succ k ih =>
      unfold NonlinDASys.reachNextCompositional at h
      extract_lets pass R inputEnclosure U at h
      -- every subsystem's pair is `subReach` at its `Û⁽ⁱ⁾`: recomputed, or confirmed before
      have hpass : ∀ i, ((pass i).2.1, (pass i).2.2) = subReach i (pass i).1 := by
        intro i
        by_cases hi : s.inputEnclosure i = true
        · simp only [pass, if_pos hi]; exact hs i hi
        · simp only [pass, if_neg hi]
      split_ifs at h with hall
      · -- every flag is set: the loop ends
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl, rfl⟩ := h
        refine ⟨hall, fun i => ?_, fun i => (pass i).2.2, rfl, hpass⟩
        rw [Zonotope.mtimes_exact, Zonotope.mtimes_exact]
        exact hsub _ _ (hall i)
      · exact ih _ (fun i _ => hpass i) h

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
