module

public import CORALean.HybridDynamics.Operations.NonlinearResetResolve

@[expose] public section

/-!
# `NonlinearReset.resolve` applies to the closed-loop input

The resolved reset at the state `x` and the global input `v` is the original reset at the input
`w` of all components in which every globally bound input is its entry of `v` and every other
one is the output of the component it is bound to, at that component's own input: exact. `w` is
unique, and the theorem says the resolved reset does not depend on which `w` is used, so it is
the value at the closed-loop input. The output must not depend on locally bound inputs, which
`resolve` throws for in CORA.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {N g k : ℕ} {n m p : Fin k → ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem NonlinearReset.resolve_apply (r : NonlinearReset N (∑ i, m i) N)
    (out : ∀ i, Vec ℝ (n i) → Vec ℝ (m i) → Vec ℝ (p i))
    (stateBinds : ∀ i, Fin (n i) → Fin N) (inputBinds : ∀ i, Fin (m i) → ResolveSource k p g)
    (hloc : ∀ c (xc : Vec ℝ (n c)) (u u' : Vec ℝ (m c)),
      (∀ jj a, inputBinds c jj = .global a → u jj = u' jj) → ∀ l, out c xc u l = out c xc u' l)
    (x : Vec ℝ N) (v : Vec ℝ g) (w : Vec ℝ (∑ i, m i))
    (hg : ∀ i j a, inputBinds i j = .global a → w (finSigmaFinEquiv ⟨i, j⟩) = v a)
    (ho : ∀ i j c' l, inputBinds i j = .output c' l →
      w (finSigmaFinEquiv ⟨i, j⟩) =
        out c' (fun s => x (stateBinds c' s)) (fun jj => w (finSigmaFinEquiv ⟨c', jj⟩)) l) :
    (r.resolve out stateBinds inputBinds).f x v = r.f x w := by -- --- PROOF ---
  have : (fun col : Fin (∑ i, m i) =>
      match inputBinds (finSigmaFinEquiv.symm col).1 (finSigmaFinEquiv.symm col).2 with
      | .global a => v a
      | .output c l => out c (fun s => x (stateBinds c s)) (fun jj =>
          match inputBinds c jj with
          | .global a => v a
          | .output _ _ => 0) l) = w := by
    funext col
    obtain ⟨⟨i, j⟩, rfl⟩ := finSigmaFinEquiv.surjective col
    have e1 : finSigmaFinEquiv.symm (finSigmaFinEquiv ⟨i, j⟩) = ⟨i, j⟩ := Equiv.symm_apply_apply _ _
    rw [e1]
    rcases h : inputBinds i j with a | ⟨c', l⟩
    · exact (hg i j a h).symm
    · rw [ho i j c' l h]
      exact (hloc c' _ _ _ (fun jj a ha => by simp [ha, hg c' jj a ha]) l).symm
  exact congrArg (r.f x) this

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
