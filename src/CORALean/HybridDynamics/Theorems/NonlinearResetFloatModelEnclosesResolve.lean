module

public import CORALean.HybridDynamics.Operations.NonlinearResetResolveFloat
public import CORALean.HybridDynamics.Operations.NonlinearResetResolve

@[expose] public section

/-!
# The resolved float model encloses the resolved reset

If `fm` encloses the product reset `r` and each `fmOut c` encloses the component output `out c`,
then `fm.resolve` encloses `r.resolve`: every entry of the stacked input is in its box, being a
global input or a component output at states and globally bound inputs that are in their boxes.
An outer statement.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float ContSet SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {N g k : ℕ} {n m p : Fin k → ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem NonlinearReset.FloatModel.Encloses.resolve
    {fm : NonlinearReset.FloatModel 𝕋 N (∑ i, m i) N} {r : NonlinearReset N (∑ i, m i) N}
    (h : fm.Encloses r)
    {fmOut : ∀ i, Interval (Vec 𝕋 (n i)) → Interval (Vec 𝕋 (m i)) → Interval (Vec 𝕋 (p i))}
    {out : ∀ i, Vec ℝ (n i) → Vec ℝ (m i) → Vec ℝ (p i)}
    (hout : ∀ c Xc Uc, ∀ x ∈ construct Xc, ∀ u ∈ construct Uc,
      out c x u ∈ construct (fmOut c Xc Uc))
    (stateBinds : ∀ i, Fin (n i) → Fin N)
    (inputBinds : ∀ i, Fin (m i) → ResolveSource k p g) : -- --- CONCL ---
    (fm.resolve fmOut stateBinds inputBinds).Encloses
      (r.resolve out stateBinds inputBinds) := by -- --- PROOF ---
  -- a vector is in a float box when every coordinate is between the real bounds
  have mem_iff : ∀ {k : ℕ} (I : Interval (Vec 𝕋 k)) (v : Vec ℝ k),
      v ∈ construct I ↔ ∀ i, toReal (I.inf i) ≤ v i ∧ v i ≤ toReal (I.sup i) :=
    fun _ _ => Iff.rfl
  refine ⟨fun X V x hx v hv => ?_⟩
  rw [mem_iff] at hx hv
  unfold NonlinearReset.FloatModel.resolve NonlinearReset.resolve
  dsimp only
  refine h.f_mem X _ x ((mem_iff _ _).2 hx) _ ((mem_iff _ _).2 fun col => ?_)
  -- the entry `col` of the stacked input: a global input, or a component output
  rcases hcase : inputBinds (finSigmaFinEquiv.symm col).1 (finSigmaFinEquiv.symm col).2 with
    a | ⟨c, l⟩
  · simp only [hcase]
    exact hv a
  · -- the component's states and globally bound inputs are in their boxes
    simp only [hcase]
    have hxc : (fun s => x (stateBinds c s)) ∈ construct
        (⟨fun s => X.inf (stateBinds c s), fun s => X.sup (stateBinds c s)⟩ :
          Interval (Vec 𝕋 (n c))) := (mem_iff _ _).2 fun s => hx (stateBinds c s)
    have huc : (fun jj => match inputBinds c jj with | .global a => v a | .output _ _ => 0) ∈
        construct (⟨fun jj => match inputBinds c jj with
          | .global a => V.inf a | .output _ _ => FloatOps.zero,
          fun jj => match inputBinds c jj with
          | .global a => V.sup a | .output _ _ => FloatOps.zero⟩ : Interval (Vec 𝕋 (m c))) := by
      refine (mem_iff _ _).2 fun jj => ?_
      rcases hjj : inputBinds c jj with a | ⟨_, _⟩
      · simp only [hjj]
        exact hv a
      · simp only [hjj, toReal_zero]
        exact ⟨le_rfl, le_rfl⟩
    exact (mem_iff _ _).1 (hout c _ _ _ hxc _ huc) l

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
