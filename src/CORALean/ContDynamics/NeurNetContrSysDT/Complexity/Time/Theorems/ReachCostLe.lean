module

public import CORALean.ContDynamics.NeurNetContrSysDT.Complexity.Time.Operations.ReachCost
public import CORALean.ContDynamics.NeurNetContrSysDT.Complexity.Time.Operations.ReachStepBound
public import CORALean.ContDynamics.NeurNetContrSysDT.Theorems.Real.ReachOrderLe
public import CORALean.ContDynamics.LinearSysDT.Complexity.Time.Operations.Basic
public import CORALean.ContSet.Zonotope.Real.Complexity.Time.Operations.MtimesCost
public import CORALean.ContSet.Zonotope.Real.Complexity.Time.Theorems.Basic
public import CORALean.ContSet.Zonotope.Real.Complexity.Time.Operations.PlusCost
public import CORALean.ContSet.Zonotope.Real.Complexity.Time.Operations.ReduceGirardCost
public import CORALean.ContSet.Zonotope.Real.Complexity.Time.Theorems.ReduceGirardCostMono
public import CORALean.NN.Complexity.Time.Operations.EncloseCost

@[expose] public section

/-!
# `reach` costs at most `k` worst-case steps

The worked composition: nothing here is asserted. The leaf counts come from
`Zonotope/Real/Complexity/Time/` and `NN/Complexity/Time/Enclose.lean`, the generator count each is
evaluated at comes from `reach_order_le` and the caller's own bound `hEnc` on
the controller's output, and monotonicity of a count in the operand size is
what joins the two. What is left is induction on the step count.

`hR₀` and `hEnc` are the two hypotheses no size fact here supplies: `hR₀`
because `reach_order_le` bounds every set the run *produces*, not the
caller's own `R₀`; `hEnc` because how many generators an enclosure carries
depends on which layers the controller runs, which no `Complexity/Space/` fact
states for `NeuralNetwork.enclose` in general.
-/

-- Authors:       Claude Opus 5.5, Claude Sonnet 5.5
-- Written:       23-September-2026
-- Last update:   15-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real

variable {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- Every set the run holds is at order `o`: `reach_order_le` past the first
step, and the caller's hypothesis at it. -/
theorem NeurNetContrSysDT.aux_reach_h_le (sys : NeurNetContrSysDT (LinearSysDT ℝ n) 𝒵 n)
    (U_ext : Zonotope (Vec ℝ sys.nExt)) {o : ℕ} (ho : 0 < o)
    (R₀ : Zonotope (Vec ℝ n)) (hR₀ : R₀.h ≤ o * n) :
    ∀ k, (sys.reach (S := 𝒵) U_ext ⟨R₀, 0, k⟩ ⟨o, ho⟩).h ≤ o * n
  | 0 => hR₀
  | k + 1 => sys.reach_order_le U_ext ho R₀ k

/-- One step at any input size within the order bound, and any enclosure size
within `hEnc`, costs at most `reachStepBound`. -/
theorem NeurNetContrSysDT.aux_step_le (n hEnc o hIn hOut : ℕ) (hi : hIn ≤ o * n)
    (houu : hOut ≤ hEnc) :
    Zonotope.mtimesCost n n hIn + Zonotope.plusCost n
        + Zonotope.reduceGirardCost n (hIn + hOut) ≤ LinearSysDT.reachStepBound n hEnc o :=
  Cost.add_le_add (Cost.add_le_add (Zonotope.mtimesCost_mono n n hi) le_rfl)
    (Zonotope.reduceGirardCost_mono n (Nat.add_le_add hi houu))


-- =======================================  MAIN THEOREM  ======================================= --

/-- `k` steps cost at most `k` worst-case steps, at a per-layer bound `LC` and a
bound `hEnc` on what the controller's enclosure carries into each step. -/
theorem NeurNetContrSysDT.reachCost_le (sys : NeurNetContrSysDT (LinearSysDT ℝ n) 𝒵 n)
    (U_ext : Zonotope (Vec ℝ sys.nExt)) {o : ℕ} (ho : 0 < o)
    (R₀ : Zonotope (Vec ℝ n)) (hR₀ : R₀.h ≤ o * n) (LC : ∀ {a b : ℕ}, Layer 𝒵 a b → Cost)
    (hEnc hU : ℕ) (hE : ∀ k, (sys.contr.enclose (sys.reach (S := 𝒵) U_ext ⟨R₀, 0, k⟩ ⟨o, ho⟩)).h
      ≤ hEnc) (hUe : U_ext.h ≤ hU) (k : ℕ) :
    sys.reachCost U_ext o ho R₀ LC k ≤ k • sys.reachStepBound o hEnc hU LC := by -- --- PROOF ---
  induction k with
  | zero => simp [NeurNetContrSysDT.reachCost]
  | succ k ih =>
    -- the step's input is the set reached so far, at order `o`; its enclosure is at most `hEnc`
    have hstep := NeurNetContrSysDT.aux_step_le n (hEnc + hU) o _ _
      (sys.aux_reach_h_le U_ext ho R₀ hR₀ k) (Nat.add_le_add (hE k) hUe)
    -- the input map's `mtimes` is at the enclosure's size, at most `hEnc`
    have hin : Zonotope.mtimesCost n sys.m
        (sys.contr.enclose (sys.reach (S := 𝒵) U_ext ⟨R₀, 0, k⟩ ⟨o, ho⟩)).h
          + Zonotope.plusCost n ≤
        Zonotope.mtimesCost n sys.m hEnc + Zonotope.plusCost n :=
      Cost.add_le_add (Zonotope.mtimesCost_mono n sys.m (hE k)) le_rfl
    -- and the external inputs' at theirs, at most `hU`
    have hext : Zonotope.mtimesCost n sys.nExt U_ext.h + Zonotope.plusCost n ≤
        Zonotope.mtimesCost n sys.nExt hU + Zonotope.plusCost n :=
      Cost.add_le_add (Zonotope.mtimesCost_mono n sys.nExt hUe) le_rfl
    have h := Nat.add_le_add (Cost.le_iff.mp ih)
      (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add
        (le_refl (NeuralNetwork.encloseCost LC sys.contr).ops) (Cost.le_iff.mp hin))
        (Cost.le_iff.mp hext)) (Cost.le_iff.mp hstep))
    refine Cost.le_iff.mpr ?_
    simpa [NeurNetContrSysDT.reachCost, NeurNetContrSysDT.reachStepBound, Nat.succ_mul,
      Nat.add_assoc] using h

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
