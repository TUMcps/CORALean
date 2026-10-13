import CORALean.ContSet.ConZonotope.Real.Theorems.ReduceKeepByOuter
import CORALean.ContSet.Conversion.Real.Zonotope_to_ConZonotope
import CORALean.ContSet.Zonotope.Real.Theorems.MemConstruct
import CORALean.Global.Entrywise

/-!
# A reduction that keeps the constraint

A segment `{2β₀ + β₁ + β₂}` over `β₀ ∈ [-1, 0]`, `β₁, β₂ ∈ [-1, 1]`: the constraint
cuts the long generator in half, so the set is `[-4, 2]`. Boxing the two short
generators into one, the Girard-style reduction goes through the enclosing zonotope
and forgets `β₀ ≤ 0`, ending at `[-4, 4]`; `reduceKeepBy` projects the constraint onto
the generator it keeps and ends at `[-4, 2]`. Both are outer, only one is tight here.
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

/-- The segment above, `β₀ ≤ 0` its one constraint. -/
abbrev reduceKeepExample : ConZonotope (Vec ℝ 1) where
  h := 3
  c := fun _ => 0
  G := fun j _ => if j = 0 then 2 else 1
  P := { m := 1, A := fun _ => LinearMap.proj 0, b := fun _ => 0, me := 0,
         Ae := fun i => i.elim0, be := fun i => i.elim0 }

/-- Keeping the first generator and boxing the other two. -/
abbrev reduceKeepExampleSplit : Split (Fin reduceKeepExample.h) into (Fin 1) ⊕ (Fin 2) :=
  Partition.split 1 2


-- =======================================  MAIN THEOREM  ======================================= --

/-- With the constraint kept, the reduced set stays below `2`. -/
theorem reduceKeepExample_le : (reduceKeepExample.reduceKeepBy reduceKeepExampleSplit).construct
    ⊆ {x | x 0 ≤ 2} := by -- --- PROOF ---
  rintro x ⟨γ, hγ, hP, rfl⟩
  have h0 : (reduceKeepExample.P.A 0) (ConZonotope.keepEmbed reduceKeepExampleSplit
        (blockLeft 1 1 γ))
      ≤ reduceKeepExample.P.b 0
        + ConZonotope.keepSlack reduceKeepExampleSplit (reduceKeepExample.P.A 0) :=
    hP.1 (Fin.castAdd (0 + 0) (0 : Fin 1))
  have h1 : |γ (1 : Fin (1 + 1))| ≤ 1 := hγ (Fin.natAdd 1 (0 : Fin 1))
  have h2 := hγ (Fin.castAdd 1 (0 : Fin 1))
  -- the dropped generators are unconstrained, so the slack is zero
  have hl : (Pi.single (reduceKeepExampleSplit.left 0) (1 : ℝ) : Vec ℝ 3) 0 = 1 := rfl
  have hr0 : (Pi.single (reduceKeepExampleSplit.right 0) (1 : ℝ) : Vec ℝ 3) 0 = 0 := rfl
  have hr1 : (Pi.single (reduceKeepExampleSplit.right 1) (1 : ℝ) : Vec ℝ 3) 0 = 0 := rfl
  simp [ConZonotope.keepEmbed, ConZonotope.keepSlack, reduceKeepExample, blockLeft,
    hl, hr0, hr1] at h0
  -- the value: `2 γ₀ + 2 γ₁`
  have hx : (reduceKeepExample.reduceKeepBy reduceKeepExampleSplit).c +
      ∑ j, γ j • (reduceKeepExample.reduceKeepBy reduceKeepExampleSplit).G j ∈
      {x : Vec ℝ 1 | x 0 ≤ 2} := by
    show (_ + ∑ j : Fin (1 + 1), γ j • _ : Vec ℝ 1) 0 ≤ 2
    rw [Entrywise.add_sum_smul_apply, Fin.sum_univ_two]
    -- both generator entries and the centre, read off the definition
    have hG0 : (reduceKeepExample.reduceKeepBy reduceKeepExampleSplit).G
        (0 : Fin (1 + 1)) 0 = 2 := rfl
    have hG1 : (reduceKeepExample.reduceKeepBy reduceKeepExampleSplit).G
        (1 : Fin (1 + 1)) 0 = 2 := by
      have n0 : reduceKeepExampleSplit.right 0 ≠ 0 :=
        fun h => Nat.succ_ne_zero 0 (congrArg Fin.val h)
      have n1 : reduceKeepExampleSplit.right 1 ≠ 0 :=
        fun h => Nat.succ_ne_zero 1 (congrArg Fin.val h)
      simp only [ConZonotope.reduceKeepBy, Zonotope.reduceBy, ConZonotope.zonotope]
      rw [show (1 : Fin (1 + 1)) = Fin.natAdd 1 (0 : Fin 1) from rfl, Fin.append_right]
      simp [Fin.sum_univ_two, n0, n1]
      norm_num
    have hc : (reduceKeepExample.reduceKeepBy reduceKeepExampleSplit).c 0 = 0 := rfl
    rw [hG0, hG1, hc]
    linarith [(abs_le.mp h1).2]
  exact hx

/-- Through the enclosing zonotope, the constraint is gone and `4` is reached. -/
theorem reduceKeepExample_old_not_le :
    ¬ (reduceKeepExample.zonotope.reduceBy reduceKeepExampleSplit).conZonotope.construct
      ⊆ {x | x 0 ≤ 2} := by -- --- PROOF ---
  intro hsub
  -- the point `4` is the corner `(1, 1)` of the enclosing zonotope's reduction
  have hmem : (fun _ => 4 : Vec ℝ 1) ∈
      (reduceKeepExample.zonotope.reduceBy reduceKeepExampleSplit).conZonotope.construct := by
    refine (Set.ext_iff.mp (Zonotope.conZonotope_exact (α := Vec ℝ 1) _) _).mp ?_
    rw [Zonotope.mem_construct_iff]
    refine ⟨fun _ => 1, fun _ => by simp, fun i => ?_⟩
    -- the dropped generators sit at indices `1` and `2`, so neither is the first
    have n0 : reduceKeepExampleSplit.right 0 ≠ 0 :=
      fun h => Nat.succ_ne_zero 0 (congrArg Fin.val h)
    have n1 : reduceKeepExampleSplit.right 1 ≠ 0 :=
      fun h => Nat.succ_ne_zero 1 (congrArg Fin.val h)
    have i0 : i = 0 := Subsingleton.elim _ _
    subst i0
    -- the same entries as above, in the enclosing zonotope's reduction
    have hG0 : (reduceKeepExample.zonotope.reduceBy reduceKeepExampleSplit).G
        (0 : Fin (1 + 1)) 0 = 2 := rfl
    have hG1 : (reduceKeepExample.zonotope.reduceBy reduceKeepExampleSplit).G
        (1 : Fin (1 + 1)) 0 = 2 := by
      simp only [Zonotope.reduceBy, ConZonotope.zonotope]
      rw [show (1 : Fin (1 + 1)) = Fin.natAdd 1 (0 : Fin 1) from rfl, Fin.append_right]
      simp [Fin.sum_univ_two, n0, n1]
      norm_num
    have hc : (reduceKeepExample.zonotope.reduceBy reduceKeepExampleSplit).c 0 = 0 := rfl
    show (4 : ℝ) = (reduceKeepExample.zonotope.reduceBy reduceKeepExampleSplit).c 0
      + ∑ j : Fin (1 + 1), (reduceKeepExample.zonotope.reduceBy reduceKeepExampleSplit).G j 0 * 1
    rw [Fin.sum_univ_two, hG0, hG1, hc]
    norm_num
  have := hsub hmem
  norm_num at this

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
