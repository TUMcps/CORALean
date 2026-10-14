module

public import CORALean.ContSet.Interval.Real.Operations.Times
public import CORALean.ContSet.Interval.Real.Theorems.TimesExact
public import CORALean.Specification.SyntaxTree.Definitions.Basic
public import CORALean.Specification.SyntaxTree.Operations.Basic
public import CORALean.Specification.SyntaxTree.SyntaxTree

@[expose] public section

/-!
# The product of two intervals holds the product

`I * J` holds `a * b`.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {n : ℕ} {B : Real.Interval (Vec ℝ n)} {t : SyntaxTree n}


-- =======================================  MAIN THEOREM  ======================================= --

/-- `I * J` holds `a * b`. -/
theorem SyntaxTree.contains_times {I J : Dom} {a b : ℝ} (ha : Dom.contains I a)
    (hb : Dom.contains J b) : Dom.contains (Real.Interval.times I J) (a * b) := by -- --- PROOF ---
  have hI : I.IsNonempty := fun i => by
    obtain rfl : i = 0 := Subsingleton.elim i 0
    exact ha.1.trans ha.2
  have hJ : J.IsNonempty := fun i => by
    obtain rfl : i = 0 := Subsingleton.elim i 0
    exact hb.1.trans hb.2
  have hx : (fun _ => a : Vec ℝ 1) ∈ I.construct := by
    intro i; obtain rfl : i = 0 := Subsingleton.elim i 0; exact ha
  have hy : (fun _ => b : Vec ℝ 1) ∈ J.construct := by
    intro i; obtain rfl : i = 0 := Subsingleton.elim i 0; exact hb
  have hm : (fun i => (fun _ => a : Vec ℝ 1) i * (fun _ => b : Vec ℝ 1) i : Vec ℝ 1) ∈
      (I.times J).construct := by
    rw [Real.Interval.times_exact hI hJ]; exact ⟨_, hx, _, hy, rfl⟩
  exact hm 0

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
