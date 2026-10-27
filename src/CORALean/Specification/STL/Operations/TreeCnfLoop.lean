module

public import CORALean.Specification.STL.Operations.TreeCnfRewrite
public import CORALean.Global.StepOf

@[expose] public section

/-!
# The rewrite loop of the conjunctive normal form

`@stl/conjunctiveNormalForm.m`: `while true`, rewrite and stop at the first pass that counts no
distribution. The loop ends because every pass that distributes lowers the weight of the formula
(`&` adds and adds one, `|` multiplies, a leaf weighs two): distributing `(a & b) | c` replaces a
product `(a + b + 1) * c` by a sum `a * c + b * c + 1`.

## Inputs
* `φ` – formula

## Output
* the formula rewritten until no change remains
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open scoped NNReal

variable {τ κ : Type} {n : ℕ}


-- ------------------------------------------  STEPS  ------------------------------------------- --

-- the weight of a formula: `&` adds, `|` multiplies, a leaf weighs two
@[step_of STL.Tree.cnfLoop]
def STL.Tree.step_cnfWeight : STL.Tree τ κ n → ℕ
  | .and φ ψ => step_cnfWeight φ + step_cnfWeight ψ + 1
  | .or φ ψ => step_cnfWeight φ * step_cnfWeight ψ
  | _ => 2


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `while true [obj,cnt] = aux_rewrite(obj); if cnt == 0 break; end end` of
`conjunctiveNormalForm.m`, with the NNF step left to the caller. -/
def STL.Tree.cnfLoop (φ : STL.Tree τ κ n) : STL.Tree τ κ n :=
  let res := (φ.cnfRewrite).1
  let cnt := (φ.cnfRewrite).2
  if _ : cnt = 0 then res else cnfLoop res
termination_by φ.step_cnfWeight
decreasing_by
  rename_i h
  -- every formula weighs at least two
  have htwo' : ∀ φ : STL.Tree τ κ n, 2 ≤ φ.step_cnfWeight := by
    intro φ
    induction φ with
    | and φ ψ ihφ ihψ => simp only [STL.Tree.step_cnfWeight]; omega
    | or φ ψ ihφ ihψ => simp only [STL.Tree.step_cnfWeight]; nlinarith
    | _ => simp [STL.Tree.step_cnfWeight]
  have htwo : PLift (∀ φ : STL.Tree τ κ n, 2 ≤ φ.step_cnfWeight) := ⟨htwo'⟩
  clear htwo'
  -- a pass never raises the weight, and lowers it when it distributes
  have hweight : ∀ φ : STL.Tree τ κ n,
      (φ.cnfRewrite).1.step_cnfWeight ≤ φ.step_cnfWeight ∧
        ((φ.cnfRewrite).2 ≠ 0 →
          (φ.cnfRewrite).1.step_cnfWeight < φ.step_cnfWeight) := by
    clear * - htwo
    intro φ
    induction φ with
    | or φ ψ ihφ ihψ =>
      have h₁ := htwo.down (φ.cnfRewrite).1
      have h₂ := htwo.down (ψ.cnfRewrite).1
      obtain ⟨a₁, a₂⟩ := ihφ
      obtain ⟨b₁, b₂⟩ := ihψ
      simp only [STL.Tree.cnfRewrite]
      split
      all_goals simp_all only [STL.Tree.step_cnfWeight]
      -- both operands became `&`: four clauses replace the product
      · rename_i ψ' _ _ _ l₁ l₂ r₁ r₂ _ _
        have t₁ := htwo.down l₁
        have t₂ := htwo.down l₂
        have t₃ := htwo.down r₁
        have t₄ := htwo.down r₂
        have key := Nat.mul_le_mul a₁ b₁
        refine ⟨?_, fun _ => ?_⟩ <;> nlinarith
      -- only the left operand is an `&`
      · rename_i ψ' _ _ _ l₁ l₂ _ _
        have key := Nat.mul_le_mul a₁ b₁
        refine ⟨?_, fun _ => ?_⟩ <;> nlinarith
      -- only the right operand is an `&`
      · rename_i _ _ _ r₁ r₂ φ' ψ' _ _
        have key := Nat.mul_le_mul a₁ b₁
        refine ⟨?_, fun _ => ?_⟩ <;> nlinarith
      -- nothing distributed here: the weight drops where an operand's did
      · refine ⟨Nat.mul_le_mul a₁ b₁, fun h => ?_⟩
        by_cases c : φ.cnfRewrite.2 = 0
        · have := Nat.mul_le_mul (a₁) (b₂ (by omega))
          nlinarith
        · have := Nat.mul_le_mul (a₂ c) b₁
          nlinarith
    -- the case of an `&`
    | and φ ψ ihφ ihψ =>
      obtain ⟨a₁, a₂⟩ := ihφ
      obtain ⟨b₁, b₂⟩ := ihψ
      simp only [STL.Tree.cnfRewrite, STL.Tree.step_cnfWeight]
      refine ⟨by omega, fun h => ?_⟩
      by_cases hφ : (φ.cnfRewrite).2 = 0
      · have := b₂ (by omega); omega
      · have := a₂ hφ; omega
    | _ => simp [STL.Tree.cnfRewrite]
  exact (hweight φ).2 h

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
