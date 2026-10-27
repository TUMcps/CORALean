module

public import CORALean.Specification.STL.Operations.TreeDnfRewrite
public import CORALean.Global.StepOf

@[expose] public section

/-!
# The rewrite loop of the disjunctive normal form

`@stl/disjunctiveNormalForm.m`: `while true`, rewrite and stop at the first pass that counts no
distribution. The loop ends because every pass that distributes lowers the weight of the formula
(`|` adds and adds one, `&` multiplies, a leaf weighs two): distributing `(a | b) & c` replaces a
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

-- the weight of a formula: `|` adds, `&` multiplies, a leaf weighs two
@[step_of STL.Tree.dnfLoop]
def STL.Tree.step_dnfWeight : STL.Tree τ κ n → ℕ
  | .or φ ψ => step_dnfWeight φ + step_dnfWeight ψ + 1
  | .and φ ψ => step_dnfWeight φ * step_dnfWeight ψ
  | _ => 2


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `while true [obj,cnt] = aux_rewrite(obj); if cnt == 0 break; end end` of
`disjunctiveNormalForm.m`, with the NNF step left to the caller. -/
def STL.Tree.dnfLoop (φ : STL.Tree τ κ n) : STL.Tree τ κ n :=
  let res := (φ.dnfRewrite).1
  let cnt := (φ.dnfRewrite).2
  if _ : cnt = 0 then res else dnfLoop res
termination_by φ.step_dnfWeight
decreasing_by
  rename_i h
  -- every formula weighs at least two
  have htwo' : ∀ φ : STL.Tree τ κ n, 2 ≤ φ.step_dnfWeight := by
    intro φ
    induction φ with
    | or φ ψ ihφ ihψ => simp only [STL.Tree.step_dnfWeight]; omega
    | and φ ψ ihφ ihψ => simp only [STL.Tree.step_dnfWeight]; nlinarith
    | _ => simp [STL.Tree.step_dnfWeight]
  have htwo : PLift (∀ φ : STL.Tree τ κ n, 2 ≤ φ.step_dnfWeight) := ⟨htwo'⟩
  clear htwo'
  -- a pass never raises the weight, and lowers it when it distributes
  have hweight : ∀ φ : STL.Tree τ κ n,
      (φ.dnfRewrite).1.step_dnfWeight ≤ φ.step_dnfWeight ∧
        ((φ.dnfRewrite).2 ≠ 0 →
          (φ.dnfRewrite).1.step_dnfWeight < φ.step_dnfWeight) := by
    clear * - htwo
    intro φ
    induction φ with
    | and φ ψ ihφ ihψ =>
      have h₁ := htwo.down (φ.dnfRewrite).1
      have h₂ := htwo.down (ψ.dnfRewrite).1
      obtain ⟨a₁, a₂⟩ := ihφ
      obtain ⟨b₁, b₂⟩ := ihψ
      simp only [STL.Tree.dnfRewrite]
      split
      all_goals simp_all only [STL.Tree.step_dnfWeight]
      -- both operands became `|`: four cubes replace the product
      · rename_i ψ' _ _ _ l₁ l₂ r₁ r₂ _ _
        have t₁ := htwo.down l₁
        have t₂ := htwo.down l₂
        have t₃ := htwo.down r₁
        have t₄ := htwo.down r₂
        have key := Nat.mul_le_mul a₁ b₁
        refine ⟨?_, fun _ => ?_⟩ <;> nlinarith
      -- only the left operand is an `|`
      · rename_i ψ' _ _ _ l₁ l₂ _ _
        have key := Nat.mul_le_mul a₁ b₁
        refine ⟨?_, fun _ => ?_⟩ <;> nlinarith
      -- only the right operand is an `|`
      · rename_i _ _ _ r₁ r₂ φ' ψ' _ _
        have key := Nat.mul_le_mul a₁ b₁
        refine ⟨?_, fun _ => ?_⟩ <;> nlinarith
      -- nothing distributed here: the weight drops where an operand's did
      · refine ⟨Nat.mul_le_mul a₁ b₁, fun h => ?_⟩
        by_cases c : φ.dnfRewrite.2 = 0
        · have := Nat.mul_le_mul (a₁) (b₂ (by omega))
          nlinarith
        · have := Nat.mul_le_mul (a₂ c) b₁
          nlinarith
    -- the case of an `|`
    | or φ ψ ihφ ihψ =>
      obtain ⟨a₁, a₂⟩ := ihφ
      obtain ⟨b₁, b₂⟩ := ihψ
      simp only [STL.Tree.dnfRewrite, STL.Tree.step_dnfWeight]
      refine ⟨by omega, fun h => ?_⟩
      by_cases hφ : (φ.dnfRewrite).2 = 0
      · have := b₂ (by omega); omega
      · have := a₂ hφ; omega
    | _ => simp [STL.Tree.dnfRewrite]
  exact (hweight φ).2 h

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
