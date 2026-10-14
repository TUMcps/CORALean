module

public import CORALean.ContSet.Capsule.Real.Counterexamples.MtimesCora
public import CORALean.Global.Cost

@[expose] public section

/-!
# `Capsule.mtimesCoraCost`

Asserted, not proved: `Operations/MtimesCora.lean` takes the eigenvalue `lam` as
an argument, so computing it is the caller's cost and not this operation's. What
remains is two `Cost.matVec m n` and one product for the radius.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       10-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

/-- What `Capsule.mtimesCora` costs at `M : Mat ℝ m n`, `lam` given. -/
def Capsule.mtimesCoraCost (m n : ℕ) : Cost := (2 : ℕ) • Cost.matVec m n + ⟨1⟩

/-- Monotone in both dimensions. -/
theorem Capsule.mtimesCoraCost_mono {m m' n n' : ℕ} (hm : m ≤ m') (hn : n ≤ n') :
    Capsule.mtimesCoraCost m n ≤ Capsule.mtimesCoraCost m' n' := by
  have := Nat.mul_le_mul hm hn
  simp only [Capsule.mtimesCoraCost, Cost.le_iff, Cost.ops_add, Cost.ops_smul, Cost.matVec]
  omega

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
