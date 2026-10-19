module

public import CORALean.NN.Operations.RefineVerify
public import CORALean.NN.Theorems.RefineVerifyFromSound

@[expose] public section

/-!
# Automatic abstraction refinement is sound

[1, Alg. 3]: `VERIFIED` means every output of the network on the input set misses the unsafe
set `Sᵤ`, whatever the refinement rule and however many iterations it took, provided the
disjointness test is sound. `refineVerifyFrom_sound` at line 1's order pattern.

## References

* [1] T. Ladner and M. Althoff. "Automatic Abstraction Refinement in Neural
      Network Verification using Sensitivity Analysis". HSCC 2023.
-/

-- Authors:       Claude Opus 5.5
-- Written:       08-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open ContSet

variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] [∀ n, Reduce (S n) (Vec ℝ n)]
variable {n m : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Alg. 3]: `VERIFIED` means no output on the input set is unsafe. -/
theorem RefinableNetwork.refineVerify_sound (rn : RefinableNetwork S n m) (ρ : ℕ) {X : S n}
    {Su : Set (Vec ℝ m)} {isDisjoint : S m → Bool}
    (hdis : ∀ Y, isDisjoint Y = true → ∀ y ∈ construct Y, y ∉ Su)
    (refineStep : Schedule → Schedule) {I : ℕ}
    (h : rn.refineVerify ρ X isDisjoint refineStep I = true) : -- --- CONCL ---
    ∀ x ∈ construct X, rn.eval x ∉ Su :=
  rn.refineVerifyFrom_sound ρ hdis refineStep I _ h

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
