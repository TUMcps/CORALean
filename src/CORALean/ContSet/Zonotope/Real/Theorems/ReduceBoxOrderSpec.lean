module

public import CORALean.ContSet.Zonotope.Real.Definitions.IsReduceBoxAdmissible
public import CORALean.ContSet.Zonotope.Real.Operations.ReduceBoxOrder
public import CORALean.ContSet.Zonotope.Real.Theorems.OfPointMemIff
public import CORALean.ContSet.Zonotope.Real.Theorems.ReduceBoxEqOfPoint

@[expose] public section

/-!
# The chosen order meets the error it was chosen for

What turns `reduceBox_eq_ofPoint` into a rule: `Z.h` itself is always
admissible once `0 ∈ B`, so the set `reduceBoxOrder` takes its infimum over is
never empty and the order it names actually meets `B`.

Needs `0 < n`: at `n = 0` no order drops `Z.h` generators unless `Z.h` already
is `0`, `o * n` staying `0` throughout, so the witness below would not go
through — a real restriction, not a formality dodged for convenience.

## Inputs
* `Z` – zonotope
* `B` – admissible bound

## Hypotheses
* `hn` – dimension positive
* `hB` – origin lies in `B`

## Conclusion
* the chosen order is admissible
-/

-- Authors:       Claude Opus 5
-- Written:       08-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- The order chosen for `B` is admissible for `B`, given `0 < n` and `0 ∈ B`:
`Z.h` is always an admissible witness, so the infimum meets `B` too. -/
theorem Zonotope.reduceBoxOrder_spec (Z : Zonotope (Vec ℝ n)) (hn : 0 < n)
    {B : Set (Vec ℝ n)} (hB : (0 : Vec ℝ n) ∈ B) : -- --- CONCL ---
    Z.IsReduceBoxAdmissible B (Z.reduceBoxOrder B) := by -- --- PROOF ---
  have hthr : Z.h ≤ Z.h * n := by
    calc Z.h = Z.h * 1 := (mul_one Z.h).symm
      _ ≤ Z.h * n := Nat.mul_le_mul (le_refl Z.h) hn
  have hmem : Z.IsReduceBoxAdmissible B Z.h := by
    show (Z.reduceBox Z.h).construct ⊆ B
    rw [Zonotope.reduceBox_eq_ofPoint hthr]
    intro x hx
    rw [Zonotope.mem_ofPoint_iff] at hx
    rwa [hx]
  have hne : {o : ℕ | Z.IsReduceBoxAdmissible B o}.Nonempty := ⟨Z.h, hmem⟩
  exact Nat.sInf_mem hne

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
