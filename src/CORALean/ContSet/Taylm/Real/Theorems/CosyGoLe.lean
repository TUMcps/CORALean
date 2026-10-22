module

public import CORALean.ContSet.Taylm.Real.Operations.CosyGo
public import CORALean.ContSet.Taylm.Real.Theorems.GlobalMinLe
public import CORALean.ContSet.Taylm.Real.Theorems.GoLowerBoundLe
public import CORALean.ContSet.Taylm.Real.Definitions.GoodBox
public import CORALean.ContSet.Taylm.Real.Operations.HalveBox
public import Mathlib.Tactic.Linarith

@[expose] public section

/-!
# COSY-GO's lower end bounds the function

[1, Sec. 4]: the lower end of `cosyGo` is below the enclosed function on all of `X`.

## Inputs
* `T` – Taylor model
* `f` – enclosed function
* `X` – domain box
* `ε` – tolerance
* `ldbFuel` – fuel of the linear bounder
* `fuel` – step budget
* `t` – point

## Hypotheses
* `h` – the model encloses the function
* `hX` – the box lies in the unit box
* `ht` – point lies in the box

## Conclusion
* the lower end of the optimizer's enclosure is at most the function's value

## References

* [1] K. Makino and M. Berz. "Verified Global Optimization with Taylor Model-based Range
      Bounders". Transactions on Computers, 11(4):1611-1618, 2005.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   14-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- Halving keeps a sub-box of the normalized box. -/
theorem Taylm.aux_goodBox_halve {B : Fin n → Interval ℝ} (hB : Taylm.GoodBox B)
    (β : Fin n) : -- --- CONCL ---
    Taylm.GoodBox (Taylm.halveBox B β).1 ∧
      Taylm.GoodBox (Taylm.halveBox B β).2 := by -- --- PROOF ---
  have hm := hB β
  constructor <;> intro k <;> simp only [Taylm.halveBox, Function.update_apply] <;>
    split_ifs with hk
  · subst hk; simp only; constructor <;> (try constructor) <;> (try constructor) <;> linarith
  · exact hB k
  · subst hk; simp only; constructor <;> (try constructor) <;> (try constructor) <;> linarith
  · exact hB k


-- =======================================  MAIN THEOREM  ======================================= --

theorem Taylm.cosyGo_le {T : Taylm n} {f : Vec ℝ n → ℝ} (h : T.Encloses f)
    {X : Fin n → Interval ℝ} (hX : Taylm.GoodBox X) (ε : ℝ) (ldbFuel fuel : ℕ) {t : Vec ℝ n}
    (ht : Taylm.InBox X t) : (T.cosyGo X ε ldbFuel fuel).inf ≤ f t :=
  Taylm.globalMin_le (fun _ β hB => Taylm.aux_goodBox_halve hB β)
    (fun _ hB _ ht => Taylm.goLowerBound_le h ε ldbFuel hB ht) hX fuel ht

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
