module

public import CORALean.ContSet.Taylm.Real.Operations.OptLinQuad
public import CORALean.ContSet.Taylm.Real.Theorems.CosyGoLe
public import CORALean.ContSet.Taylm.Real.Theorems.UminusOuter
public import Mathlib.Tactic.Linarith

@[expose] public section

/-!
# `Taylm.optLinQuad` bounds the enclosed function

Both ends by [1, Sec. 4]'s optimizer: on `T` for the lower one, on `-T`, which encloses `-f`, for
the upper one.

## Inputs
* `T` – Taylor model
* `f` – enclosed function
* `ε` – tolerance
* `ldbFuel` – fuel of the linear bounder
* `fuel` – step budget
* `t` – point

## Hypotheses
* `h` – the model encloses the function
* `ht` – point lies in the unit box

## Conclusion
* the optimizer's enclosure contains the function's value

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


-- =======================================  MAIN THEOREM  ======================================= --

theorem Taylm.optLinQuad_mem {T : Taylm n} {f : Vec ℝ n → ℝ} (h : T.Encloses f) (ε : ℝ)
    (ldbFuel fuel : ℕ) {t : Vec ℝ n} (ht : t ∈ Taylm.box n) :
    (T.optLinQuad ε ldbFuel fuel).inf ≤ f t ∧
      f t ≤ (T.optLinQuad ε ldbFuel fuel).sup := by -- --- PROOF ---
  have hX : Taylm.GoodBox (fun _ : Fin n => ⟨(-1 : ℝ), (1 : ℝ)⟩) := fun _ => by norm_num
  have htX : Taylm.InBox (fun _ : Fin n => ⟨(-1 : ℝ), (1 : ℝ)⟩) t := fun k => abs_le.1 (ht k)
  have h1 := Taylm.cosyGo_le h hX ε ldbFuel fuel htX
  have h2 := Taylm.cosyGo_le (Taylm.uminus_outer h) hX ε ldbFuel fuel htX
  simp only [Taylm.optLinQuad]
  constructor <;> linarith

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
