module

public import CORALean.ContSet.Taylm.Real.Operations.CosyGo
public import CORALean.ContSet.Taylm.Real.Theorems.GlobalMinLe
public import CORALean.ContSet.Taylm.Real.Theorems.GoLowerBoundLe
public import CORALean.ContSet.Taylm.Real.Theorems.GoodBoxHalve

@[expose] public section

/-!
# COSY-GO's lower end bounds the function

[1, Sec. 4]: the lower end of `cosyGo` is below the enclosed function on all of `X`.

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

theorem Taylm.cosyGo_le {T : Taylm n} {f : Vec ℝ n → ℝ} (h : T.Encloses f)
    {X : Fin n → Interval ℝ} (hX : Taylm.GoodBox X) (ε : ℝ) (ldbFuel fuel : ℕ) {t : Vec ℝ n}
    (ht : Taylm.InBox X t) : (T.cosyGo X ε ldbFuel fuel).inf ≤ f t :=
  Taylm.globalMin_le (fun _ β hB => Taylm.goodBox_halve hB β)
    (fun _ hB _ ht => Taylm.goLowerBound_le h ε ldbFuel hB ht) hX fuel ht

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
