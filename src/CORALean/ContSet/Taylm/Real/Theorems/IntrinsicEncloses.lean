import CORALean.ContSet.Taylm.Real.Operations.Intrinsic
import CORALean.ContSet.Taylm.Real.Theorems.ExpOuter
import CORALean.ContSet.Taylm.Real.Theorems.LogOuter
import CORALean.ContSet.Taylm.Real.Theorems.InvOuter
import CORALean.ContSet.Taylm.Real.Theorems.SqrtOuter
import CORALean.ContSet.Taylm.Real.Theorems.InvSqrtOuter
import CORALean.ContSet.Taylm.Real.Theorems.SinOuter
import CORALean.ContSet.Taylm.Real.Theorems.CosOuter
import CORALean.ContSet.Taylm.Real.Theorems.SinhOuter
import CORALean.ContSet.Taylm.Real.Theorems.CoshOuter
import CORALean.ContSet.Taylm.Real.Theorems.AsinOuter
import CORALean.ContSet.Taylm.Real.Theorems.AcosOuter
import CORALean.ContSet.Taylm.Real.Theorems.AtanOuter
import CORALean.ContSet.Taylm.Real.Theorems.TanOuter
import CORALean.ContSet.Taylm.Real.Theorems.TanhOuter

/-!
# An intrinsic encloses its function

Whenever `Taylm.intrinsic` returns a model, its condition held, and the operation's own outer
theorem says the model encloses the intrinsic of the enclosed function: the source's intrinsics, one
intrinsic at a time, as the induction of [1, Thm. 2] uses it.

## References

* [1] K. Makino and M. Berz. "Taylor Models and Other Validated Functional Inclusion
      Methods". International Journal of Pure and Applied Mathematics, 4(4):379-452, 2003.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Taylm.intrinsic_encloses {T T' : Taylm n} {f : Vec ℝ n → ℝ} (h : T.Encloses f)
    (s : Taylm.Intrinsic) (hs : T.intrinsic s = some T') :
    T'.Encloses fun t => s.fn (f t) := by -- --- PROOF ---
  -- the unguarded intrinsics return their model
  have hu : ∀ {U : Taylm n}, some U = some T' → U.Encloses (fun t => s.fn (f t)) →
      T'.Encloses fun t => s.fn (f t) := fun hU hE => by
    rw [Option.some.injEq] at hU; exact hU ▸ hE
  -- a guarded one returned a model, so its guard held
  have hg : ∀ {p : Prop} [Decidable p] {U : Taylm n}, (if p then some U else none) = some T' →
      (p → U.Encloses (fun t => s.fn (f t))) → T'.Encloses fun t => s.fn (f t) := by
    intro p _ U hU hE
    split_ifs at hU with hp
    exact hu hU (hE hp)
  -- each intrinsic by its own outer theorem
  cases s
  · exact hu hs (Taylm.exp_outer h)
  · exact hg hs fun hc => Taylm.log_outer h hc
  · exact hg hs fun hc => Taylm.inv_outer h hc
  · exact hg hs fun hc => Taylm.sqrt_outer h hc
  · exact hg hs fun hc => Taylm.invSqrt_outer h hc
  · exact hu hs (Taylm.sin_outer h)
  · exact hu hs (Taylm.cos_outer h)
  · exact hu hs (Taylm.sinh_outer h)
  · exact hu hs (Taylm.cosh_outer h)
  · exact hg hs fun hc => Taylm.asin_outer h hc
  · exact hg hs fun hc => Taylm.acos_outer h hc
  · exact hu hs (Taylm.atan_outer h)
  · exact hg hs fun hc => Taylm.tan_outer h hc
  · exact hu hs (Taylm.tanh_outer h)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
