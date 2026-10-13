import CORALean.ContDynamics.LinearSys.LinearSys
import CORALean.ContDynamics.OutputEq.OutputEq

/-!
# The canonical form of a linear system

CORA's `canonicalForm` [1]: `Ax + B u + c + E w → Ax + u'` with `u' ∈ U_ + u_`, and
`Cx + D u + k + F v → Cx + v'` with `v' ∈ V_ + v_`. The system record is `LinearSys`, which
keeps `A` only, so `B`, `c`, `D`, `k`, `E`, `F` are arguments, `C` and `D` in `OutputEq`;
the system returned is `(A, I, 0, C, 0, 0, 0, I)`, so what is returned of it is `A` and the
output equation `(C, 0)`. A real-layer definition: the vectors `u_`, `v_` are real
arithmetic, and `Recentre` is what `U - centerU` needs. One piece of the piecewise
constant `uVec`, `vVec` at a time: CORA's extra zero column for the `steps + 1` output
times only repeats the formula with `uVec = 0`.

## References

* [1] `contDynamics/@linearSys/canonicalForm.m`
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix ContSet Scalar Plus Mtimes

variable {n m q r s : ℕ}
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]
variable [∀ n, Plus (S n) (Vec ℝ n)] [Mtimes (Mat ℝ) S]
variable [∀ n, Recentre (S n) (Vec ℝ n)] [∀ n, OfPoint (S n) (Vec ℝ n)]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `[linsys_, U_, u_, V_, v_] = canonicalForm(linsys, U, uVec, W, V, vVec)`, line by line. -/
noncomputable def LinearSys.canonicalForm (sys : LinearSys ℝ n) (B : Mat ℝ n m) (c : Vec ℝ n)
    (out : OutputEq ℝ n m r) (k : Vec ℝ r) (E : Mat ℝ n q) (F : Mat ℝ r s)
    (U : S m) (uVec : Vec ℝ m) (W : S q) (V : S s) (vVec : Vec ℝ s) :
    LinearSys ℝ n × OutputEq ℝ n n r × S n × Vec ℝ n × S r × Vec ℝ r :=
  let centerU := Recentre.centre U                                   -- read out all centers
  let centerW := Recentre.centre W
  let centerV := Recentre.centre V
  let U₀ := Recentre.recentre U                                      -- U - centerU
  let W₀ := Recentre.recentre W                                      -- W - centerW
  let V₀ := Recentre.recentre V                                      -- V - centerV
  let v_ := out.D *ᵥ uVec + k + F *ᵥ (centerV + vVec)                -- offset on the output
  let V_ := plus (mtimes out.D (plus U₀ (OfPoint.ofPoint centerU)))
    (mtimes F V₀)                                                    -- D (U + centerU) + F V
  let u_ := B *ᵥ uVec + B *ᵥ centerU + c + E *ᵥ centerW              -- offset on the state
  let U_ := plus (mtimes B U₀) (mtimes E W₀)                         -- B U + E W
  (⟨sys.A⟩, ⟨out.C, 0⟩, U_, u_, V_, v_)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
