module

public import CORALean.ContDynamics.LinearSys.LinearSys

@[expose] public section

/-!
# The canonical form of a linear system

CORA's `canonicalForm` [1]: `Ax + B u + c + E w → Ax + u'` with `u' ∈ U_ + u_`, and
`Cx + D u + k + F v → Cx + v'` with `v' ∈ V_ + v_`, the system returned
`(A, I, 0, C, 0, 0, 0, I)`, as CORA builds it. A real-layer definition: the vectors `u_`, `v_`
are real arithmetic, and `Recenter` is what `U - centerU` needs. One piece of the piecewise
constant `uVec`, `vVec` at a time: CORA's extra zero column for the `steps + 1` output
times only repeats the formula with `uVec = 0`.

## References

* [1] `contDynamics/@linearSys/canonicalForm.m`
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   14-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix ContSet Scalar Plus Mtimes

variable {n : ℕ}
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]
variable [∀ n, Plus (S n) (Vec ℝ n)] [Mtimes (Mat ℝ) S]
variable [∀ n, Recenter (S n) (Vec ℝ n)] [∀ n, OfPoint (S n) (Vec ℝ n)]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `[linsys_, U_, u_, V_, v_] = canonicalForm(linsys, U, uVec, W, V, vVec)`, line by line. -/
noncomputable def LinearSys.canonicalForm (sys : LinearSys ℝ n) (U : S sys.m) (uVec : Vec ℝ sys.m)
    (W : S sys.r) (V : S sys.s) (vVec : Vec ℝ sys.s) :
    LinearSys ℝ n × S n × Vec ℝ n × S sys.q × Vec ℝ sys.q :=
  let centerU := Recenter.center U                                   -- read out all centers
  let centerW := Recenter.center W
  let centerV := Recenter.center V
  let U₀ := Recenter.recenter U                                      -- U - centerU
  let W₀ := Recenter.recenter W                                      -- W - centerW
  let V₀ := Recenter.recenter V                                      -- V - centerV
  let v_ := sys.D *ᵥ uVec + sys.k + sys.F *ᵥ (centerV + vVec)        -- offset on the output
  let V_ := plus (mtimes sys.D (plus U₀ (OfPoint.ofPoint centerU)))
    (mtimes sys.F V₀)                                                -- D (U + centerU) + F V
  let u_ := sys.B *ᵥ uVec + sys.B *ᵥ centerU + sys.c + sys.E *ᵥ centerW  -- offset on the state
  let U_ := plus (mtimes sys.B U₀) (mtimes sys.E W₀)                 -- B U + E W
  let sys_ : LinearSys ℝ n :=                                        -- A, I, 0, C, 0, 0, 0, I
    ⟨n, sys.q, n, sys.q, sys.A, 1, 0, sys.C, 0, 0, 0, 1⟩
  (sys_, U_, u_, V_, v_)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
