import CORALean.ContSet.ContSet.ContSet

/-!
# `abstrErrLoop`, the abstraction error's fixed point

Lines 8-11 of [1, Alg. 1], which its `Alg. 2` line 7 names `abstrErrLoop`:
guess an applied error, compute the true one it induces, and enlarge and retry
until the true error sits inside the applied one. What comes back is the *true*
error — the tighter of the two — and line 12 is what spends it.

`enlarge` and the true-error map `Φ` are supplied. Neither is a property of a
set: `enlarge` is [1]'s "constant factor greater than 1", and `Φ` is the
`abstrErr` of whichever abstraction the caller runs, of which this tree has
`abstrErr` and `abstrErrLin`. Routing the containment test through a `Bool`
keeps the loop runnable, as `Alg. 3` of the CDC paper is.

`Ψ ⊄ Ψ̄` is a loop with no stated iteration count, so `fuel` is an argument and
the result an `Option`; `abstrErrPolySearch` beside it is the same shape for
the polynomial abstraction. `Ψ̄` is no Lean identifier, so the applied error is
`Ψapp` and the true one `Ψtrue`.

## References

* [1] M. Wetzlinger, A. Kulmburg, A. Le Penven and M. Althoff. "Adaptive
      Reachability Algorithms for Nonlinear Systems Using Abstraction Error
      Analysis". Nonlinear Analysis: Hybrid Systems, vol. 46, 2022, p. 101252.
-/

-- Authors:       Tobias Ladner
-- Written:       18-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {n : ℕ}
variable {S : ℕ → Type}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The first true error the applied error it was computed from contains, and
`none` once `fuel` enlargements have failed to reach one. -/
def abstrErrLoop (sub : S n → S n → Bool) (enlarge : S n → S n) (Φ : S n → S n) :
    S n → ℕ → Option (S n)
  | _, 0 => none
  | Ψ, k + 1 =>
    let Ψapp := enlarge Ψ                              -- 9. Ψ̄ ← enlarge(Ψ)
    let Ψtrue := Φ Ψapp                                -- 10. Ψ ← abstrErr(R_lin(τ), Ψ̄, κ)
    if sub Ψtrue Ψapp then some Ψtrue                  -- 11. while Ψ ⊄ Ψ̄
    else abstrErrLoop sub enlarge Φ Ψtrue k

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
