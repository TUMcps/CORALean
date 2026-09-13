import CORALean.Global.DropIdx

/-!
# `ConPolyZono.reduceConE`

The generator exponent matrix of [1, Prop. 13], laid out to match `reduceConG`:
the exponent columns of the surviving generators, then the *constraint* exponent
columns of the surviving constraint generators.

That the second block comes from `EC` and not from `E` is the whole substitution
in one line — the generators replacing column `d` are the monomials the
eliminated constraint row supplies, and those are read off `EC`.

## References

* [1] N. Kochdumper and M. Althoff. "Constrained Polynomial Zonotopes". Acta
      Informatica, 2023.
-/

-- Authors:       Tobias Ladner
-- Written:       13-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The surviving generator exponent columns, then the surviving constraint
exponent columns. -/
def ConPolyZono.reduceConE {p h s : ℕ} (E : Fin p → Fin h → ℕ) (EC : Fin p → Fin s → ℕ)
    (d : Fin h) (t : Fin s) : Fin p → Fin ((h - 1) + (s - 1)) → ℕ :=
  fun k => Fin.addCases (fun i => E k (dropIdx d i)) (fun i => EC k (dropIdx t i))

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
