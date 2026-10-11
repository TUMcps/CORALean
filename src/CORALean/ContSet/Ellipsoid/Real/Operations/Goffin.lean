import CORALean.ContSet.Ellipsoid.Real.Operations.GoffinCut

/-!
# Goffin's algorithm for zonotopes

[1, Sec. 4.6 (algorithm)]: from `E(E₀, 0) ⊇ Z` (Sec. 4.1), iteration `j` maps by
`Φ : ξ ↦ E_j^{-1/2}ξ`, runs the test (17) with `γ = 1/√(n(1+ε))` on `Z′ = ΦZ`, and either stops
— `E(E_j/(1+ε), 0)` is then an `ε`-approximate Löwner–John ellipse of `Z` — or cuts with the
separator `a` of Sec. 4.5 (`goffinCut`). The test together with the separation algorithm is the
argument `test`: `none` when (17) passes at `E_j`, `some a` otherwise; it is a linear program
per axis and per separator, outside what a definition here computes. A stopped run stays at its
last `E_j`, so `goffin … j` is `E_j` for every `j` up to the stop.

## References

* [1] M. Černý. "Goffin's algorithm for zonotopes". Kybernetika, 48(5):890-906, 2012.
-/

-- Authors:       Tobias Ladner
-- Written:       11-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- [1, Sec. 4.6 (algorithm)]: `E_j`, stopping at the first `j` whose test passes. -/
noncomputable def Ellipsoid.goffin (ε : ℝ) (test : Mat ℝ n n → Option (Vec ℝ n))
    (E₀ : Mat ℝ n n) : ℕ → Mat ℝ n n
  | 0 => E₀
  | j + 1 =>
    let Ej := Ellipsoid.goffin ε test E₀ j
    match test Ej with
    | none => Ej
    | some a => Ellipsoid.goffinCut ε Ej a

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
