module

public import CORALean.ContSet.ConPolyZono.Real.Operations.UnionConCoef

@[expose] public section

/-!
# `ConPolyZono.unionConInt`

The selector row of [1, Thm. 1], scaled to integers. Over ℝ its coefficients are
`1`, `1/(2p₁)`, `1/(2p₂)` and `1/(4p₁p₂)`, which no binary format holds, and a
rounded coefficient would change the constraint without any set to pay it into.
Scaling the row by `4 max(1,p₁) max(1,p₂)` makes every coefficient an integer, and
`b = 0` is unchanged by a scale; `max` only keeps the scale non-zero when an
operand has no factors, where the groups it would divide are empty anyway.

## References

* [1] N. Kochdumper and M. Althoff. "Constrained Polynomial Zonotopes". Acta
      Informatica, 2023.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      19-October-2026 (Tobias Ladner)


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The selector row's coefficients, each times `4 max(1,p₁) max(1,p₂)`. -/
def ConPolyZono.unionConInt (p₁ p₂ : ℕ) :
    Fin (2 + (p₁ + p₁ + (p₂ + p₂ + (p₁ * p₂ + p₁ * p₂)))) → ℤ :=
  Fin.append ![4 * (max 1 p₁ : ℕ) * (max 1 p₂ : ℕ), -(4 * (max 1 p₁ : ℕ) * (max 1 p₂ : ℕ))]
    (Fin.append
      (Fin.append (fun _ => 2 * (max 1 p₂ : ℕ)) (fun _ => -(2 * (max 1 p₂ : ℕ))))
      (Fin.append
        (Fin.append (fun _ => -(2 * (max 1 p₁ : ℕ))) (fun _ => -(2 * (max 1 p₁ : ℕ))))
        (Fin.append (fun _ => -1) (fun _ => 1))))

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
