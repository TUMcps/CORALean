module

public import CORALean.Global.Float.Interfaces
public import CORALean.Global.Tensor

@[expose] public section

/-!
# A Krylov subspace of a vector, as the float order search returns it

The order `k` the order search for [1, Thm. 3]'s error bound stopped at, whether its test accepted
it, the bound found for it, the scale `ν = ‖c‖` of the first basis vector, the basis vectors
`v(1), …, v(k+1)` (indices `0, …, k`) and the Hessenberg entries `h_{i,j}` (at `(i - 1, j - 1)`). A
bound that was not accepted is not a certificate.

## References

* [1] [T. Jawecki, W. Auzinger and O. Koch. "Computable upper error bounds for Krylov approximations
      to matrix exponentials and associated φ-functions". BIT Numerical Mathematics,
      2020.](../../../../../../references/2020/jawecki-bit-krylov-error-bounds.md)
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       11-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float


-- ========================================  MAIN TYPE  ========================================= --

/-- A Krylov subspace with its order, the bound found for it and whether the test accepted it. -/
structure Krylov.SubspaceFloat (𝕋 : Type) (n : ℕ) where
  order : ℕ
  ok : Bool
  bound : 𝕋
  ν : 𝕋
  V : ℕ → Vector 𝕋 n
  H : ℕ → ℕ → 𝕋

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
