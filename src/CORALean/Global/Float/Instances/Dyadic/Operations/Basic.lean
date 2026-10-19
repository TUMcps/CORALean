module

public import CORALean.Global.Float.Instances.Dyadic.Dyadic
public import CORALean.Global.Float.Instances.Dyadic.Operations.CoarsenUp
public import CORALean.Global.Float.Instances.Dyadic.Operations.ExactAdd
public import CORALean.Global.Float.Instances.Dyadic.Operations.LeShl
public import CORALean.Global.Float.Instances.Dyadic.Operations.QuotDown

@[expose] public section

/-!
# `Global/Float/Instances/Dyadic/Operations`: small declarations

One section per declaration, at most five code lines each; alphabetical, after the
sections each one uses (CONTRIBUTING, "Small declarations").
-/


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --


namespace CORALean.Float

namespace Dyadic

-- rounded again: the quotient carries `p` bits and up to the dividend's length more
variable {p : ℕ}


-- =======================================  `alignGuard`  ======================================= --
-- Authors:       Claude Sonnet 5.5
-- Written:       10-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- The widest alignment `addUp`/`addDown` form: well beyond the mantissa width, so that no
operand pair on the `p`-bit grid is coarsened unless the smaller one is far below the ulp of
the sum, yet a constant, so `2 ^ alignGuard p` is small. -/
def alignGuard (p : ℕ) : ℕ := 4 * p + 64


-- ========================================  `alignExp`  ======================================== --
-- Authors:       Claude Sonnet 5.5
-- Written:       10-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- Both operands of `addUp`/`addDown` are coarsened to `alignGuard p` binades below the larger
exponent, so the alignment inside the exact sum spans at most `alignGuard p` bits whatever the
operands' exponents. -/
def alignExp (a b : Dyadic p) : ℤ := max a.exponent b.exponent - alignGuard p


-- ======================================  `coarsenDown`  ======================================= --
-- Authors:       Claude Sonnet 5.5
-- Written:       10-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- The mirror image of `coarsenUp`: `d` rounded down to the grid of exponent `e` by a bit shift,
the floor of the mantissa at the raised exponent. -/
def coarsenDown (e : ℤ) (d : Dyadic p) : Dyadic p :=
  ⟨d.mantissa >>> (e - d.exponent).toNat, max d.exponent e⟩


-- ========================================  `exactMul`  ======================================== --
-- Authors:       Claude Sonnet 5
-- Written:       16-August-2026
-- Last update:   02-September-2026
-- Reviewed:      ---

/-- Closed on dyadics, so this loses nothing; only the mantissa grows, to `2p`
bits at a `p`-bit product. `MulUp`/`MulDown` round it back down to `p`. -/
def exactMul (a b : Dyadic p) : Dyadic p :=
  ⟨a.mantissa * b.mantissa, a.exponent + b.exponent⟩


-- ==========================================  `half`  ========================================== --
-- Authors:       Claude Sonnet 5
-- Written:       16-August-2026
-- Last update:   02-September-2026
-- Reviewed:      ---

/-- Exact: the mantissa is untouched. -/
def half (a : Dyadic p) : Dyadic p := ⟨a.mantissa, a.exponent - 1⟩


-- =========================================  `leShr`  ========================================== --
-- Authors:       Claude Sonnet 5.5
-- Written:       10-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- The mirror image of `leShl`, by negating both sides. -/
def leShr (m n : ℤ) (g : ℕ) : Bool := leShl (-n) (-m) g


-- ==========================================  `neg`  =========================================== --
-- Authors:       Claude Sonnet 5
-- Written:       16-August-2026
-- Last update:   02-September-2026
-- Reviewed:      ---

/-- Exact: flips the mantissa's sign and leaves the exponent alone. -/
def neg (d : Dyadic p) : Dyadic p := ⟨-d.mantissa, d.exponent⟩


-- =========================================  `quotUp`  ========================================= --
-- Authors:       Claude Sonnet 5
-- Written:       16-August-2026
-- Last update:   25-September-2026
-- Reviewed:      ---

/-- `quotDown`'s mirror, at the same shift: negates the shifted dividend twice,
turning the floor into a ceiling exactly as `roundUp` does. -/
def quotUp (a b : Dyadic p) : Dyadic p :=
  ⟨-(-(a.mantissa * 2 ^ (p + b.mantissa.natAbs.log2 + 1)) / b.mantissa),
    a.exponent - b.exponent - ((p + b.mantissa.natAbs.log2 + 1 : ℕ) : ℤ)⟩


-- =========================================  `shift`  ========================================== --
-- Authors:       Claude Sonnet 5
-- Written:       16-August-2026
-- Last update:   02-September-2026
-- Reviewed:      ---

/-- What `roundUp`/`roundDown` drop from the mantissa to bring it back to `p`
bits. -/
def shift (d : Dyadic p) : ℕ := Nat.log2 d.mantissa.natAbs + 1 - p


-- =======================================  `roundDown`  ======================================== --
-- Authors:       Claude Sonnet 5
-- Written:       16-August-2026
-- Last update:   02-September-2026
-- Reviewed:      19-October-2026 (Tobias Ladner)

/-- Integer `/` is floor division on ℤ, so shifting the mantissa right by `shift`
bits and raising the exponent to match rounds toward `-∞`. -/
def roundDown (d : Dyadic p) : Dyadic p :=
  ⟨d.mantissa / 2 ^ d.shift, d.exponent + d.shift⟩


-- ========================================  `addDown`  ========================================= --
-- Authors:       Claude Sonnet 5
-- Written:       16-August-2026
-- Last update:   02-September-2026
-- Reviewed:      ---

/-- `exactAdd` of both operands coarsened downward (`coarsenDown`: a no-op unless one sits more than
`alignGuard p` binades below the other, which keeps `2 ^ gap` small), then `roundDown` back to
`p` bits. -/
def addDown (a b : Dyadic p) : Dyadic p :=
  roundDown (exactAdd (coarsenDown (alignExp a b) a) (coarsenDown (alignExp a b) b))


-- ========================================  `divDown`  ========================================= --
-- Authors:       Claude Sonnet 5
-- Written:       16-August-2026
-- Last update:   02-September-2026
-- Reviewed:      ---

/-- Rounded twice, `quotDown`'s mirror: `roundDown` rounds again past the
rounding `quotDown` already did while dividing. -/
def divDown (a b : Dyadic p) : Dyadic p := roundDown (quotDown a b)


-- ========================================  `mulDown`  ========================================= --
-- Authors:       Claude Sonnet 5
-- Written:       16-August-2026
-- Last update:   02-September-2026
-- Reviewed:      ---

/-- `exactMul`, then `roundDown` back to `p` bits. -/
def mulDown (a b : Dyadic p) : Dyadic p := roundDown (exactMul a b)


-- ========================================  `roundUp`  ========================================= --
-- Authors:       Claude Sonnet 5
-- Written:       16-August-2026
-- Last update:   02-September-2026
-- Reviewed:      14-October-2026 (Tobias Ladner)

/-- The ceiling is the floor of the negation, so this negates, shifts right by
`shift` bits, and negates back. -/
def roundUp (d : Dyadic p) : Dyadic p :=
  ⟨-(-d.mantissa / 2 ^ d.shift), d.exponent + d.shift⟩


-- =========================================  `addUp`  ========================================== --
-- Authors:       Claude Sonnet 5
-- Written:       16-August-2026
-- Last update:   02-September-2026
-- Reviewed:      ---

/-- `exactAdd` of both operands coarsened upward (`coarsenUp`: a no-op unless one sits more than
`alignGuard p` binades below the other, which keeps `2 ^ gap` small), then `roundUp` back to
`p` bits. -/
def addUp (a b : Dyadic p) : Dyadic p :=
  roundUp (exactAdd (coarsenUp (alignExp a b) a) (coarsenUp (alignExp a b) b))


-- =========================================  `divUp`  ========================================== --
-- Authors:       Claude Sonnet 5
-- Written:       16-August-2026
-- Last update:   25-September-2026
-- Reviewed:      ---

/-- Rounded twice: `quotUp` already rounds while dividing, since a quotient of
dyadics is not dyadic, and its shift leaves it at least `p` bits and up to the
dividend's length more, so `roundUp` returns it to `p`. -/
def divUp (a b : Dyadic p) : Dyadic p := roundUp (quotUp a b)


-- =========================================  `mulUp`  ========================================== --
-- Authors:       Claude Sonnet 5
-- Written:       16-August-2026
-- Last update:   02-September-2026
-- Reviewed:      ---

/-- `exactMul`, then `roundUp` back to `p` bits. -/
def mulUp (a b : Dyadic p) : Dyadic p := roundUp (exactMul a b)

end Dyadic
end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
