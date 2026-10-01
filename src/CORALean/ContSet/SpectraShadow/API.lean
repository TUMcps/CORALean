import CORALean.ContSet.SpectraShadow.Real.API
import CORALean.ContSet.SpectraShadow.Float.API

/-!
# Spectrahedral shadows, both layers

CORA's `spectraShadow` [1]: the projection `{c + G β | A₀ + Σ βᵢ Aᵢ ⪰ 0}` of a
spectrahedron, the representation every convex set a semidefinite program
describes lands in.

The specification in `Real`, and in `Float` the same inequality's matrices stored
in `𝕋` beside an error box for the centre. `plus`, `mtimes` and `cartProd` are
exact over ℝ, the closure properties the representation is for; the float layer
has `plus` alone, a generator's rounding being unboundable here — see
`Float/SpectraShadow.lean`.

Everything that needs a semidefinite solver is absent: the support function,
containment, emptiness and intersection.

## References

* [1] `contSet/@spectraShadow/spectraShadow.m`, CORA (Sep. 2025).
-/
