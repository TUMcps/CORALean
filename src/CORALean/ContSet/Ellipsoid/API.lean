import CORALean.ContSet.Ellipsoid.Real.API
import CORALean.ContSet.Ellipsoid.Float.API

/-!
# Ellipsoids, collected

Stored as a centre and a generator matrix rather than as CORA's shape matrix
`Q`; `Real.Ellipsoid` says why.

Both layers. The float one was expected to need a square root — an ellipsoid is
the one representation whose support function is closed form, and that closed
form is `⟨d, q⟩ + ‖Gᵀd‖₂` — and it needs none: an upper bound on `√x` is any `s`
with `x ≤ s·s`, which is a multiplication, so the layer *checks* a candidate
instead of computing a root. `Global.Float.EuclideanNorm` is that check, and
nothing here adds a scalar operation.
-/
