import CORALean.NN.Layers.Cost.Linear

/-!
# What running a layer costs

Scalar-operation counts against `Global/Cost.lean`'s model, asserted rather
than proved. `linearCost` is the one layer whose propagation is a set
operation and nothing else, per its own file's docstring, so it is the one
this directory prices: one `mtimes`, one `plus`, one embedded bias, at
parameters no representation-agnostic file can fix. `Convolution`, average
pooling and `BatchNorm` are `Layer.linear` at their own matrix, so
`linearCost` prices them too, at whichever matrix they name.

Every other layer relaxes a nonlinear function — an activation, a pooled
window's pivot, softmax's two boxes — and what that relaxation costs is a
question this directory leaves open along with it. `linearWithError` is left
out too: its extra `Interval.plus` on the error box is one more term to add,
not yet stated here.
-/
