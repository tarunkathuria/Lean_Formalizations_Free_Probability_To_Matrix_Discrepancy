# Square MS implementation

The public theorem is `FaithfulMS.Main.matrix_spencer_square` in [Main.lean](FaithfulMS/Main.lean). Its full hypotheses, discrepancy bound, probability guarantee, and polynomial work bound are summarized in the [README](README.md).

## Computational interfaces

[DirectSDP.PolynomialService](FaithfulMS/DirectSDP.lean) supplies exact feasible attained primal optimization with polynomial work. The implementation constructs the affine SDP, decodes its optimizing density, and computes the covariance response by scalar/matrix operations and exact EVD. Exact optimization is an explicit arithmetic assumption, not a consequence proved about an approximate SDP solver.

## Walk

Preparation uses the computed covariance response to select paid covariance cuts. Support cleanup uses finite Jacobi rotations and Schur deletions. The legal movement subspace respects frozen coordinates and is orthogonal to the current point; the movement covariance is one half of its projection. Signed frame vectors are sampled uniformly and scaled by `sqrt(rank/2)`, then multiplied by the defined step size. Covariance is withdrawn by the corresponding quadratic increment.

Optimizing densities also supply direct supporting-plane trace tests. The finite step schedules, rounding, epoch acceptance, retries, and label restoration are included in the work accounting. Derived finite conditional sampling laws compose through the adaptive computation. The public endpoint proves work and draw bounds on every execution and success at least `1-2^(-k)`.

The [separate existence project](../existence_ms/README.md) obtains an attained optimizer by mathematical choice and has no polynomial-service assumption.
