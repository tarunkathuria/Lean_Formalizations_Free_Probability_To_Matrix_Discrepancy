# Higher-rank KS implementation

The public endpoint is [HigherRankKSRuntime.algorithmic](HigherRankKSRuntime/Main.lean). See the [README](README.md) for its complete input and output bounds.

## Shared mathematical state

The runtime imports `AugmentedHigherRankKS.State` from the sibling existence project. Its state records coefficients, spent and remaining reserves, and discrepancy/budget centers. `StateUpdates`, `Progress`, and `InvariantControllerLoop` prove feasibility, progress, and bounded iteration for the implemented updates.

## Value queries and curvature

`RuntimeSDPValue` specifies the approximate-value solver and its polynomial cost contract, including affine-block materialization. `RuntimeInputFactors` computes input square roots using EVD; `RuntimeStateReport` assembles query centers and proves report accuracy against the optimized potential.

`NumericHessian` and `ThirdDifference` establish finite-difference errors. `TangentEVD` constructs a frame perpendicular to the current active vector, diagonalizes the compressed Hessian, and lifts a unit minimum-Rayleigh direction. `RuntimeDirection` counts this computation. Exact EVD has unit invocation cost; input/output processing and scalar arithmetic are charged separately.

## Finite controller and global output

`NextEvent` performs near-face or low-reserve cleanup, scans preparation queries, or takes the lower reported-value sign of a tangent movement. `RuntimeNext` discharges the local accuracy and curvature obligations. `InactiveCoordinates` and `FrozenCoordinates` prove label preservation.

`RuntimeCubeArithmetic` implements the live-mass matrix and final rounding. `RuntimeGlobalArithmetic` relates these operations to the mathematical epoch loop. `RuntimeProgram` assembles the finite algorithm, and `Main` proves correctness and uniform polynomial work for its computed output. No local curvature certificate or successful-execution hypothesis is supplied to the public theorem.
