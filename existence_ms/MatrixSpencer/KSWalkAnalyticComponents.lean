import MatrixSpencer.KSEighthPreparedState
import MatrixSpencer.KSHessianContact
import MatrixSpencer.KSRayleighAccuracy
import MatrixSpencer.KSFiniteDifference
import MatrixSpencer.KSDebitSmoothness

/-!
Further partial bridges for the KS walk. These components relate actual
endpoint preparation, touching-majorant derivatives, and numerical error
propagation. They do not yet implement the value oracle, assemble the
numerical walk, or prove its unconditional success theorem.
-/
