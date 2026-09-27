import MatrixSpencer.KSDebitRetirement
import MatrixSpencer.KSSpinLocalState

/-!
# Debit-assisted retirement at the actual chosen optimizer

Every density, source frame, and positive transport used below is defined
from the input family and the genuine optimized potential. The frame and
optimization certificates are proved internally. Positive owner coefficients
describe the current finite live family; zero vectors are permitted.

The numerical rejection consequence assumes the stated accuracy of the two
value reports. It does not assert a procedure computing those reports.
-/

open Matrix Set
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section
namespace MatrixSpencer.KSDebitActualRetirement

open KSSpinLocalState KSRankOne KSPotentialModels

variable {ι n : Type*} [Fintype ι] [DecidableEq ι] [Fintype n] [DecidableEq n] [Nonempty n]
local instance {k : Type*} [Fintype k] [DecidableEq k] : CStarAlgebra (Matrix k k ℂ) := {}

def value (M : Matrix (n ⊕ n) (n ⊕ n) ℂ) (v : ι → n → ℂ) (c : ι → ℝ) (θ : ℝ) : ℝ :=
  ownerPotential M (KSSpinSource.family (atoms v)) (KSSpinSource.coefficientCovariance c) θ

def chosenDensity (M : Matrix (n ⊕ n) (n ⊕ n) ℂ) (v : ι → n → ℂ)
    (c : ι → ℝ) (θ : ℝ) : Matrix (n ⊕ n) (n ⊕ n) ℂ :=
  densityOptimizer M (covarianceKraus (KSSpinSource.family (atoms v))
    (KSSpinSource.coefficientCovariance c)) θ

def chosenTransport (M : Matrix (n ⊕ n) (n ⊕ n) ℂ) (v : ι → n → ℂ)
    (c : ι → ℝ) (θ : ℝ) :
    Matrix (KSSpinCompression.supportIndex (atoms v))
      (KSSpinCompression.supportIndex (atoms v)) ℂ :=
  transportOptimizer
    (KSSupportSymmetry.compress (KSSpinCompression.embedding (atoms v)) (chosenDensity M v c θ))
    (covarianceCompressedSource (KSSpinSource.family (atoms v))
      (KSSpinSource.coefficientCovariance c) (chosenDensity M v c θ))

def probe (M : Matrix (n ⊕ n) (n ⊕ n) ℂ) (v : ι → n → ℂ)
    (c : ι → ℝ) (θ : ℝ) (i : ι) : ℝ :=
  realTrace (chosenTransport M v c θ * KSSpinCompression.compressedAtom (atoms v) i)

def queriedValue (M : Matrix (n ⊕ n) (n ⊕ n) ℂ) (v : ι → n → ℂ)
    (c : ι → ℝ) (θ : ℝ) (i : ι) (t δ : ℝ) : ℝ :=
  value (M + t • signedLift (atoms v i) - δ • KSSpinSource.doubled (atoms v i))
    v (Function.update c i 0) θ

theorem chosenDensity_posDef
    (M : Matrix (n ⊕ n) (n ⊕ n) ℂ) (v : ι → n → ℂ) (c : ι → ℝ)
    {θ : ℝ} (hθ : 0 < θ) : (chosenDensity M v c θ).PosDef :=
  densityOptimizer_posDef _ _ hθ

theorem chosenTransport_posDef
    (M : Matrix (n ⊕ n) (n ⊕ n) ℂ) (v : ι → n → ℂ)
    {c : ι → ℝ} (hc : ∀ i, 0 < c i) {θ : ℝ} (hθ : 0 < θ) :
    (chosenTransport M v c θ).PosDef := by
  have hS := chosenDensity_posDef M v c hθ
  exact transportOptimizer_posDef
    (KSSupportSymmetry.compress_posDef _ (KSSpinCompression.embedding_isometry (atoms v)) hS)
    (KSSpinCompression.compressed_source_posDef v hc hS)

theorem probe_nonneg
    (M : Matrix (n ⊕ n) (n ⊕ n) ℂ) (v : ι → n → ℂ)
    {c : ι → ℝ} (hc : ∀ i, 0 < c i) {θ : ℝ} (hθ : 0 < θ) (i : ι) :
    0 ≤ probe M v c θ i :=
  realTrace_mul_nonneg (chosenTransport_posDef M v hc hθ).posSemidef
    (KSSpinCompression.compressedAtom_posSemidef (atoms v) (fun j => atom_posSemidef (v j)) i)

/-- The chosen transport is definitionally the same transport used in the
actual curvature theorem when the owners are `64 (1 - x_i²)`. -/
theorem chosenTransport_owners
    (M : Matrix (n ⊕ n) (n ⊕ n) ℂ) (v : ι → n → ℂ) (x : ι → ℝ) (θ : ℝ) :
    chosenTransport M v (owners x) θ =
      stateTransport v x (chosenDensity M v (owners x) θ) := rfl

/-- No separately supplied optimizer or transport certificate is needed. -/
theorem retire
    (M : Matrix (n ⊕ n) (n ⊕ n) ℂ) (v : ι → n → ℂ)
    {c : ι → ℝ} (hc : ∀ i, 0 < c i) {θ : ℝ} (hθ : 0 < θ)
    (i : ι) (t δ : ℝ) (hsafe : |t| ≤ c i * probe M v c θ i + δ) :
    queriedValue M v c θ i t δ ≤ value M v c θ := by
  let V := KSSpinCompression.embedding (atoms v)
  let S := chosenDensity M v c θ
  let Z := chosenTransport M v c θ
  have hS : S.PosDef := chosenDensity_posDef M v c hθ
  have hM := KSSpinCompression.compressed_source_posDef v hc hS
  have hS0 := KSSupportSymmetry.compress_posDef V (KSSpinCompression.embedding_isometry _) hS
  have hsolve := transportOptimizer_solve hS0 hM
  apply KSDebitRetirement.spin_retire_with_debit_in_frame M v c (fun i => (hc i).le)
    V (KSSpinCompression.embedding_isometry _) hθ ⟨S, hS.isHermitian⟩ hS
    (densityOptimizer_mem _ _ θ).2 (densityOptimizer_isMaxOn _ _ θ)
    (chosenTransport_posDef M v hc hθ) hM hsolve
    (fun X _ => KSSpinCompression.source_reconstruct v c X) i t δ
  change |t| ≤ c i * realTrace (KSSpinSource.doubled (atoms v i) *
    (KSSpinCompression.embedding (atoms v) * Z * (KSSpinCompression.embedding (atoms v))ᴴ)) + δ
  rw [KSSpinCompression.transport_probe, realTrace_mul_comm]
  exact hsafe

/-- Rejection of the nearest endpoint forces a strictly positive gap beyond
the debit allowance, for the internally chosen actual transport. -/
theorem rejected_nearest_gap
    (M : Matrix (n ⊕ n) (n ⊕ n) ℂ) (v : ι → n → ℂ)
    {c : ι → ℝ} (hc : ∀ i, 0 < c i) {θ : ℝ} (hθ : 0 < θ)
    (i : ι) {a δ : ℝ} (ha : -1 ≤ a ∧ a ≤ 1)
    (hreject : value M v c θ < queriedValue M v c θ i (nearestSign a - a) δ) :
    c i * probe M v c θ i + δ < 1 - |a| := by
  apply lt_of_not_ge
  intro hs
  have hsafe := retire M v hc hθ i (nearestSign a - a) δ
    (by rwa [nearestSign_distance ha])
  exact (not_lt_of_ge hsafe) hreject

/-- Failed approximate value tests imply the actual boundary margin and
the exact no-safe test. The hypotheses use only two reported values with
their explicit error bounds; the transport is defined internally. -/
theorem numerical_rejection_margin_and_noSafe
    (M : Matrix (n ⊕ n) (n ⊕ n) ℂ) (v : ι → n → ℂ)
    {c : ι → ℝ} (hc : ∀ i, 0 < c i) {θ : ℝ} (hθ : 0 < θ)
    (i : ι) {a δ η reportedOld reportedQuery : ℝ} (ha : -1 ≤ a ∧ a ≤ 1)
    (hδ : 0 ≤ δ) (hη : 0 ≤ η)
    (hold : |reportedOld - value M v c θ| ≤ η / 8)
    (hquery : |reportedQuery - queriedValue M v c θ i (nearestSign a - a) δ| ≤ η / 8)
    (hreject : η / 2 < reportedQuery - reportedOld) :
    δ < 1 - |a| ∧ c i * probe M v c θ i < 1 - |a| := by
  have htrue : value M v c θ < queriedValue M v c θ i (nearestSign a - a) δ := by
    rcases abs_le.mp hold with ⟨hol, hou⟩
    rcases abs_le.mp hquery with ⟨hql, hqu⟩
    linarith
  have hgap := rejected_nearest_gap M v hc hθ i ha htrue
  have hcq := mul_nonneg (hc i).le (probe_nonneg M v hc hθ i)
  constructor <;> linarith

/-- Specialization to the full-cube owner formula gives exactly the
transport test used by the actual negative-curvature theorem. -/
theorem numerical_rejection_owners
    (M : Matrix (n ⊕ n) (n ⊕ n) ℂ) (v : ι → n → ℂ)
    (x : ι → ℝ) (hx : ∀ i, |x i| < 1) {θ : ℝ} (hθ : 0 < θ)
    (i : ι) {δ η reportedOld reportedQuery : ℝ} (hδ : 0 ≤ δ) (hη : 0 ≤ η)
    (hold : |reportedOld - value M v (owners x) θ| ≤ η / 8)
    (hquery : |reportedQuery -
      queriedValue M v (owners x) θ i (nearestSign (x i) - x i) δ| ≤ η / 8)
    (hreject : η / 2 < reportedQuery - reportedOld) :
    δ < 1 - |x i| ∧ owners x i * realTrace
      (stateTransport v x (chosenDensity M v (owners x) θ) *
        KSSpinCompression.compressedAtom (atoms v) i) < 1 - |x i| := by
  have hi := abs_lt.mp (hx i)
  exact numerical_rejection_margin_and_noSafe M v (owners_pos hx) hθ i
    ⟨hi.1.le, hi.2.le⟩ hδ hη hold hquery hreject

end MatrixSpencer.KSDebitActualRetirement
