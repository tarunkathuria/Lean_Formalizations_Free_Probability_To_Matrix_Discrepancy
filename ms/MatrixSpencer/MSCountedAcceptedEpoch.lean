import MatrixSpencer.MSCountedRetry
import MatrixSpencer.MSConvexAcceptancePolynomial

/-! Short-circuit retries for the actual convex-value square-MS epoch.
The numerical trial implementation is composed with the fully compiled
acceptance evaluator. Every trial that is rejected is charged, and later
prospective draws are untouched after the first acceptance. -/
open Matrix
noncomputable section
namespace MatrixSpencer.MSCountedAcceptedEpoch
open MSManuscriptAdaptive MSCountedSampler
open MSManuscriptNumericalConfig
variable {m N d : ℕ} [Nonempty (Fin d)]
variable (P : KSPolynomialConvexSolver.PolynomialSolver)
set_option maxHeartbeats 1400000
set_option maxRecDepth 4000

def trial (cfg : EpochConfig (Fin m) (Fin d)) (hd : 0<d) :=
  @MSConvexNumericalEpochRun.output (RealRAM.MSRawOwnerReport.oracle P) m d (ofEpochConfig cfg hd)

def output (cfg : EpochConfig (Fin m) (Fin d)) (hd : 0<d) (r : ℕ) :=
  @MSConvexValueAcceptedEpoch.output (RealRAM.MSRawOwnerReport.oracle P) m d cfg hd r

theorem retry_eq (cfg : EpochConfig (Fin m) (Fin d)) (hd : 0<d) (r : ℕ) :
    MSManuscriptAcceptanceRetry.output (trial P cfg hd)
      (fun s=>(RealRAM.MSAcceptanceData.accepts P cfg hd s).value) r =
      output P cfg hd r := by
  have he : (fun s=>(RealRAM.MSAcceptanceData.accepts P cfg hd s).value)=
      @MSConvexValueAcceptedEpoch.accepts (RealRAM.MSRawOwnerReport.oracle P) m d cfg hd := by
    funext s
    exact RealRAM.MSAcceptanceData.accepts_value P cfg hd s
  rw [he]
  rfl

def implementation (cfg : EpochConfig (Fin m) (Fin d)) (hd : 0<d)
    (E : Implementation (trial P cfg hd)) (r : ℕ) :
    Implementation (output P cfg hd r) :=
  MSCountedSampler.congr (retry_eq P cfg hd r)
    (MSCountedRetry.implementation E (RealRAM.MSAcceptanceData.accepts P cfg hd) r)

def operations (N d r B : ℕ) : ℕ :=
  r*(B+MSConvexAcceptancePolynomial.acceptanceCost P N d+3)+1

theorem implementation_bounded (cfg : EpochConfig (Fin m) (Fin d)) (hd : 0<d) (hm : m≤N)
    (E : Implementation (trial P cfg hd)) {B R : ℕ} (hE : Bounded E B R) (r : ℕ) :
    Bounded (implementation P cfg hd E r) (operations P N d r B) (r*R) := by
  apply MSCountedSampler.congr_bounded
  exact MSCountedRetry.implementation_bounded E (RealRAM.MSAcceptanceData.accepts P cfg hd) hE
    (fun s=>MSConvexAcceptancePolynomial.accepts_cost P cfg hd hm s) r

theorem execution_bounded (cfg : EpochConfig (Fin m) (Fin d)) (hd : 0<d) (hm : m≤N)
    (E : Implementation (trial P cfg hd)) {B R : ℕ} (hE : Bounded E B R) (r : ℕ)
    (z : (output P cfg hd r).Draws) :
    ∃cost draws,(implementation P cfg hd E r).Executes z
      ((output P cfg hd r).value z) cost draws ∧
      cost≤operations P N d r B ∧ draws≤r*R :=
  MSCountedSampler.execution_bounded (implementation P cfg hd E r)
    (implementation_bounded P cfg hd hm E hE r) z

theorem executed_sound (cfg : EpochConfig (Fin m) (Fin d)) (hd : 0<d)
    (E : Implementation (trial P cfg hd)) (r : ℕ)
    (z : (output P cfg hd r).Draws)
    (s : MSManuscriptNumericalEpochRun.Certified (ofEpochConfig cfg hd)) (cost draws : ℕ)
    (he : (implementation P cfg hd E r).Executes z (some s) cost draws) :
    MSManuscriptAcceptedEpoch.GoodEndpoint cfg hd s := by
  letI := RealRAM.MSRawOwnerReport.oracle P
  exact MSConvexValueAcceptedEpoch.output_sound cfg hd r z s
    ((implementation P cfg hd E r).result z (some s) cost draws he).symm

theorem failure_probability (cfg : EpochConfig (Fin m) (Fin d)) (hd : 0<d) (r : ℕ) :
    (output P cfg hd r).expectation failure≤(301/800:ℝ)^r := by
  letI := RealRAM.MSRawOwnerReport.oracle P
  exact MSConvexValueAcceptedEpoch.output_failure_le cfg hd r

end MatrixSpencer.MSCountedAcceptedEpoch
