import MatrixSpencer.RealRAMMSOriginalInput
import MatrixSpencer.MSCountedAdaptive

/-! Original-label output wrapper, including zero physical dimension. The
positive-dimensional implementation is a counted full process, subsequently
instantiated by the concrete original factory composition. No probability
space is enumerated to extract or test its result. -/
open Matrix
noncomputable section
namespace MatrixSpencer.MSCountedOriginalOutput
open MSManuscriptAdaptive
open MSCountedSampler
open RealRAM.JacobiIteration (Counted)
open MSManuscriptNumericalComposition (Point)
variable {N D : ℕ}
attribute [local instance] Classical.propDecidable
set_option maxRecDepth 4096
set_option maxHeartbeats 1200000

def pointSampler (P : KSPolynomialConvexSolver.PolynomialSolver)
    (A : Fin N → CMatrix D) (hA : ∀i,(A i).IsHermitian)
    (hN : ∀i,spectralNorm (A i) ≤ 1) (r : ℕ) (hd : 0<D) : Sampler (Option (Point N)) :=
  letI : NeZero D:=⟨hd.ne'⟩
  letI:=RealRAM.MSRawOwnerReport.oracle P
  MSManuscriptNumericalComposition.pointSampler A hA hN r (MSConvexValueAlgorithm.provider A hA hN r)

def extract (y : Option (Point N)) : Counted (Option (Fin N → ℝ)) :=
  match y with
  | none=>⟨none,1⟩
  | some y=>⟨some (fun i=>y.val i),3*N+3⟩

theorem extract_value (y : Option (Point N)) :
    (extract y).value=y.map (fun y=>WithLp.ofLp y.val) := by cases y <;> rfl

theorem extract_cost (y : Option (Point N)) : (extract y).cost ≤ 3*N+3 := by
  cases y <;> simp [extract]

theorem map_eq (P : KSPolynomialConvexSolver.PolynomialSolver)
    (A : Fin N → CMatrix D) (hA : ∀i,(A i).IsHermitian)
    (hN : ∀i,spectralNorm (A i) ≤ 1) (r : ℕ) (hd : 0<D) :
    (pointSampler P A hA hN r hd).map (fun y=>(extract y).value)=
      MSConvexRawInput.output P A hA hN r := by
  simp only [extract_value]
  cases D with
  | zero=>omega
  | succ d=>rfl

def positive (P : KSPolynomialConvexSolver.PolynomialSolver)
    (A : Fin N → CMatrix D) (hA : ∀i,(A i).IsHermitian)
    (hN : ∀i,spectralNorm (A i) ≤ 1) (r : ℕ) (hd : 0<D)
    (E : Implementation (pointSampler P A hA hN r hd)) :
    Implementation (MSConvexRawInput.output P A hA hN r) :=
  congr (map_eq P A hA hN r hd)
    (overhead (map E extract) ((RealRAM.MSOriginalInput.setup A).cost+2))

theorem positive_bounded (P : KSPolynomialConvexSolver.PolynomialSolver)
    (A : Fin N → CMatrix D) (hA : ∀i,(A i).IsHermitian)
    (hN : ∀i,spectralNorm (A i) ≤ 1) (r : ℕ) (hd : 0<D)
    (E : Implementation (pointSampler P A hA hN r hd)) {B R : ℕ} (hE : Bounded E B R) :
    Bounded (positive P A hA hN r hd E) (B+1100*(N+D+1)^3) R := by
  apply congr_bounded
  have h:=overhead_bounded (map E extract) ((RealRAM.MSOriginalInput.setup A).cost+2)
    (map_bounded E extract hE extract_cost)
  intro z out cost draws he
  have hb:=h z out cost draws he
  have hi:=RealRAM.MSOriginalInput.setup_cost A
  have hn : N+1 ≤ (N+D+1)^3 := by
    have hh:=Nat.pow_le_pow_right (n:=N+D+1) (by omega) (show 1≤3 by omega)
    simp only [pow_one] at hh
    omega
  constructor <;> omega

/-- Stores all N literal unit signs; no matrix entry or spectral query exists
in this branch. -/
def zero (P : KSPolynomialConvexSolver.PolynomialSolver)
    (A : Fin N → CMatrix 0) (hA : ∀i,(A i).IsHermitian)
    (hN : ∀i,spectralNorm (A i) ≤ 1) (r : ℕ) :
    Implementation (MSConvexRawInput.output P A hA hN r) :=
  pure (some (fun _=>1)) (2*N+2)

theorem zero_bounded (P : KSPolynomialConvexSolver.PolynomialSolver)
    (A : Fin N → CMatrix 0) (hA : ∀i,(A i).IsHermitian)
    (hN : ∀i,spectralNorm (A i) ≤ 1) (r : ℕ) :
    Bounded (zero P A hA hN r) (2*N+3) 0 := pure_bounded _ _

def implementation (P : KSPolynomialConvexSolver.PolynomialSolver)
    (A : Fin N → CMatrix D) (hA : ∀i,(A i).IsHermitian)
    (hN : ∀i,spectralNorm (A i) ≤ 1) (r : ℕ)
    (E : ∀hd : 0<D,Implementation (pointSampler P A hA hN r hd)) :
    Implementation (MSConvexRawInput.output P A hA hN r) := by
  cases D with
  | zero=>exact zero P A hA hN r
  | succ d=>exact positive P A hA hN r (by omega) (E (by omega))

theorem implementation_bounded (P : KSPolynomialConvexSolver.PolynomialSolver)
    (A : Fin N → CMatrix D) (hA : ∀i,(A i).IsHermitian)
    (hN : ∀i,spectralNorm (A i) ≤ 1) (r : ℕ)
    (E : ∀hd : 0<D,Implementation (pointSampler P A hA hN r hd))
    {B R : ℕ} (hE : ∀hd,Bounded (E hd) B R) :
    Bounded (implementation P A hA hN r E) (B+1100*(N+D+1)^3) R := by
  cases D with
  | zero=>
    intro z out cost draws he
    have h:=zero_bounded P A hA hN r z out cost draws he
    have hn : N+1 ≤ (N+1)^3 := by
      simpa only [pow_one] using Nat.pow_le_pow_right (n:=N+1) (by omega) (show 1≤3 by omega)
    simp only [Nat.add_zero]
    constructor <;> omega
  | succ d=>exact positive_bounded P A hA hN r _ _ (hE _)

end MatrixSpencer.MSCountedOriginalOutput
