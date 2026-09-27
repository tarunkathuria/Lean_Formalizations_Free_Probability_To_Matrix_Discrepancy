import MatrixSpencer.KSEighthManuscriptRun
import MatrixSpencer.KSEighthManuscriptHessianReport



open Matrix Set
open scoped BigOperators MatrixOrder
noncomputable section
namespace MatrixSpencer.KSEighthManuscriptParameters
open KSEighthLiveEnumeration
variable {N d : ℕ}

def rho (N : ℕ) (δ : ℝ) : ℝ := δ/(100*(N : ℝ))
def kappa (N : ℕ) (δ : ℝ) : ℝ := δ/(10000*(N : ℝ)^2)
def precision (N : ℕ) (δ : ℝ) : ℝ := kappa N δ/(100*(N : ℝ))
def fourthCap (v : Fin N → Fin d → ℂ) (θ : ℝ) : ℝ :=
  1 + KSEighthInputTaylorBound.fourthBudget v θ

def beta (v : Fin N → Fin d → ℂ) (δ θ : ℝ) : ℝ :=
  kappa N δ/(100*(N : ℝ)*(fourthCap v θ+1))

def movementStep (v : Fin N → Fin d → ℂ) (δ θ : ℝ) : ℝ :=
  (1/2 : ℝ) * min (rho N δ/Real.sqrt (N : ℝ))
    (min (Real.sqrt (δ/(10000*fourthCap v θ*(N : ℝ)^3))) (1/100))

theorem rho_pos (hN : 0 < N) {δ : ℝ} (hδ : 0 < δ) : 0 < rho N δ := by
  unfold rho
  positivity

theorem kappa_pos (hN : 0 < N) {δ : ℝ} (hδ : 0 < δ) : 0 < kappa N δ := by
  unfold kappa
  positivity

theorem precision_pos (hN : 0 < N) {δ : ℝ} (hδ : 0 < δ) : 0 < precision N δ := by
  have hk := kappa_pos hN hδ
  unfold precision
  positivity

theorem precision_le (hN : 0 < N) {δ : ℝ} (hδ : 0 < δ) : precision N δ ≤ kappa N δ := by
  have hn : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hk := (kappa_pos hN hδ).le
  unfold precision
  apply div_le_self hk
  linarith

theorem fourthCap_pos (v : Fin N → Fin d → ℂ) {θ : ℝ} (hθ : 0 < θ) (hd : 0 < d) :
    0 < fourthCap v θ := by
  letI : Nonempty (Fin d) := ⟨⟨0,hd⟩⟩
  have hM := KSEighthInputTaylorBound.fourthBudget_pos v hθ
  unfold fourthCap
  linarith

theorem beta_pos (v : Fin N → Fin d → ℂ) {δ θ : ℝ}
    (hN : 0 < N) (hδ : 0 < δ) (hθ : 0 < θ) (hd : 0 < d) : 0 < beta v δ θ := by
  have hk := kappa_pos hN hδ
  have hM := fourthCap_pos v hθ hd
  unfold beta
  positivity

theorem beta_le_quarter (v : Fin N → Fin d → ℂ) {δ θ : ℝ}
    (hN : 0 < N) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hθ : 0 < θ) (hd : 0 < d) :
    beta v δ θ ≤ 1/4 := by
  have hn : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hM := fourthCap_pos v hθ hd
  have hk : kappa N δ ≤ 1 := by
    unfold kappa
    rw [div_le_one (by positivity)]
    nlinarith [sq_nonneg ((N : ℝ)-1)]
  unfold beta
  rw [div_le_iff₀ (by positivity : 0 < 100*(N : ℝ)*(fourthCap v θ+1))]
  nlinarith

theorem movementStep_pos (v : Fin N → Fin d → ℂ) {δ θ : ℝ}
    (hN : 0 < N) (hδ : 0 < δ) (hθ : 0 < θ) (hd : 0 < d) : 0 < movementStep v δ θ := by
  have hρ := rho_pos hN hδ
  have hM := fourthCap_pos v hθ hd
  unfold movementStep
  positivity

theorem movementStep_margin (v : Fin N → Fin d → ℂ) {δ θ : ℝ}
    (hN : 0 < N) (hδ : 0 < δ) (hθ : 0 < θ) (hd : 0 < d) :
    movementStep v δ θ * Real.sqrt (N : ℝ) ≤ rho N δ := by
  have ht := movementStep_pos v hN hδ hθ hd
  have hs : 0 < Real.sqrt (N : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast hN)
  have hmin : 2*movementStep v δ θ ≤ rho N δ/Real.sqrt (N : ℝ) := by
    unfold movementStep
    linarith [min_le_left (rho N δ/Real.sqrt (N : ℝ))
      (min (Real.sqrt (δ/(10000*fourthCap v θ*(N : ℝ)^3))) (1/100))]
  have hh := (le_div_iff₀ hs).mp hmin
  nlinarith [mul_pos ht hs]

/-- All numerical procedures are data fields, not selected witnesses of good
covariances or successful signings. -/
def controller (v : Fin N → Fin d → ℂ) {δ θ : ℝ}
    (hN : 0 < N) (hδ : 0 < δ) (hθ : 0 < θ) (hd : 0 < d) : KSEighthManuscriptRun.Controller N where
  ρ := rho N δ
  ρ_pos := rho_pos hN hδ
  τ := rho N δ
  report := KSEighthNumericalValue.stateReport v θ hd (rho N δ/8)
  stepSize := movementStep v δ θ
  step_pos := movementStep_pos v hN hδ hθ hd
  step_le := movementStep_margin v hN hδ hθ hd
  covariance := fun s => KSEighthManuscriptHessianReport.covariance v θ (precision N δ)
    (kappa N δ) (beta v δ θ) hd s.coeff
  covariance_posSemidef := fun s => KSEighthManuscriptCovariance.covariance_posSemidef _ _ _
  covariance_le_one := fun s => (KSEighthManuscriptCovariance.covariance_feasible _ _ _).2.2.1
  covariance_trace := fun s _ => by
    unfold KSEighthManuscriptHessianReport.covariance
    rw [(KSEighthManuscriptCovariance.covariance_feasible _ _ _).2.2.2]
    unfold KSEighthManuscriptCovariance.target
    nlinarith [show (0 : ℝ) ≤ count s.coeff from Nat.cast_nonneg _]


theorem controller_covariance_curvature (v : Fin N → Fin d → ℂ) {δ θ : ℝ}
    (hN : 0 < N) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hθ : 0 < θ) (hd : 0 < d)
    (s : KSEighthManuscriptRun.State (controller v hN hδ hθ hd))
    (hs : ¬KSEighthWalkRun.terminal s) :
    Matrix.trace ((controller v hN hδ hθ hd).covariance s *
      KSEighthManuscriptPreparedInertia.hessian v θ s.coeff) ≤ 3*kappa N δ*count s.coeff :=
  (KSEighthManuscriptHessianReport.covariance_spec v (rho_pos hN hδ) hθ
    (precision_pos hN hδ) (precision_le hN hδ) (beta_pos v hN hδ hθ hd)
    (beta_le_quarter v hN hδ hδ1 hθ hd) hd s hs).2.2.2

end MatrixSpencer.KSEighthManuscriptParameters
