import MatrixSpencer.RectangularRidgeSolverCertificate
import MatrixSpencer.MSManuscriptNumericalAcceptance

/-! The rectangular walk's actual acceptance test, using six accurate SDP
queries and scalar comparisons. Every accepted valid endpoint satisfies the
potential increment bound, and every endpoint in the analytic good event is
accepted. The epoch sampler must separately prove its valid endpoints and
the good-event mass; neither is assumed by the numerical solver. -/

open Matrix Set
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section
namespace MatrixSpencer.RectangularRidgeSolverAcceptance
variable {N d : ℕ} [Nonempty (Fin d)]
local instance ridgeSolverAcceptanceCStar : CStarAlgebra (Matrix (Fin d) (Fin d) ℂ) := {}
local instance ridgeSolverAcceptanceSpace : NormedSpace ℝ (selfAdjoint (Matrix (Fin d) (Fin d) ℂ)) := inferInstance
open RectangularRidgeCertificate RectangularRidgeSolverCertificate

structure Config (N d : ℕ) where
  anchor : selfAdjoint (Matrix (Fin d) (Fin d) ℂ)
  atoms : Fin N → Matrix (Fin d) (Fin d) ℂ
  hermitian : ∀ i, (atoms i).IsHermitian
  depth : ℕ
  depth_pos : 1≤depth
  theta : ℝ
  theta_pos : 0<theta
  ridge : ℝ
  ridge_pos : 0<ridge
  radius : ℝ
  radius_nonneg : 0≤radius
  count : ℕ
  count_pos : 1≤count
  coordinate : Fin d

structure Endpoint (N d : ℕ) where
  center : selfAdjoint (Matrix (Fin d) (Fin d) ℂ)
  covariance : Matrix (Fin N) (Fin N) ℝ
  covariance_psd : covariance.PosSemidef
  movement : selfAdjoint (Matrix (Fin d) (Fin d) ℂ)
  failed : Bool

def scale (cfg : Config N d) : ℝ := Real.sqrt (cfg.count : ℝ)
def tolerance : ℝ := RectangularRidgeTangentParameters.tolerance

def Endpoint.Valid (cfg : Config N d) (e : Endpoint N d) : Prop :=
  Real.sqrt (realTrace (((e.center-cfg.anchor : selfAdjoint (Matrix (Fin d) (Fin d) ℂ)) :
    Matrix (Fin d) (Fin d) ℂ)*((e.center-cfg.anchor : selfAdjoint (Matrix (Fin d) (Fin d) ℂ)) :
    Matrix (Fin d) (Fin d) ℂ)))≤cfg.radius ∧
  Real.sqrt (realTrace ((e.movement : Matrix (Fin d) (Fin d) ℂ)*(e.movement : Matrix (Fin d) (Fin d) ℂ)))≤cfg.radius

def psi (cfg : Config N d) (e : Endpoint N d) : ℝ :=
  certificate cfg.anchor cfg.atoms cfg.depth cfg.theta cfg.ridge e.center e.covariance

def tangent (cfg : Config N d) (e : Endpoint N d) : ℝ :=
  realTrace (density cfg.anchor cfg.depth cfg.theta cfg.ridge*(e.movement : Matrix (Fin d) (Fin d) ℂ))

def psiReport (O : RectangularRidgeConvexValue.Solver) (cfg : Config N d) (e : Endpoint N d) : ℝ :=
  certificateReport O cfg.depth cfg.depth_pos cfg.coordinate cfg.anchor e.center cfg.atoms
    cfg.hermitian e.covariance e.covariance_psd cfg.theta cfg.ridge cfg.radius tolerance

def tangentReport (O : RectangularRidgeConvexValue.Solver) (cfg : Config N d) (e : Endpoint N d) : ℝ :=
  RectangularRidgeSolverCertificate.tangentReport O cfg.depth cfg.depth_pos cfg.coordinate
    cfg.anchor e.movement cfg.theta cfg.ridge cfg.radius tolerance

def accepts (O : RectangularRidgeConvexValue.Solver) (cfg : Config N d) (e : Endpoint N d) : Bool :=
  MSManuscriptNumericalAcceptance.acceptReports e.failed (scale cfg)
    (psiReport O cfg e) (tangentReport O cfg e)

theorem reports_accuracy (O : RectangularRidgeConvexValue.Solver) (cfg : Config N d)
    (e : Endpoint N d) (he : e.Valid cfg) :
    |psiReport O cfg e-psi cfg e|≤scale cfg/100 ∧
      |tangentReport O cfg e-tangent cfg e|≤scale cfg/100 := by
  have ht : 0<tolerance := by norm_num [tolerance,RectangularRidgeTangentParameters.tolerance]
  have hm := RectangularRidgeTangentParameters.tolerance_le_scaled_margin cfg.count_pos
  have hp := certificateReport_accuracy O cfg.depth cfg.depth_pos cfg.coordinate
    cfg.anchor e.center cfg.atoms cfg.hermitian e.covariance e.covariance_psd
    cfg.theta_pos cfg.ridge_pos cfg.radius_nonneg ht he.1
  have hg := RectangularRidgeSolverCertificate.tangentReport_accuracy O cfg.depth cfg.depth_pos
    cfg.coordinate cfg.anchor e.movement cfg.theta_pos cfg.ridge_pos cfg.radius_nonneg ht he.2
  exact ⟨hp.trans hm,hg.trans (by change tolerance/3≤scale cfg/100; change tolerance≤scale cfg/100 at hm; linarith)⟩

theorem accepts_sound (O : RectangularRidgeConvexValue.Solver) (cfg : Config N d)
    (e : Endpoint N d) (he : e.Valid cfg) (ha : accepts O cfg e=true) :
    e.failed=false ∧ psi cfg e≤(1651/100:ℝ)*scale cfg ∧ tangent cfg e≤(451/100:ℝ)*scale cfg :=
  MSManuscriptNumericalAcceptance.reports_sound (reports_accuracy O cfg e he).1
    (reports_accuracy O cfg e he).2 ha

def Good (cfg : Config N d) (e : Endpoint N d) : Prop :=
  e.failed=false ∧ psi cfg e≤16*scale cfg ∧ tangent cfg e≤4*scale cfg

theorem good_accepted (O : RectangularRidgeConvexValue.Solver) (cfg : Config N d)
    (e : Endpoint N d) (he : e.Valid cfg) (hg : Good cfg e) : accepts O cfg e=true :=
  MSManuscriptNumericalAcceptance.good_reports_accepted (Real.sqrt_nonneg _)
    (reports_accuracy O cfg e he).1 (reports_accuracy O cfg e he).2 hg.1 hg.2.1 hg.2.2

def roundingTangent (cfg : Config N d) (e : Endpoint N d) : ℝ :=
  realTrace (density (cfg.anchor : Matrix (Fin d) (Fin d) ℂ) cfg.depth cfg.theta cfg.ridge*
    ((e.center : Matrix (Fin d) (Fin d) ℂ)-(cfg.anchor : Matrix (Fin d) (Fin d) ℂ)-
      (e.movement : Matrix (Fin d) (Fin d) ℂ)))

theorem accepted_potential_increment (O : RectangularRidgeConvexValue.Solver)
    (cfg : Config N d) (e : Endpoint N d) (he : e.Valid cfg) (ha : accepts O cfg e=true)
    (Cstart : Matrix (Fin N) (Fin N) ℝ) (hCstart : Cstart.PosSemidef)
    (hround : roundingTangent cfg e≤scale cfg/100) :
    RectangularRidgeCovarianceCalculus.ownerPotential cfg.depth e.center cfg.atoms e.covariance cfg.theta cfg.ridge-
      RectangularRidgeCovarianceCalculus.ownerPotential cfg.depth cfg.anchor cfg.atoms Cstart cfg.theta cfg.ridge<25*scale cfg := by
  obtain ⟨_,hp,ht⟩ := accepts_sound O cfg e he ha
  have hid := certificate_terminal_identity (cfg.anchor : Matrix (Fin d) (Fin d) ℂ)
    (e.center : Matrix (Fin d) (Fin d) ℂ) cfg.atoms cfg.depth cfg.theta cfg.ridge Cstart e.covariance
  have h0 := certificate_nonneg (cfg.anchor : Matrix (Fin d) (Fin d) ℂ)
    (cfg.anchor : Matrix (Fin d) (Fin d) ℂ) cfg.atoms cfg.hermitian hCstart cfg.depth cfg.theta cfg.ridge
  have hs : RectangularRidgeCertificate.tangent (cfg.anchor : Matrix (Fin d) (Fin d) ℂ)
      cfg.depth cfg.theta cfg.ridge e.center=tangent cfg e+roundingTangent cfg e := by
    simp only [RectangularRidgeCertificate.tangent,tangent,roundingTangent,Matrix.mul_sub,realTrace_sub]
    ring
  rw [hs] at hid
  have hscale : 0<scale cfg := Real.sqrt_pos.mpr (by exact_mod_cast (show 0<cfg.count by have := cfg.count_pos; omega))
  change _=psi cfg e-_+(tangent cfg e+roundingTangent cfg e) at hid
  change regularizedOwnerPotential e.center cfg.atoms e.covariance (RectangularRidgeCovarianceCalculus.regularizer cfg.depth cfg.theta cfg.ridge)-
    regularizedOwnerPotential cfg.anchor cfg.atoms Cstart (RectangularRidgeCovarianceCalculus.regularizer cfg.depth cfg.theta cfg.ridge)<25*scale cfg
  linarith

end MatrixSpencer.RectangularRidgeSolverAcceptance
