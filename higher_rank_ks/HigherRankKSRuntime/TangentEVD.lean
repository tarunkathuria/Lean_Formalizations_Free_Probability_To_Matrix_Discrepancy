import HigherRankKSRuntime.Tangent.Frame
import HigherRankKSRuntime.Tangent.RestrictedEVD
import HigherRankKSRuntime.NumericHessian
import HigherRankKSRuntime.ValueDecisions

/-! Exact EVD in the explicitly constructed coefficient tangent space.
The canonical frame is the identity at zero and a scalar Householder
construction otherwise. No tangent-direction primitive is assumed. -/

open Matrix Set
open scoped BigOperators Matrix.Norms.L2Operator
noncomputable section
namespace HigherRankKSRuntime.TangentEVD
open MatrixSpencer
open KSRayleighAccuracy (realRayleigh)
open KSNumericalHessian (Space hessian)
open HigherRankKSRuntime.Tangent
variable {m : ℕ}

def output (x : Space m) (H : Matrix (Fin m) (Fin m) ℝ)
    (hr : 0 < (Frame.canonical m x).rank) : Space m :=
  RestrictedEVD.output (Frame.canonical m x).embed H hr

theorem rank_pos_of_unit_witness (x g : Space m) (hg : ‖g‖ = 1)
    (horth : inner ℝ x g = 0) : 0 < (Frame.canonical m x).rank := by
  apply Frame.rank_pos_of_nonzero (Frame.canonical m x) g _ horth
  intro hz
  rw [hz, norm_zero] at hg
  norm_num at hg

theorem output_norm (x : Space m) (H : Matrix (Fin m) (Fin m) ℝ)
    (hr : 0 < (Frame.canonical m x).rank) : ‖output x H hr‖ = 1 :=
  RestrictedEVD.output_norm _ _ _

theorem output_orthogonal (x : Space m) (H : Matrix (Fin m) (Fin m) ℝ)
    (hr : 0 < (Frame.canonical m x).rank) : inner ℝ x (output x H hr) = 0 :=
  (Frame.canonical m x).orthogonal _

/-- The computed vector attains the minimum over precisely the unit sphere
in `x`-perpendicular, not over an assumed or smaller favorable subspace. -/
theorem output_minimizes_tangent (x : Space m) (H : Matrix (Fin m) (Fin m) ℝ)
    (hH : H.IsSymm) (hr : 0 < (Frame.canonical m x).rank)
    (g : Space m) (hg : ‖g‖ = 1) (horth : inner ℝ x g = 0) :
    realRayleigh H (output x H hr) ≤ realRayleigh H g := by
  obtain ⟨v, hv⟩ := (Frame.canonical m x).onto g horth
  have hvnorm : ‖v‖ = 1 := by rw [← (Frame.canonical m x).embed.norm_map, hv, hg]
  simpa only [output, hv] using
    RestrictedEVD.output_minimal (Frame.canonical m x).embed H hH hr v hvnorm

theorem output_comparison (x : Space m) (H report : Matrix (Fin m) (Fin m) ℝ)
    (hreport : report.IsSymm) (hr : 0 < (Frame.canonical m x).rank)
    {κ : ℝ} (herr : ‖H - report‖ ≤ κ)
    (g : Space m) (hg : ‖g‖ = 1) (horth : inner ℝ x g = 0) :
    realRayleigh H (output x report hr) ≤ realRayleigh H g + 2 * κ := by
  obtain ⟨v, hv⟩ := (Frame.canonical m x).onto g horth
  have hvnorm : ‖v‖ = 1 := by rw [← (Frame.canonical m x).embed.norm_map, hv, hg]
  simpa only [output, hv] using
    RestrictedEVD.output_comparison (Frame.canonical m x).embed H report hreport hr herr v hvnorm

theorem output_curvature_gap (x : Space m) (H report : Matrix (Fin m) (Fin m) ℝ)
    (hreport : report.IsSymm) (hr : 0 < (Frame.canonical m x).rank)
    {γ : ℝ} (hγ : 0 < γ) (herr : ‖H - report‖ ≤ γ / 8)
    (g : Space m) (hg : ‖g‖ = 1) (horth : inner ℝ x g = 0)
    (hcurv : realRayleigh H g ≤ -4 * γ) :
    realRayleigh H (output x report hr) < -3 * γ := by
  have hc := output_comparison x H report hreport hr herr g hg horth
  linarith

theorem chosen_potential (f : Space m → ℝ) (x g : Space m)
    {h M γ qp qm ν : ℝ} (hh : 0 < h) (hγ : 0 < γ)
    (hf : ContDiffAt ℝ 2 f x)
    (hline : ContDiffOn ℝ 3 (fun t => f (x + t • g)) (Icc (-h) h))
    (hthird : ∀ t ∈ Icc (-h) h, |iteratedDeriv 3 (fun t => f (x + t • g)) t| ≤ M)
    (hcurvature : realRayleigh (hessian f x) g ≤ -3 * γ)
    (hbudget : M * h ≤ γ / 16) (hν : ν ≤ γ * h ^ 2 / 64)
    (hqp : |qp - f (x + h • g)| ≤ ν) (hqm : |qm - f (x - h • g)| ≤ ν) :
    reportedBest qp qm (f (x + h • g)) (f (x - h • g)) ≤ f x - γ * h ^ 2 / 2 := by
  have ht := ThirdDifference.directional_average_le f x g hh hf hline hthird
  have hs := reportedBest_le_average hqp hqm
  rw [KSNumericalHessian.hessian_rayleigh] at hcurvature
  have hc := mul_le_mul_of_nonneg_right hcurvature (sq_nonneg h)
  have hr := mul_le_mul_of_nonneg_right hbudget (sq_nonneg h)
  have hpos := mul_pos hγ (sq_pos_of_pos hh)
  nlinarith

end HigherRankKSRuntime.TangentEVD
