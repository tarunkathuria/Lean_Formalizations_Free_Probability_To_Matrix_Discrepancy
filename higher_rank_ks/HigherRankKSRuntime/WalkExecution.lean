import HigherRankKSRuntime.RuntimeDirection

/-! A complete local numerical walk update: centered value stencils, explicit
tangent-frame EVD, two endpoint value queries, and the better reported sign. -/

open Matrix Set
open scoped BigOperators Matrix.Norms.L2Operator
noncomputable section
namespace HigherRankKSRuntime.WalkExecution
open MatrixSpencer
open MatrixSpencer.RealRAM
open MatrixSpencer.RealRAM.JacobiIteration (Counted)
open HigherRankKSRuntime.Tangent
open KSNumericalHessian (Space hessian)

variable {m : ℕ}

def compute (R : FullHessian.Report m) (x : Space m) (t h : ℝ)
    (hr : 0 < (Frame.canonical m x).rank) : Counted (Space m) :=
  let g := RuntimeDirection.compute R x t hr
  let rp := R (h • g.value)
  let rm := R (-h • g.value)
  ⟨if rp.value ≤ rm.value then g.value else -g.value,
    g.cost + rp.cost + rm.cost + 3 * m + 5⟩

theorem compute_unit (R : FullHessian.Report m) (x : Space m) (t h : ℝ)
    (hr : 0 < (Frame.canonical m x).rank) : ‖(compute R x t h hr).value‖ = 1 := by
  simp only [compute]
  split_ifs <;> simpa only [norm_neg] using RuntimeDirection.compute_unit R x t hr

theorem compute_orthogonal (R : FullHessian.Report m) (x : Space m) (t h : ℝ)
    (hr : 0 < (Frame.canonical m x).rank) :
    inner ℝ x (compute R x t h hr).value = 0 := by
  simp only [compute]
  split_ifs <;> simp only [inner_neg_right, RuntimeDirection.compute_orthogonal, neg_zero]

theorem chosen_value (R : FullHessian.Report m) (x : Space m) (t h : ℝ)
    (hr : 0 < (Frame.canonical m x).rank) (f : Space m → ℝ) :
    f (h • (compute R x t h hr).value) =
      reportedBest (R (h • (RuntimeDirection.compute R x t hr).value)).value
        (R (-h • (RuntimeDirection.compute R x t hr).value)).value
        (f (h • (RuntimeDirection.compute R x t hr).value))
        (f (-h • (RuntimeDirection.compute R x t hr).value)) := by
  simp only [compute, reportedBest]
  split_ifs <;> simp only [smul_neg, neg_smul]

theorem potential_descent (R : FullHessian.Report m) (x : Space m)
    (t h : ℝ) (hr : 0 < (Frame.canonical m x).rank) (f : Space m → ℝ)
    {N : ℕ} {M γ ν : ℝ} (hmN : m ≤ N) (hN : 0 < N)
    (hM : 0 < M) (hγ : 0 < γ) (hν : 0 ≤ ν) (ht : 0 < t) (hh : 0 < h)
    (hf : ContDiffAt ℝ 2 f 0)
    (hstencil : NumericHessian.LineBounds f 0 t M)
    (hquery : KSFullManuscriptHessian.QueryAccuracy f (fun y => (R y).value) 0 t ν)
    (hreport : ∀ y, ‖y‖ ≤ h → |(R y).value - f y| ≤ ν)
    (htsmall : t ≤ γ / (64 * N * M))
    (hνt : ν ≤ γ * t ^ 2 / (256 * N))
    (hhsmall : M * h ≤ γ / 16) (hνh : ν ≤ γ * h ^ 2 / 64)
    (hlines : ∀ g : Space m, ‖g‖ = 1 →
      ContDiffOn ℝ 3 (fun s => f (s • g)) (Icc (-h) h) ∧
        ∀ s ∈ Icc (-h) h, |iteratedDeriv 3 (fun u => f (u • g)) s| ≤ M)
    (g : Space m) (hg : ‖g‖ = 1) (horth : inner ℝ x g = 0)
    (hcurv : KSRayleighAccuracy.realRayleigh (hessian f 0) g ≤ -4 * γ) :
    f (h • (compute R x t h hr).value) ≤ f 0 - γ * h ^ 2 / 2 := by
  let H := KSFullManuscriptHessian.matrixReport (fun y => (R y).value) 0 t
  have herr0 := NumericHessian.operator_error f (fun y => (R y).value) 0 ht hM.le hν
    hf hstencil hquery
  have herr : ‖hessian f 0 - H‖ ≤ γ / 8 := by
    have hmNr : (m : ℝ) ≤ N := by exact_mod_cast hmN
    have hb : 0 ≤ 2 * M * t + 4 * ν / t ^ 2 := by positivity
    exact (herr0.trans (mul_le_mul_of_nonneg_right hmNr hb)).trans
      (NumericHessian.accuracy_budget hN hM ht hγ htsmall hνt).le
  let v := (RuntimeDirection.compute R x t hr).value
  have hv : ‖v‖ = 1 := RuntimeDirection.compute_unit R x t hr
  have hvc : KSRayleighAccuracy.realRayleigh (hessian f 0) v < -3 * γ := by
    dsimp [v]
    rw [RuntimeDirection.compute_value]
    exact TangentEVD.output_curvature_gap x (hessian f 0) H
      (KSFullManuscriptHessian.matrixReport_isSymm _ _ _) hr hγ herr g hg horth hcurv
  obtain ⟨hl, hthird⟩ := hlines v hv
  have hp : |(R (h • v)).value - f (h • v)| ≤ ν :=
    hreport _ (by rw [norm_smul, hv, mul_one, Real.norm_eq_abs, abs_of_pos hh])
  have hm : |(R (-h • v)).value - f (-h • v)| ≤ ν :=
    hreport _ (by rw [norm_smul, hv, mul_one, Real.norm_eq_abs, abs_neg, abs_of_pos hh])
  have hd := TangentEVD.chosen_potential f 0 v hh hγ hf
    (by simpa only [zero_add] using hl) (by simpa only [zero_add] using hthird)
    hvc.le hhsmall hνh (by simpa only [zero_add] using hp)
    (by simpa only [zero_sub, neg_smul] using hm)
  rw [chosen_value R x t h hr f]
  simpa only [zero_add, zero_sub, neg_smul] using hd

theorem compute_cost (R : FullHessian.Report m) (x : Space m) (t h : ℝ)
    (hr : 0 < (Frame.canonical m x).rank) {Q : ℕ}
    (hQstencil : ∀ y, ‖y‖ ≤ 2 * |t| → (R y).cost ≤ Q)
    (hQend : ∀ y, ‖y‖ ≤ |h| → (R y).cost ≤ Q) :
    (compute R x t h hr).cost ≤
      m ^ 2 * (4 * Q + 100 * (m + 1) + 18) + 1000 * (m + 1) ^ 5 +
        2 * Q + 3 * m + 25 := by
  have hd := RuntimeDirection.compute_cost R x t hr hQstencil
  have hn := RuntimeDirection.compute_unit R x t hr
  have hp := hQend (h • (RuntimeDirection.compute R x t hr).value)
    (by rw [norm_smul, hn, mul_one, Real.norm_eq_abs])
  have hm := hQend (-h • (RuntimeDirection.compute R x t hr).value)
    (by rw [norm_smul, hn, mul_one, Real.norm_eq_abs, abs_neg])
  dsimp only [compute]
  omega

end HigherRankKSRuntime.WalkExecution
