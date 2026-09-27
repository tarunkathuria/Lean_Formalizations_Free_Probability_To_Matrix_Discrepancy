import MatrixSpencer.KSEighthManuscriptDriftGeometry



open Matrix Set
open scoped BigOperators MatrixOrder ContDiff Topology
noncomputable section
namespace MatrixSpencer.KSEighthManuscriptDrift
open KSEighthLiveEnumeration KSEighthManuscriptMovement KSEighthManuscriptDriftGeometry
variable {N d : ℕ}

theorem proposal_average_le (v : Fin N → Fin d → ℂ) {θ : ℝ} (hθ : 0 < θ) (hd : 0 < d)
    {x : Fin N → ℝ} (hx : x ∈ ksCube (1/8)) (hk : 0 < count x)
    {Q : Matrix (Fin (count x)) (Fin (count x)) ℝ} (hQ : Q.PosSemidef) (hQ1 : Q ≤ 1)
    {h ρ κ : ℝ} (hh : 0 < h) (hstep : h*Real.sqrt (N : ℝ) ≤ ρ)
    (hsmall : h*Real.sqrt (N : ℝ) ≤ 1/32)
    (hm : ∀ i, |x i| < 1/8 → ρ < 1/8 - |x i|)
    (hcurv : Matrix.trace (Q*KSEighthManuscriptPreparedInertia.hessian v θ x) ≤ 3*κ*count x) :
    (∑z, KSEighthManuscriptSampler.weight z *
      KSPotentialModels.eighthPotential (fun i => KSRankOne.atom (v i)) θ (proposal x Q h z)) ≤
      KSPotentialModels.eighthPotential (fun i => KSRankOne.atom (v i)) θ x +
      3*κ*count x*h^2 + KSEighthInputTaylorBound.fourthBudget v θ*(N : ℝ)^2*h^4/24 := by
  letI : Nonempty (Fin d) := ⟨⟨0,hd⟩⟩
  have hN : 0 < N := hk.trans_le (count_le x)
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  have hs : 0 < Real.sqrt (N : ℝ) := Real.sqrt_pos.mpr hn
  let t := h*Real.sqrt (N : ℝ)
  let w := KSEighthManuscriptNormalizedSampler.bounded (livePoint x) Q N
  let f := KSEighthFacePotential.potential v θ x
  let M := KSEighthInputTaylorBound.fourthBudget v θ
  have ht : 0 < t := mul_pos hh hs
  have htr : t ≤ 1/32 := hsmall
  have hxl : ∀j, |livePoint x j| ≤ (1/8 : ℝ) := fun j => (liveEquiv x j).property.le
  have hw (z) : ‖w z‖ ≤ 2 := KSEighthManuscriptNormalizedSampler.bounded_norm_le_two
    (livePoint x) hxl hQ (physicalCovariance_le_one x hQ1) hN (count_le x) z
  have hf : ContDiffAt ℝ 2 f 0 := (KSEighthFacePotential.contDiffAt_potential v hθ x).of_le
    (WithTop.coe_le_coe.mpr (show (2 : ℕ∞) ≤ ⊤ from le_top))
  have hsub : Icc (-t) t ⊆ Icc (-(1/32 : ℝ)) (1/32) := fun a ha => ⟨by linarith [ha.1],by linarith [ha.2]⟩
  have ha (z) : (f (t • w z)+f (-(t • w z)))/2 ≤
      f 0 + fderiv ℝ (fderiv ℝ f) 0 (w z) (w z)*t^2/2 + M*t^4/24 := by
    have hline : ContDiffOn ℝ 4 (fun a : ℝ => f (0+a • w z)) (Icc (-t) t) := by
      simpa only [zero_add] using (KSEighthHessianQueries.line_contDiffOn v hθ hd hx (w z) (hw z)).mono hsub
    have hcap : ∀a∈Icc (-t) t, |iteratedDeriv 4 (fun a : ℝ => f (0+a • w z)) a| ≤ M := by
      intro a ha
      simpa only [zero_add] using KSEighthHessianQueries.line_fourth_bound v hθ hd hx (w z) (hw z)
        (abs_le.mpr (hsub ha))
    simpa only [zero_add,zero_sub] using KSFourthDifference.directional_average_le f 0 (w z) ht hf hline hcap
  have hmean : (∑z, KSEighthManuscriptSampler.weight z *
      fderiv ℝ (fderiv ℝ f) 0 (w z) (w z)) =
      (N : ℝ)⁻¹ * (2*Matrix.trace (Q*KSEighthManuscriptPreparedInertia.hessian v θ x)) := by
    simp_rw [← KSNumericalHessian.hessian_rayleigh]
    have he := KSEighthManuscriptNormalizedSampler.bounded_quadratic_mean (livePoint x) hxl hQ hk N
      (KSNumericalHessian.hessian f 0)
    change _ = (N : ℝ)⁻¹ * _ at he
    rw [he]
    congr 1
    simp only [KSEighthManuscriptPreparedInertia.hessian, Matrix.mul_smul,Matrix.trace_smul,
      smul_eq_mul,realTrace,RCLike.re_to_real]
    change Matrix.trace (Q*KSNumericalHessian.hessian f 0) = _
    ring
  have hsum := Finset.sum_le_sum (fun z (_ : z ∈ Finset.univ) =>
    mul_le_mul_of_nonneg_left (ha z) (KSEighthManuscriptSampler.weight_pos hk z).le)
  have hsym := KSEighthManuscriptNormalizedSampler.bounded_symmetric_average (livePoint x) Q N
    (fun u => f (t • u))
  simp only [smul_neg] at hsym
  change (∑z, KSEighthManuscriptSampler.weight z*((f (t • w z)+f (-(t • w z)))/2)) = _ at hsym
  rw [hsym] at hsum
  have hrhs : (∑z, KSEighthManuscriptSampler.weight z *
      (f 0 + fderiv ℝ (fderiv ℝ f) 0 (w z) (w z)*t^2/2 + M*t^4/24)) =
      f 0 + ((N : ℝ)⁻¹*(2*Matrix.trace (Q*KSEighthManuscriptPreparedInertia.hessian v θ x)))*t^2/2 + M*t^4/24 := by
    simp only [mul_add,Finset.sum_add_distrib,← Finset.sum_mul, KSEighthManuscriptSampler.weight_sum hk,one_mul]
    simp_rw [mul_div_assoc,← mul_assoc]
    rw [← Finset.sum_mul,hmean]
    ring
  rw [hrhs] at hsum
  have heval (z) : f (t • w z) = KSPotentialModels.eighthPotential (fun i => KSRankOne.atom (v i)) θ (proposal x Q h z) :=
    potential_scaled_bounded v hθ hd hx hQ hQ1 (by simpa only [abs_of_pos hh] using hstep) hN hm z
  change (∑z, KSEighthManuscriptSampler.weight z*f (t • w z)) ≤ _ at hsum
  simp_rw [heval] at hsum
  have hzero : f 0 = KSPotentialModels.eighthPotential (fun i => KSRankOne.atom (v i)) θ x :=
    KSEighthFacePotential.potential_zero v hθ hx
  rw [hzero] at hsum
  have ht2 : t^2 = h^2*(N : ℝ) := by
    unfold t
    rw [mul_pow,Real.sq_sqrt hn.le]
  have ht4 : t^4 = h^4*(N : ℝ)^2 := by nlinarith [sq_nonneg (t^2-h^2*N)]
  rw [ht2,ht4] at hsum
  have hc : (N : ℝ)⁻¹*(2*Matrix.trace (Q*KSEighthManuscriptPreparedInertia.hessian v θ x))*(h^2*N)/2 =
      Matrix.trace (Q*KSEighthManuscriptPreparedInertia.hessian v θ x)*h^2 := by
    field_simp
  rw [hc] at hsum
  have hmcurv := mul_le_mul_of_nonneg_right hcurv (sq_nonneg h)
  nlinarith

end MatrixSpencer.KSEighthManuscriptDrift
