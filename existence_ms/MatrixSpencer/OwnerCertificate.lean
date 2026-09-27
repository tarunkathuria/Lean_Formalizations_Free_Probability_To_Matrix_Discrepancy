import MatrixSpencer.OwnerBounds

/-!
# The actual anchored certificate used in a finite epoch

The supporting density is the actual zero-Kraus maximizer at the frozen
center. No supporting-plane or variance oracle is assumed.
-/

open Matrix
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator

noncomputable section
namespace MatrixSpencer

variable {ι n : Type*} [Fintype ι] [Fintype n] [DecidableEq ι] [DecidableEq n]
variable [Nonempty n]
local instance ownerCertificateCStar : CStarAlgebra (Matrix n n ℂ) := {}

/-- The actual global Tsallis-only maximizing density at the saved center. -/
def ownerCertificateDensity (Hstar : Matrix n n ℂ) (θ : ℝ) : Matrix n n ℂ :=
  densityOptimizer Hstar (fun _ : Empty => (0 : Matrix n n ℂ)) θ

/-- The frozen supporting-plane displacement. -/
def ownerCertificateTangent (Hstar : Matrix n n ℂ) (θ : ℝ) (H : Matrix n n ℂ) : ℝ :=
  realTrace (ownerCertificateDensity Hstar θ * (H - Hstar))

/-- The actual owner potential above its saved global supporting plane. -/
def ownerCertificate (Hstar : Matrix n n ℂ) (A : ι → Matrix n n ℂ)
    (θ : ℝ) (H : Matrix n n ℂ) (C : Matrix ι ι ℝ) : ℝ :=
  ownerPotential H A C θ - baseDensityPotential Hstar θ - ownerCertificateTangent Hstar θ H

/-- Fixed coefficient gradient used for the scalar tangent martingale. -/
def ownerCertificateGradient (Hstar : Matrix n n ℂ) (A : ι → Matrix n n ℂ)
    (θ : ℝ) : ι → ℝ := fun i => realTrace (ownerCertificateDensity Hstar θ * A i)

omit [Fintype ι] [DecidableEq ι] in
theorem ownerCertificateDensity_mem (Hstar : Matrix n n ℂ) (θ : ℝ) :
    ownerCertificateDensity Hstar θ ∈ densitySet :=
  densityOptimizer_mem Hstar (fun _ : Empty => (0 : Matrix n n ℂ)) θ

omit [Fintype ι] [DecidableEq ι] in
/-- The actual saved optimizer gives a global supporting plane for the base potential. -/
theorem baseDensityPotential_certificate_support
    (Hstar H : Matrix n n ℂ) (θ : ℝ) :
    baseDensityPotential Hstar θ + ownerCertificateTangent Hstar θ H ≤ baseDensityPotential H θ := by
  have h := densityPotential_supporting_plane Hstar H (fun _ : Empty => (0 : Matrix n n ℂ)) θ
    (ownerCertificateDensity_mem Hstar θ) (densityOptimizer_isMaxOn Hstar _ θ)
  rw [realTrace_mul_comm] at h
  exact h

/-- The anchored certificate is nonnegative at every PSD owner covariance. -/
theorem ownerCertificate_nonneg (Hstar H : Matrix n n ℂ)
    (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).IsHermitian)
    {C : Matrix ι ι ℝ} (hC : C.PosSemidef) (θ : ℝ) :
    0 ≤ ownerCertificate Hstar A θ H C := by
  have hs := baseDensityPotential_certificate_support Hstar H θ
  have ho := baseDensityPotential_le_owner H A hA hC θ
  unfold ownerCertificate
  linarith

omit [DecidableEq ι] in
@[simp] theorem ownerCertificate_at_anchor (Hstar : Matrix n n ℂ)
    (A : ι → Matrix n n ℂ) (θ : ℝ) (C : Matrix ι ι ℝ) :
    ownerCertificate Hstar A θ Hstar C = ownerPotential Hstar A C θ - baseDensityPotential Hstar θ := by
  simp only [ownerCertificate, ownerCertificateTangent, sub_self, Matrix.mul_zero,
    realTrace_zero, sub_zero]

/-- Initial certificate cost depends on the original retained count, not physical dimension. -/
theorem ownerCertificate_initial_le (Hstar : Matrix n n ℂ)
    (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).IsHermitian) (hN : ∀ i, ‖A i‖ ≤ 1)
    {C : Matrix ι ι ℝ} (hC : C.PosSemidef) (hC1 : C ≤ 1) (θ : ℝ) :
    ownerCertificate Hstar A θ Hstar C ≤ 2 * Real.sqrt (Fintype.card ι : ℝ) := by
  rw [ownerCertificate_at_anchor]
  have h := ownerPotential_le_base_add Hstar A hA hN hC hC1 θ
  linarith

omit [Fintype ι] [DecidableEq ι] in
/-- Every coordinate of the actual saved gradient is bounded by one. -/
theorem abs_ownerCertificateGradient_le_one (Hstar : Matrix n n ℂ)
    (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).IsHermitian) (hN : ∀ i, ‖A i‖ ≤ 1)
    (θ : ℝ) (i : ι) : |ownerCertificateGradient Hstar A θ i| ≤ 1 := by
  unfold ownerCertificateGradient
  rw [realTrace_mul_comm]
  exact (abs_realTrace_mul_density_le_norm (hA i) (ownerCertificateDensity_mem Hstar θ)).trans (hN i)

/-- The actual scalar tangent has variance at most the original retained count
under every PSD movement covariance bounded by identity. -/
theorem ownerCertificateGradient_covariance_bound (Hstar : Matrix n n ℂ)
    (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).IsHermitian) (hN : ∀ i, ‖A i‖ ≤ 1)
    (θ : ℝ) {Q : Matrix ι ι ℝ} (hQ : Q.PosSemidef) (hQ1 : Q ≤ 1) :
    0 ≤ ownerCertificateGradient Hstar A θ ⬝ᵥ (Q *ᵥ ownerCertificateGradient Hstar A θ) ∧
      ownerCertificateGradient Hstar A θ ⬝ᵥ (Q *ᵥ ownerCertificateGradient Hstar A θ) ≤
        (Fintype.card ι : ℝ) := by
  let g := ownerCertificateGradient Hstar A θ
  have hlo : 0 ≤ g ⬝ᵥ (Q *ᵥ g) := by simpa only [star_trivial] using hQ.2 g
  have hhi := (Matrix.le_iff.mp hQ1).2 g
  simp only [star_trivial, Matrix.sub_mulVec, Matrix.one_mulVec, dotProduct_sub, sub_nonneg] at hhi
  have hg : g ⬝ᵥ g ≤ (Fintype.card ι : ℝ) := by
    calc
      _ = ∑ i, (g i) ^ 2 := by simp only [dotProduct, pow_two]
      _ ≤ ∑ _i : ι, (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro i _
        have h := abs_ownerCertificateGradient_le_one Hstar A hA hN θ i
        have hs := (sq_le_sq₀ (abs_nonneg (g i)) (by norm_num : (0 : ℝ) ≤ 1)).mpr h
        simpa only [sq_abs, one_pow] using hs
      _ = _ := by simp
  exact ⟨hlo, hhi.trans hg⟩

omit [Fintype ι] [DecidableEq ι] in
theorem ownerCertificateTangent_difference (Hstar H H' : Matrix n n ℂ) (θ : ℝ) :
    ownerCertificateTangent Hstar θ H' - ownerCertificateTangent Hstar θ H =
      realTrace (ownerCertificateDensity Hstar θ * (H' - H)) := by
  simp only [ownerCertificateTangent, Matrix.mul_sub, realTrace_sub]
  ring

omit [DecidableEq ι] in
/-- Exact tangent increment in the original coefficient labels. -/
theorem ownerCertificateTangent_increment (Hstar H : Matrix n n ℂ)
    (A : ι → Matrix n n ℂ) (θ : ℝ) (v : ι → ℝ) :
    ownerCertificateTangent Hstar θ (H + ∑ i, v i • A i) - ownerCertificateTangent Hstar θ H =
      ∑ i, v i * ownerCertificateGradient Hstar A θ i := by
  rw [ownerCertificateTangent_difference, add_sub_cancel_left]
  simp only [Matrix.mul_sum, realTrace_sum, Matrix.mul_smul, realTrace_smul, ownerCertificateGradient]

omit [DecidableEq ι] in
theorem ownerCertificate_center_difference (Hstar H H' : Matrix n n ℂ)
    (A : ι → Matrix n n ℂ) (θ : ℝ) (C : Matrix ι ι ℝ) :
    ownerCertificate Hstar A θ H' C - ownerCertificate Hstar A θ H C =
      (ownerPotential H' A C θ - ownerPotential H A C θ) -
        realTrace (ownerCertificateDensity Hstar θ * (H' - H)) := by
  unfold ownerCertificate
  rw [← ownerCertificateTangent_difference]
  ring

/-- Center rounding changes the certificate by at most twice the operator norm error. -/
theorem abs_ownerCertificate_center_difference_le
    (Hstar : Matrix n n ℂ) {H H' : Matrix n n ℂ} (hH : H.IsHermitian) (hH' : H'.IsHermitian)
    (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).IsHermitian)
    {C : Matrix ι ι ℝ} (hC : C.PosSemidef) (θ : ℝ) :
    |ownerCertificate Hstar A θ H' C - ownerCertificate Hstar A θ H C| ≤ 2 * ‖H' - H‖ := by
  rw [ownerCertificate_center_difference]
  have he := abs_ownerPotential_sub_le_norm hH hH' A hA hC θ
  have ht := abs_realTrace_mul_density_le_norm (hH'.sub hH) (ownerCertificateDensity_mem Hstar θ)
  rw [realTrace_mul_comm] at ht
  have hs := abs_sub (ownerPotential H' A C θ - ownerPotential H A C θ)
    (realTrace (ownerCertificateDensity Hstar θ * (H' - H)))
  linarith

omit [DecidableEq ι] in
/-- Terminal potential growth is the certificate growth plus the exact frozen tangent. -/
theorem ownerCertificate_terminal_identity (Hstar H : Matrix n n ℂ)
    (A : ι → Matrix n n ℂ) (θ : ℝ) (Cstart Cend : Matrix ι ι ℝ) :
    ownerPotential H A Cend θ - ownerPotential Hstar A Cstart θ =
      ownerCertificate Hstar A θ H Cend - ownerCertificate Hstar A θ Hstar Cstart +
        ownerCertificateTangent Hstar θ H := by
  rw [ownerCertificate_at_anchor]
  unfold ownerCertificate
  ring

/-- A selected finite endpoint converts its certificate and tangent bounds to actual potential growth. -/
theorem ownerCertificate_terminal_le (Hstar H : Matrix n n ℂ)
    (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).IsHermitian) (θ : ℝ)
    {Cstart Cend : Matrix ι ι ℝ} (hCstart : Cstart.PosSemidef) (M : ℝ)
    (hM : ownerCertificateTangent Hstar θ H = M) :
    ownerPotential H A Cend θ - ownerPotential Hstar A Cstart θ ≤
      ownerCertificate Hstar A θ H Cend + |M| := by
  rw [ownerCertificate_terminal_identity, hM]
  have h0 := ownerCertificate_nonneg Hstar Hstar A hA hCstart θ
  linarith [le_abs_self M]

/-- Rounding the selected center adds at most its operator-norm error to the actual endpoint cost. -/
theorem ownerCertificate_terminal_rounding_le (Hstar : Matrix n n ℂ)
    {H Hfinal : Matrix n n ℂ} (hH : H.IsHermitian) (hHfinal : Hfinal.IsHermitian)
    (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).IsHermitian) (θ : ℝ)
    {Cstart Cend : Matrix ι ι ℝ} (hCstart : Cstart.PosSemidef) (hCend : Cend.PosSemidef)
    (M r : ℝ) (hM : ownerCertificateTangent Hstar θ H = M) (hr : ‖Hfinal - H‖ ≤ r) :
    ownerPotential Hfinal A Cend θ - ownerPotential Hstar A Cstart θ ≤
      ownerCertificate Hstar A θ H Cend + |M| + r := by
  have ht := ownerCertificate_terminal_le Hstar H A hA θ (Cend := Cend) hCstart M hM
  have hr' := ownerPotential_sub_le_norm hH hHfinal A hA hCend θ
  linarith

/-- Accumulated center-rounding errors may be separated from the scalar
martingale; only their terminal tangent discrepancy is charged. -/
theorem ownerCertificate_terminal_tangent_error_le (Hstar H : Matrix n n ℂ)
    (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).IsHermitian) (θ : ℝ)
    {Cstart Cend : Matrix ι ι ℝ} (hCstart : Cstart.PosSemidef) (M r : ℝ)
    (herr : |ownerCertificateTangent Hstar θ H - M| ≤ r) :
    ownerPotential H A Cend θ - ownerPotential Hstar A Cstart θ ≤
      ownerCertificate Hstar A θ H Cend + |M| + r := by
  rw [ownerCertificate_terminal_identity]
  have h0 := ownerCertificate_nonneg Hstar Hstar A hA hCstart θ
  have he := (abs_le.mp herr).2
  linarith [le_abs_self M]

omit [Fintype ι] [DecidableEq ι] in
/-- Each actual Hermitian center correction changes the frozen tangent by at
most its Euclidean operator norm. -/
theorem abs_ownerCertificateTangent_difference_le (Hstar : Matrix n n ℂ)
    {H H' : Matrix n n ℂ} (hH : H.IsHermitian) (hH' : H'.IsHermitian) (θ : ℝ) :
    |ownerCertificateTangent Hstar θ H' - ownerCertificateTangent Hstar θ H| ≤ ‖H' - H‖ := by
  rw [ownerCertificateTangent_difference, realTrace_mul_comm]
  exact abs_realTrace_mul_density_le_norm (hH'.sub hH) (ownerCertificateDensity_mem Hstar θ)

end MatrixSpencer
