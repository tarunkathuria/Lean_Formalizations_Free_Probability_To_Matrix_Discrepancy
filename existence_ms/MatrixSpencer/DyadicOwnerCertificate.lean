import MatrixSpencer.DyadicDensityOptimizer
import MatrixSpencer.RegularizedOwnerPotential

/-!
# The actual anchored dyadic owner certificate

The frozen supporting density is the actual zero-Kraus maximizer. Its
existence follows from density compactness and continuity for every m and
theta. None of the certificate facts requires faithfulness or a response
estimate, and m and theta stay fixed throughout every identity.
-/

open Matrix
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section
namespace MatrixSpencer

variable {ι n : Type*} [Fintype ι] [Fintype n] [DecidableEq ι] [DecidableEq n]
local instance dyadicOwnerCertificateCStar : CStarAlgebra (Matrix n n ℂ) := {}

omit [Fintype ι] [DecidableEq ι] in
theorem dyadicDensityObjective_empty (H S : Matrix n n ℂ) (m : ℕ) (θ : ℝ) :
    dyadicDensityObjective H (fun _ : Empty => (0 : Matrix n n ℂ)) m θ S =
      regularizedBaseObjective H (dyadicTsallisRegularizer m θ) S := by
  simp [dyadicDensityObjective, regularizedBaseObjective, krausChannel, fidelity, fidelityCore]

omit [Fintype ι] [DecidableEq ι] in
theorem dyadicDensityPotential_empty (H : Matrix n n ℂ) (m : ℕ) (θ : ℝ) :
    dyadicDensityPotential H (fun _ : Empty => (0 : Matrix n n ℂ)) m θ =
      regularizedBasePotential H (dyadicTsallisRegularizer m θ) := by
  unfold dyadicDensityPotential regularizedBasePotential
  congr 2
  funext S
  exact dyadicDensityObjective_empty H S m θ

variable [Nonempty n]

def dyadicOwnerCertificateDensity (Hstar : Matrix n n ℂ) (m : ℕ) (θ : ℝ) : Matrix n n ℂ :=
  dyadicDensityOptimizer Hstar (fun _ : Empty => (0 : Matrix n n ℂ)) m θ

def dyadicOwnerCertificateTangent (Hstar : Matrix n n ℂ) (m : ℕ) (θ : ℝ)
    (H : Matrix n n ℂ) : ℝ :=
  realTrace (dyadicOwnerCertificateDensity Hstar m θ * (H - Hstar))

def dyadicOwnerCertificate (Hstar : Matrix n n ℂ) (A : ι → Matrix n n ℂ)
    (m : ℕ) (θ : ℝ) (H : Matrix n n ℂ) (C : Matrix ι ι ℝ) : ℝ :=
  regularizedOwnerPotential H A C (dyadicTsallisRegularizer m θ) -
    regularizedBasePotential Hstar (dyadicTsallisRegularizer m θ) -
      dyadicOwnerCertificateTangent Hstar m θ H

def dyadicOwnerCertificateGradient (Hstar : Matrix n n ℂ) (A : ι → Matrix n n ℂ)
    (m : ℕ) (θ : ℝ) : ι → ℝ :=
  fun i => realTrace (dyadicOwnerCertificateDensity Hstar m θ * A i)

omit [Fintype ι] [DecidableEq ι] in
theorem dyadicOwnerCertificateDensity_mem (Hstar : Matrix n n ℂ) (m : ℕ) (θ : ℝ) :
    dyadicOwnerCertificateDensity Hstar m θ ∈ densitySet :=
  dyadicDensityOptimizer_mem Hstar (fun _ : Empty => (0 : Matrix n n ℂ)) m θ

omit [Fintype ι] [DecidableEq ι] in
theorem regularizedBasePotential_dyadic_certificate_support
    (Hstar H : Matrix n n ℂ) (m : ℕ) (θ : ℝ) :
    regularizedBasePotential Hstar (dyadicTsallisRegularizer m θ) +
      dyadicOwnerCertificateTangent Hstar m θ H ≤
        regularizedBasePotential H (dyadicTsallisRegularizer m θ) := by
  have h := dyadicDensityPotential_supporting_plane Hstar H
    (fun _ : Empty => (0 : Matrix n n ℂ)) m θ (dyadicOwnerCertificateDensity_mem Hstar m θ)
    (dyadicDensityOptimizer_isMaxOn Hstar _ m θ)
  rw [dyadicDensityPotential_empty, dyadicDensityPotential_empty, realTrace_mul_comm] at h
  exact h

theorem dyadicOwnerCertificate_nonneg (Hstar H : Matrix n n ℂ)
    (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).IsHermitian)
    {C : Matrix ι ι ℝ} (hC : C.PosSemidef) (m : ℕ) (θ : ℝ) :
    0 ≤ dyadicOwnerCertificate Hstar A m θ H C := by
  have hs := regularizedBasePotential_dyadic_certificate_support Hstar H m θ
  have ho := regularizedBasePotential_le_owner H A hA hC (dyadicTsallisRegularizer m θ)
    (continuousOn_density_dyadicTsallisRegularizer m θ)
  unfold dyadicOwnerCertificate
  linarith

omit [DecidableEq ι] in
@[simp] theorem dyadicOwnerCertificate_at_anchor (Hstar : Matrix n n ℂ)
    (A : ι → Matrix n n ℂ) (m : ℕ) (θ : ℝ) (C : Matrix ι ι ℝ) :
    dyadicOwnerCertificate Hstar A m θ Hstar C =
      regularizedOwnerPotential Hstar A C (dyadicTsallisRegularizer m θ) -
        regularizedBasePotential Hstar (dyadicTsallisRegularizer m θ) := by
  simp only [dyadicOwnerCertificate, dyadicOwnerCertificateTangent, sub_self, Matrix.mul_zero,
    realTrace_zero, sub_zero]

theorem dyadicOwnerCertificate_initial_le (Hstar : Matrix n n ℂ)
    (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).IsHermitian) (hN : ∀ i, ‖A i‖ ≤ 1)
    {C : Matrix ι ι ℝ} (hC : C.PosSemidef) (hC1 : C ≤ 1) (m : ℕ) (θ : ℝ) :
    dyadicOwnerCertificate Hstar A m θ Hstar C ≤ 2 * Real.sqrt (Fintype.card ι : ℝ) := by
  rw [dyadicOwnerCertificate_at_anchor]
  have h := regularizedOwnerPotential_le_base_add Hstar A hA hN hC hC1
    (dyadicTsallisRegularizer m θ) (continuousOn_density_dyadicTsallisRegularizer m θ)
  linarith

omit [Fintype ι] [DecidableEq ι] in
theorem abs_dyadicOwnerCertificateGradient_le_one (Hstar : Matrix n n ℂ)
    (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).IsHermitian) (hN : ∀ i, ‖A i‖ ≤ 1)
    (m : ℕ) (θ : ℝ) (i : ι) : |dyadicOwnerCertificateGradient Hstar A m θ i| ≤ 1 := by
  unfold dyadicOwnerCertificateGradient
  rw [realTrace_mul_comm]
  exact (abs_realTrace_mul_density_le_norm (hA i)
    (dyadicOwnerCertificateDensity_mem Hstar m θ)).trans (hN i)

theorem dyadicOwnerCertificateGradient_covariance_bound (Hstar : Matrix n n ℂ)
    (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).IsHermitian) (hN : ∀ i, ‖A i‖ ≤ 1)
    (m : ℕ) (θ : ℝ) {Q : Matrix ι ι ℝ} (hQ : Q.PosSemidef) (hQ1 : Q ≤ 1) :
    0 ≤ dyadicOwnerCertificateGradient Hstar A m θ ⬝ᵥ (Q *ᵥ dyadicOwnerCertificateGradient Hstar A m θ) ∧
      dyadicOwnerCertificateGradient Hstar A m θ ⬝ᵥ (Q *ᵥ dyadicOwnerCertificateGradient Hstar A m θ) ≤
        (Fintype.card ι : ℝ) := by
  let g := dyadicOwnerCertificateGradient Hstar A m θ
  have hlo : 0 ≤ g ⬝ᵥ (Q *ᵥ g) := by simpa only [star_trivial] using hQ.2 g
  have hhi := (Matrix.le_iff.mp hQ1).2 g
  simp only [star_trivial, Matrix.sub_mulVec, Matrix.one_mulVec, dotProduct_sub, sub_nonneg] at hhi
  have hg : g ⬝ᵥ g ≤ (Fintype.card ι : ℝ) := by
    calc
      _ = ∑ i, (g i) ^ 2 := by simp only [dotProduct, pow_two]
      _ ≤ ∑ _i : ι, (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro i _
        have h := abs_dyadicOwnerCertificateGradient_le_one Hstar A hA hN m θ i
        have hs := (sq_le_sq₀ (abs_nonneg (g i)) (by norm_num : (0 : ℝ) ≤ 1)).mpr h
        simpa only [sq_abs, one_pow] using hs
      _ = _ := by simp
  exact ⟨hlo, hhi.trans hg⟩

omit [Fintype ι] [DecidableEq ι] in
theorem dyadicOwnerCertificateTangent_difference (Hstar H H' : Matrix n n ℂ) (m : ℕ) (θ : ℝ) :
    dyadicOwnerCertificateTangent Hstar m θ H' - dyadicOwnerCertificateTangent Hstar m θ H =
      realTrace (dyadicOwnerCertificateDensity Hstar m θ * (H' - H)) := by
  simp only [dyadicOwnerCertificateTangent, Matrix.mul_sub, realTrace_sub]
  ring

omit [DecidableEq ι] in
theorem dyadicOwnerCertificateTangent_increment (Hstar H : Matrix n n ℂ)
    (A : ι → Matrix n n ℂ) (m : ℕ) (θ : ℝ) (v : ι → ℝ) :
    dyadicOwnerCertificateTangent Hstar m θ (H + ∑ i, v i • A i) -
      dyadicOwnerCertificateTangent Hstar m θ H =
        ∑ i, v i * dyadicOwnerCertificateGradient Hstar A m θ i := by
  rw [dyadicOwnerCertificateTangent_difference, add_sub_cancel_left]
  simp only [Matrix.mul_sum, realTrace_sum, Matrix.mul_smul, realTrace_smul,
    dyadicOwnerCertificateGradient]

omit [DecidableEq ι] in
theorem dyadicOwnerCertificate_center_difference (Hstar H H' : Matrix n n ℂ)
    (A : ι → Matrix n n ℂ) (m : ℕ) (θ : ℝ) (C : Matrix ι ι ℝ) :
    dyadicOwnerCertificate Hstar A m θ H' C - dyadicOwnerCertificate Hstar A m θ H C =
      (regularizedOwnerPotential H' A C (dyadicTsallisRegularizer m θ) -
        regularizedOwnerPotential H A C (dyadicTsallisRegularizer m θ)) -
          realTrace (dyadicOwnerCertificateDensity Hstar m θ * (H' - H)) := by
  unfold dyadicOwnerCertificate
  rw [← dyadicOwnerCertificateTangent_difference]
  ring

theorem abs_dyadicOwnerCertificate_center_difference_le
    (Hstar : Matrix n n ℂ) {H H' : Matrix n n ℂ} (hH : H.IsHermitian) (hH' : H'.IsHermitian)
    (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).IsHermitian)
    {C : Matrix ι ι ℝ} (hC : C.PosSemidef) (m : ℕ) (θ : ℝ) :
    |dyadicOwnerCertificate Hstar A m θ H' C - dyadicOwnerCertificate Hstar A m θ H C| ≤
      2 * ‖H' - H‖ := by
  rw [dyadicOwnerCertificate_center_difference]
  have he := abs_regularizedOwnerPotential_sub_le_norm hH hH' A hA hC
    (dyadicTsallisRegularizer m θ) (continuousOn_density_dyadicTsallisRegularizer m θ)
  have ht := abs_realTrace_mul_density_le_norm (hH'.sub hH) (dyadicOwnerCertificateDensity_mem Hstar m θ)
  rw [realTrace_mul_comm] at ht
  have hs := abs_sub (regularizedOwnerPotential H' A C (dyadicTsallisRegularizer m θ) -
    regularizedOwnerPotential H A C (dyadicTsallisRegularizer m θ))
      (realTrace (dyadicOwnerCertificateDensity Hstar m θ * (H' - H)))
  linarith

omit [DecidableEq ι] in
theorem dyadicOwnerCertificate_terminal_identity (Hstar H : Matrix n n ℂ)
    (A : ι → Matrix n n ℂ) (m : ℕ) (θ : ℝ) (Cstart Cend : Matrix ι ι ℝ) :
    regularizedOwnerPotential H A Cend (dyadicTsallisRegularizer m θ) -
      regularizedOwnerPotential Hstar A Cstart (dyadicTsallisRegularizer m θ) =
        dyadicOwnerCertificate Hstar A m θ H Cend -
          dyadicOwnerCertificate Hstar A m θ Hstar Cstart + dyadicOwnerCertificateTangent Hstar m θ H := by
  rw [dyadicOwnerCertificate_at_anchor]
  unfold dyadicOwnerCertificate
  ring

theorem dyadicOwnerCertificate_terminal_le (Hstar H : Matrix n n ℂ)
    (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).IsHermitian) (m : ℕ) (θ : ℝ)
    {Cstart Cend : Matrix ι ι ℝ} (hCstart : Cstart.PosSemidef) (M : ℝ)
    (hM : dyadicOwnerCertificateTangent Hstar m θ H = M) :
    regularizedOwnerPotential H A Cend (dyadicTsallisRegularizer m θ) -
      regularizedOwnerPotential Hstar A Cstart (dyadicTsallisRegularizer m θ) ≤
        dyadicOwnerCertificate Hstar A m θ H Cend + |M| := by
  rw [dyadicOwnerCertificate_terminal_identity, hM]
  have h0 := dyadicOwnerCertificate_nonneg Hstar Hstar A hA hCstart m θ
  linarith [le_abs_self M]

theorem dyadicOwnerCertificate_terminal_rounding_le (Hstar : Matrix n n ℂ)
    {H Hfinal : Matrix n n ℂ} (hH : H.IsHermitian) (hHfinal : Hfinal.IsHermitian)
    (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).IsHermitian) (m : ℕ) (θ : ℝ)
    {Cstart Cend : Matrix ι ι ℝ} (hCstart : Cstart.PosSemidef) (hCend : Cend.PosSemidef)
    (M r : ℝ) (hM : dyadicOwnerCertificateTangent Hstar m θ H = M) (hr : ‖Hfinal - H‖ ≤ r) :
    regularizedOwnerPotential Hfinal A Cend (dyadicTsallisRegularizer m θ) -
      regularizedOwnerPotential Hstar A Cstart (dyadicTsallisRegularizer m θ) ≤
        dyadicOwnerCertificate Hstar A m θ H Cend + |M| + r := by
  have ht := dyadicOwnerCertificate_terminal_le Hstar H A hA m θ (Cend := Cend) hCstart M hM
  have hr' := regularizedOwnerPotential_sub_le_norm hH hHfinal A hA hCend
    (dyadicTsallisRegularizer m θ) (continuousOn_density_dyadicTsallisRegularizer m θ)
  linarith

theorem dyadicOwnerCertificate_terminal_tangent_error_le (Hstar H : Matrix n n ℂ)
    (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).IsHermitian) (m : ℕ) (θ : ℝ)
    {Cstart Cend : Matrix ι ι ℝ} (hCstart : Cstart.PosSemidef) (M r : ℝ)
    (herr : |dyadicOwnerCertificateTangent Hstar m θ H - M| ≤ r) :
    regularizedOwnerPotential H A Cend (dyadicTsallisRegularizer m θ) -
      regularizedOwnerPotential Hstar A Cstart (dyadicTsallisRegularizer m θ) ≤
        dyadicOwnerCertificate Hstar A m θ H Cend + |M| + r := by
  rw [dyadicOwnerCertificate_terminal_identity]
  have h0 := dyadicOwnerCertificate_nonneg Hstar Hstar A hA hCstart m θ
  have he := (abs_le.mp herr).2
  linarith [le_abs_self M]

omit [Fintype ι] [DecidableEq ι] in
theorem abs_dyadicOwnerCertificateTangent_difference_le (Hstar : Matrix n n ℂ)
    {H H' : Matrix n n ℂ} (hH : H.IsHermitian) (hH' : H'.IsHermitian) (m : ℕ) (θ : ℝ) :
    |dyadicOwnerCertificateTangent Hstar m θ H' - dyadicOwnerCertificateTangent Hstar m θ H| ≤
      ‖H' - H‖ := by
  rw [dyadicOwnerCertificateTangent_difference, realTrace_mul_comm]
  exact abs_realTrace_mul_density_le_norm (hH'.sub hH) (dyadicOwnerCertificateDensity_mem Hstar m θ)

omit [DecidableEq ι] in
theorem dyadicOwnerCertificate_mixed_difference (Hstar H H' : Matrix n n ℂ)
    (A : ι → Matrix n n ℂ) (m : ℕ) (θ : ℝ) (C C' : Matrix ι ι ℝ) :
    dyadicOwnerCertificate Hstar A m θ H' C' - dyadicOwnerCertificate Hstar A m θ H C =
      (regularizedOwnerPotential H' A C' (dyadicTsallisRegularizer m θ) -
        regularizedOwnerPotential H A C (dyadicTsallisRegularizer m θ)) -
          realTrace (dyadicOwnerCertificateDensity Hstar m θ * (H' - H)) := by
  unfold dyadicOwnerCertificate
  rw [← dyadicOwnerCertificateTangent_difference]
  ring

omit [DecidableEq ι] in
theorem dyadicOwnerCertificate_covariance_payment (Hstar H : Matrix n n ℂ)
    (A : ι → Matrix n n ℂ) (m : ℕ) (θ price paid : ℝ) (C C' : Matrix ι ι ℝ)
    (hp : regularizedOwnerPotential H A C' (dyadicTsallisRegularizer m θ) + price * paid ≤
      regularizedOwnerPotential H A C (dyadicTsallisRegularizer m θ)) :
    dyadicOwnerCertificate Hstar A m θ H C' + price * paid ≤ dyadicOwnerCertificate Hstar A m θ H C := by
  unfold dyadicOwnerCertificate
  linarith

theorem dyadicOwnerCertificate_rounding_preparation_le
    (Hstar Hmoved Hrounded : Matrix n n ℂ)
    (hHmoved : Hmoved.IsHermitian) (hHrounded : Hrounded.IsHermitian)
    (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).IsHermitian)
    (m : ℕ) (θ price paid r : ℝ) {C C' : Matrix ι ι ℝ} (hC : C.PosSemidef)
    (hp : regularizedOwnerPotential Hrounded A C' (dyadicTsallisRegularizer m θ) + price * paid ≤
      regularizedOwnerPotential Hrounded A C (dyadicTsallisRegularizer m θ))
    (hr : ‖Hrounded - Hmoved‖ ≤ r) :
    dyadicOwnerCertificate Hstar A m θ Hrounded C' + price * paid ≤
      dyadicOwnerCertificate Hstar A m θ Hmoved C + 2 * r := by
  have hpay := dyadicOwnerCertificate_covariance_payment Hstar Hrounded A m θ price paid C C' hp
  have hround := abs_dyadicOwnerCertificate_center_difference_le Hstar hHmoved hHrounded A hA hC m θ
  have hle := (le_abs_self
    (dyadicOwnerCertificate Hstar A m θ Hrounded C - dyadicOwnerCertificate Hstar A m θ Hmoved C)).trans hround
  linarith

end MatrixSpencer
