import MatrixSpencer.RectangularRidgeOwnerBounds

/-!
# The actual anchored certificate for the rectangular ridge walk

The saved density is the actual mixed zero-Kraus optimizer. Its density
membership and global supporting plane are proved here. All identities retain
this fixed density and the same mixed regularizer throughout an epoch.
-/
open Matrix
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section
namespace MatrixSpencer.RectangularRidgeCertificate
open RectangularRidgeCovarianceCalculus RectangularRidgeOwnerBounds
variable {ι n : Type*} [Fintype ι] [Fintype n] [DecidableEq ι] [DecidableEq n]
local instance ridgeCertificateCStar : CStarAlgebra (Matrix n n ℂ) := {}

omit [Fintype ι] [DecidableEq ι] in
lemma empty_objective_eq_base (H S : Matrix n n ℂ) (m : ℕ) (θ κ : ℝ) :
    RectangularRidgePotential.objective H (fun _ : Empty => (0 : Matrix n n ℂ)) m θ κ S =
      regularizedBaseObjective H (regularizer m θ κ) S := by
  simp [RectangularRidgePotential.objective, dyadicDensityObjective, regularizer,
    regularizedBaseObjective, krausChannel, fidelity, fidelityCore]
  ring

omit [Fintype ι] [DecidableEq ι] in
lemma empty_potential_eq_base (H : Matrix n n ℂ) (m : ℕ) (θ κ : ℝ) :
    RectangularRidgePotential.potential H (fun _ : Empty => (0 : Matrix n n ℂ)) m θ κ =
      basePotential m H θ κ := by
  unfold RectangularRidgePotential.potential basePotential regularizedBasePotential
  congr 2
  funext S
  exact empty_objective_eq_base H S m θ κ

variable [Nonempty n]

/-- The genuine mixed maximizer at the saved center, with zero source. -/
def density (Hstar : Matrix n n ℂ) (m : ℕ) (θ κ : ℝ) : Matrix n n ℂ :=
  RectangularRidgePotential.optimizer Hstar (fun _ : Empty => (0 : Matrix n n ℂ)) m θ κ

def tangent (Hstar : Matrix n n ℂ) (m : ℕ) (θ κ : ℝ) (H : Matrix n n ℂ) : ℝ :=
  realTrace (density Hstar m θ κ * (H - Hstar))

def certificate (Hstar : Matrix n n ℂ) (A : ι → Matrix n n ℂ)
    (m : ℕ) (θ κ : ℝ) (H : Matrix n n ℂ) (C : Matrix ι ι ℝ) : ℝ :=
  regularizedOwnerPotential H A C (regularizer m θ κ) -
    regularizedBasePotential Hstar (regularizer m θ κ) - tangent Hstar m θ κ H

def gradient (Hstar : Matrix n n ℂ) (A : ι → Matrix n n ℂ)
    (m : ℕ) (θ κ : ℝ) : ι → ℝ := fun i => realTrace (density Hstar m θ κ * A i)

omit [Fintype ι] [DecidableEq ι] in
lemma density_mem (Hstar : Matrix n n ℂ) (m : ℕ) (θ κ : ℝ) :
    density Hstar m θ κ ∈ densitySet :=
  RectangularRidgePotential.optimizer_mem Hstar (fun _ : Empty => (0 : Matrix n n ℂ)) m θ κ

omit [Fintype ι] [DecidableEq ι] in
lemma density_max_base (Hstar : Matrix n n ℂ) (m : ℕ) (θ κ : ℝ) :
    ∀ T ∈ densitySet, regularizedBaseObjective Hstar (regularizer m θ κ) T ≤
      regularizedBaseObjective Hstar (regularizer m θ κ) (density Hstar m θ κ) := by
  intro T hT
  have h := RectangularRidgePotential.optimizer_max Hstar
    (fun _ : Empty => (0 : Matrix n n ℂ)) m θ κ T hT
  simpa only [empty_objective_eq_base] using h

omit [Fintype ι] [DecidableEq ι] in
lemma base_support (Hstar H : Matrix n n ℂ) (m : ℕ) (θ κ : ℝ) :
    regularizedBasePotential Hstar (regularizer m θ κ) + tangent Hstar m θ κ H ≤
      regularizedBasePotential H (regularizer m θ κ) := by
  rw [regularizedBasePotential_eq_of_maximizer Hstar (regularizer m θ κ)
    (density_mem Hstar m θ κ) (density_max_base Hstar m θ κ)]
  have h := regularizedBaseObjective_le_potential H (regularizer m θ κ)
    (continuousOn_regularizer m θ κ) (density_mem Hstar m θ κ)
  unfold regularizedBaseObjective tangent at *
  rw [Matrix.mul_sub, realTrace_sub, realTrace_mul_comm (density Hstar m θ κ) H,
    realTrace_mul_comm (density Hstar m θ κ) Hstar]
  linarith

theorem certificate_nonneg (Hstar H : Matrix n n ℂ)
    (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).IsHermitian)
    {C : Matrix ι ι ℝ} (hC : C.PosSemidef) (m : ℕ) (θ κ : ℝ) :
    0 ≤ certificate Hstar A m θ κ H C := by
  have hs := base_support Hstar H m θ κ
  have ho := regularizedBasePotential_le_owner H A hA hC (regularizer m θ κ)
    (continuousOn_regularizer m θ κ)
  unfold certificate
  linarith

omit [DecidableEq ι] in
@[simp] theorem certificate_at_anchor (Hstar : Matrix n n ℂ)
    (A : ι → Matrix n n ℂ) (m : ℕ) (θ κ : ℝ) (C : Matrix ι ι ℝ) :
    certificate Hstar A m θ κ Hstar C =
      regularizedOwnerPotential Hstar A C (regularizer m θ κ) -
        regularizedBasePotential Hstar (regularizer m θ κ) := by
  simp only [certificate, tangent, sub_self, Matrix.mul_zero,
    realTrace_zero, sub_zero]

theorem certificate_initial_le (Hstar : Matrix n n ℂ)
    (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).IsHermitian) (hN : ∀ i, ‖A i‖ ≤ 1)
    {C : Matrix ι ι ℝ} (hC : C.PosSemidef) (hC1 : C ≤ 1) (m : ℕ) (θ κ : ℝ) :
    certificate Hstar A m θ κ Hstar C ≤ 2 * Real.sqrt (Fintype.card ι : ℝ) := by
  rw [certificate_at_anchor]
  have h := regularizedOwnerPotential_le_base_add Hstar A hA hN hC hC1
    (regularizer m θ κ) (continuousOn_regularizer m θ κ)
  linarith

omit [Fintype ι] [DecidableEq ι] in
theorem abs_gradient_le_one (Hstar : Matrix n n ℂ)
    (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).IsHermitian) (hN : ∀ i, ‖A i‖ ≤ 1)
    (m : ℕ) (θ κ : ℝ) (i : ι) : |gradient Hstar A m θ κ i| ≤ 1 := by
  unfold gradient
  rw [realTrace_mul_comm]
  exact (abs_realTrace_mul_density_le_norm (hA i)
    (density_mem Hstar m θ κ)).trans (hN i)

theorem gradient_covariance_bound (Hstar : Matrix n n ℂ)
    (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).IsHermitian) (hN : ∀ i, ‖A i‖ ≤ 1)
    (m : ℕ) (θ κ : ℝ) {Q : Matrix ι ι ℝ} (hQ : Q.PosSemidef) (hQ1 : Q ≤ 1) :
    0 ≤ gradient Hstar A m θ κ ⬝ᵥ (Q *ᵥ gradient Hstar A m θ κ) ∧
      gradient Hstar A m θ κ ⬝ᵥ (Q *ᵥ gradient Hstar A m θ κ) ≤
        (Fintype.card ι : ℝ) := by
  let g := gradient Hstar A m θ κ
  have hlo : 0 ≤ g ⬝ᵥ (Q *ᵥ g) := by simpa only [star_trivial] using hQ.2 g
  have hhi := (Matrix.le_iff.mp hQ1).2 g
  simp only [star_trivial, Matrix.sub_mulVec, Matrix.one_mulVec, dotProduct_sub, sub_nonneg] at hhi
  have hg : g ⬝ᵥ g ≤ (Fintype.card ι : ℝ) := by
    calc
      _ = ∑ i, (g i) ^ 2 := by simp only [dotProduct, pow_two]
      _ ≤ ∑ _i : ι, (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro i _
        have h := abs_gradient_le_one Hstar A hA hN m θ κ i
        have hs := (sq_le_sq₀ (abs_nonneg (g i)) (by norm_num : (0 : ℝ) ≤ 1)).mpr h
        simpa only [sq_abs, one_pow] using hs
      _ = _ := by simp
  exact ⟨hlo, hhi.trans hg⟩

omit [Fintype ι] [DecidableEq ι] in
theorem tangent_difference (Hstar H H' : Matrix n n ℂ) (m : ℕ) (θ κ : ℝ) :
    tangent Hstar m θ κ H' - tangent Hstar m θ κ H =
      realTrace (density Hstar m θ κ * (H' - H)) := by
  simp only [tangent, Matrix.mul_sub, realTrace_sub]
  ring

omit [DecidableEq ι] in
theorem tangent_increment (Hstar H : Matrix n n ℂ)
    (A : ι → Matrix n n ℂ) (m : ℕ) (θ κ : ℝ) (v : ι → ℝ) :
    tangent Hstar m θ κ (H + ∑ i, v i • A i) -
      tangent Hstar m θ κ H =
        ∑ i, v i * gradient Hstar A m θ κ i := by
  rw [tangent_difference, add_sub_cancel_left]
  simp only [Matrix.mul_sum, realTrace_sum, Matrix.mul_smul, realTrace_smul,
    gradient]

omit [DecidableEq ι] in
theorem certificate_center_difference (Hstar H H' : Matrix n n ℂ)
    (A : ι → Matrix n n ℂ) (m : ℕ) (θ κ : ℝ) (C : Matrix ι ι ℝ) :
    certificate Hstar A m θ κ H' C - certificate Hstar A m θ κ H C =
      (regularizedOwnerPotential H' A C (regularizer m θ κ) -
        regularizedOwnerPotential H A C (regularizer m θ κ)) -
          realTrace (density Hstar m θ κ * (H' - H)) := by
  unfold certificate
  rw [← tangent_difference]
  ring

theorem abs_center_difference_le
    (Hstar : Matrix n n ℂ) {H H' : Matrix n n ℂ} (hH : H.IsHermitian) (hH' : H'.IsHermitian)
    (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).IsHermitian)
    {C : Matrix ι ι ℝ} (hC : C.PosSemidef) (m : ℕ) (θ κ : ℝ) :
    |certificate Hstar A m θ κ H' C - certificate Hstar A m θ κ H C| ≤
      2 * ‖H' - H‖ := by
  rw [certificate_center_difference]
  have he := abs_regularizedOwnerPotential_sub_le_norm hH hH' A hA hC
    (regularizer m θ κ) (continuousOn_regularizer m θ κ)
  have ht := abs_realTrace_mul_density_le_norm (hH'.sub hH) (density_mem Hstar m θ κ)
  rw [realTrace_mul_comm] at ht
  have hs := abs_sub (regularizedOwnerPotential H' A C (regularizer m θ κ) -
    regularizedOwnerPotential H A C (regularizer m θ κ))
      (realTrace (density Hstar m θ κ * (H' - H)))
  linarith

omit [DecidableEq ι] in
theorem certificate_terminal_identity (Hstar H : Matrix n n ℂ)
    (A : ι → Matrix n n ℂ) (m : ℕ) (θ κ : ℝ) (Cstart Cend : Matrix ι ι ℝ) :
    regularizedOwnerPotential H A Cend (regularizer m θ κ) -
      regularizedOwnerPotential Hstar A Cstart (regularizer m θ κ) =
        certificate Hstar A m θ κ H Cend -
          certificate Hstar A m θ κ Hstar Cstart + tangent Hstar m θ κ H := by
  rw [certificate_at_anchor]
  unfold certificate
  ring

theorem certificate_terminal_le (Hstar H : Matrix n n ℂ)
    (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).IsHermitian) (m : ℕ) (θ κ : ℝ)
    {Cstart Cend : Matrix ι ι ℝ} (hCstart : Cstart.PosSemidef) (M : ℝ)
    (hM : tangent Hstar m θ κ H = M) :
    regularizedOwnerPotential H A Cend (regularizer m θ κ) -
      regularizedOwnerPotential Hstar A Cstart (regularizer m θ κ) ≤
        certificate Hstar A m θ κ H Cend + |M| := by
  rw [certificate_terminal_identity, hM]
  have h0 := certificate_nonneg Hstar Hstar A hA hCstart m θ κ
  linarith [le_abs_self M]

theorem certificate_terminal_rounding_le (Hstar : Matrix n n ℂ)
    {H Hfinal : Matrix n n ℂ} (hH : H.IsHermitian) (hHfinal : Hfinal.IsHermitian)
    (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).IsHermitian) (m : ℕ) (θ κ : ℝ)
    {Cstart Cend : Matrix ι ι ℝ} (hCstart : Cstart.PosSemidef) (hCend : Cend.PosSemidef)
    (M r : ℝ) (hM : tangent Hstar m θ κ H = M) (hr : ‖Hfinal - H‖ ≤ r) :
    regularizedOwnerPotential Hfinal A Cend (regularizer m θ κ) -
      regularizedOwnerPotential Hstar A Cstart (regularizer m θ κ) ≤
        certificate Hstar A m θ κ H Cend + |M| + r := by
  have ht := certificate_terminal_le Hstar H A hA m θ κ (Cend := Cend) hCstart M hM
  have hr' := regularizedOwnerPotential_sub_le_norm hH hHfinal A hA hCend
    (regularizer m θ κ) (continuousOn_regularizer m θ κ)
  linarith

theorem certificate_terminal_tangent_error_le (Hstar H : Matrix n n ℂ)
    (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).IsHermitian) (m : ℕ) (θ κ : ℝ)
    {Cstart Cend : Matrix ι ι ℝ} (hCstart : Cstart.PosSemidef) (M r : ℝ)
    (herr : |tangent Hstar m θ κ H - M| ≤ r) :
    regularizedOwnerPotential H A Cend (regularizer m θ κ) -
      regularizedOwnerPotential Hstar A Cstart (regularizer m θ κ) ≤
        certificate Hstar A m θ κ H Cend + |M| + r := by
  rw [certificate_terminal_identity]
  have h0 := certificate_nonneg Hstar Hstar A hA hCstart m θ κ
  have he := (abs_le.mp herr).2
  linarith [le_abs_self M]

omit [Fintype ι] [DecidableEq ι] in
theorem abs_tangent_difference_le (Hstar : Matrix n n ℂ)
    {H H' : Matrix n n ℂ} (hH : H.IsHermitian) (hH' : H'.IsHermitian) (m : ℕ) (θ κ : ℝ) :
    |tangent Hstar m θ κ H' - tangent Hstar m θ κ H| ≤
      ‖H' - H‖ := by
  rw [tangent_difference, realTrace_mul_comm]
  exact abs_realTrace_mul_density_le_norm (hH'.sub hH) (density_mem Hstar m θ κ)

omit [DecidableEq ι] in
theorem certificate_mixed_difference (Hstar H H' : Matrix n n ℂ)
    (A : ι → Matrix n n ℂ) (m : ℕ) (θ κ : ℝ) (C C' : Matrix ι ι ℝ) :
    certificate Hstar A m θ κ H' C' - certificate Hstar A m θ κ H C =
      (regularizedOwnerPotential H' A C' (regularizer m θ κ) -
        regularizedOwnerPotential H A C (regularizer m θ κ)) -
          realTrace (density Hstar m θ κ * (H' - H)) := by
  unfold certificate
  rw [← tangent_difference]
  ring

omit [DecidableEq ι] in
theorem certificate_covariance_payment (Hstar H : Matrix n n ℂ)
    (A : ι → Matrix n n ℂ) (m : ℕ) (θ κ price paid : ℝ) (C C' : Matrix ι ι ℝ)
    (hp : regularizedOwnerPotential H A C' (regularizer m θ κ) + price * paid ≤
      regularizedOwnerPotential H A C (regularizer m θ κ)) :
    certificate Hstar A m θ κ H C' + price * paid ≤ certificate Hstar A m θ κ H C := by
  unfold certificate
  linarith

theorem certificate_rounding_preparation_le
    (Hstar Hmoved Hrounded : Matrix n n ℂ)
    (hHmoved : Hmoved.IsHermitian) (hHrounded : Hrounded.IsHermitian)
    (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).IsHermitian)
    (m : ℕ) (θ κ price paid r : ℝ) {C C' : Matrix ι ι ℝ} (hC : C.PosSemidef)
    (hp : regularizedOwnerPotential Hrounded A C' (regularizer m θ κ) + price * paid ≤
      regularizedOwnerPotential Hrounded A C (regularizer m θ κ))
    (hr : ‖Hrounded - Hmoved‖ ≤ r) :
    certificate Hstar A m θ κ Hrounded C' + price * paid ≤
      certificate Hstar A m θ κ Hmoved C + 2 * r := by
  have hpay := certificate_covariance_payment Hstar Hrounded A m θ κ price paid C C' hp
  have hround := abs_center_difference_le Hstar hHmoved hHrounded A hA hC m θ κ
  have hle := (le_abs_self
    (certificate Hstar A m θ κ Hrounded C - certificate Hstar A m θ κ Hmoved C)).trans hround
  linarith

omit [Fintype ι] [DecidableEq ι] in
lemma density_posDef (Hstar : Matrix n n ℂ) {m : ℕ} (hm : 1 ≤ m)
    {θ κ : ℝ} (hθ : 0 < θ) (hκ : 0 ≤ κ) : (density Hstar m θ κ).PosDef :=
  RectangularRidgePotential.optimizer_posDef Hstar (fun _ : Empty => (0 : Matrix n n ℂ)) hm hθ hκ

omit [DecidableEq ι] in
/-- This is exactly E(H,C)-E(Hstar,0)-Tr(Sstar(H-Hstar)). -/
theorem certificate_eq_owner_difference (Hstar H : Matrix n n ℂ)
    (A : ι → Matrix n n ℂ) (m : ℕ) (θ κ : ℝ) (C : Matrix ι ι ℝ) :
    certificate Hstar A m θ κ H C =
      RectangularRidgeCovarianceCalculus.ownerPotential m H A C θ κ -
        RectangularRidgeCovarianceCalculus.ownerPotential m Hstar A 0 θ κ -
          realTrace (density Hstar m θ κ * (H - Hstar)) := by
  rw [owner_zero]
  rfl

omit [DecidableEq ι] in
@[simp] theorem certificate_zero_at_anchor (Hstar : Matrix n n ℂ)
    (A : ι → Matrix n n ℂ) (m : ℕ) (θ κ : ℝ) :
    certificate Hstar A m θ κ Hstar 0 = 0 := by
  rw [certificate_at_anchor, regularizedOwnerPotential_zero, sub_self]

/-- The anchored certificate decreases whenever the actual PSD owner decreases. -/
theorem certificate_mono_covariance (Hstar H : Matrix n n ℂ)
    (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).IsHermitian) (m : ℕ) (θ κ : ℝ)
    {C D : Matrix ι ι ℝ} (hC : C.PosSemidef) (hD : D.PosSemidef) (hCD : C ≤ D) :
    certificate Hstar A m θ κ H C ≤ certificate Hstar A m θ κ H D := by
  have h := mono_covariance m H A hA hC hD hCD θ κ
  exact sub_le_sub_right (sub_le_sub_right h _) _

/-- Exact owner reinstallation costs only the retained count in the same certificate. -/
theorem certificate_reinstall_le {ι' : Type*} [Fintype ι'] [DecidableEq ι']
    (Hstar H : Matrix n n ℂ) (A : ι → Matrix n n ℂ) (A' : ι' → Matrix n n ℂ)
    (hA : ∀ i, (A i).IsHermitian) (hA' : ∀ i, (A' i).IsHermitian) (hN' : ∀ i, ‖A' i‖ ≤ 1)
    (m : ℕ) (θ κ : ℝ) {C : Matrix ι ι ℝ} {C' : Matrix ι' ι' ℝ}
    (hC : C.PosSemidef) (hC' : C'.PosSemidef) (hC'1 : C' ≤ 1) :
    certificate Hstar A' m θ κ H C' - certificate Hstar A m θ κ H C ≤
      2 * Real.sqrt (Fintype.card ι' : ℝ) := by
  have h := reinstall_le m H A A' hA hA' hN' hC hC' hC'1 θ κ
  unfold RectangularRidgeCovarianceCalculus.ownerPotential at h
  unfold certificate
  change (_ - _ - _) - (_ - _ - _) ≤ _
  convert h using 1
  ring

end MatrixSpencer.RectangularRidgeCertificate
