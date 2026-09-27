import MatrixSpencer.KSSafeRetirement

/-! Actual old-owner transport comparison, with automatic physical support control. -/

open Matrix
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator

noncomputable section
namespace MatrixSpencer.KSOwnerRetirement

variable {ι n m : Type*} [Fintype ι] [Fintype n] [Fintype m]
  [DecidableEq ι] [DecidableEq n] [DecidableEq m]

open KSSafeRetirement

theorem complex_mulVec_zero_of_le {A B : Matrix n n ℂ}
    (hA : A.PosSemidef) (hAB : A ≤ B) {x : n → ℂ} (hx : B *ᵥ x = 0) :
    A *ᵥ x = 0 := by
  have hq := (Matrix.le_iff.mp hAB).2 x
  simp only [Matrix.sub_mulVec, hx, zero_sub, dotProduct_neg, neg_nonneg] at hq
  exact (hA.dotProduct_mulVec_zero_iff x).mp (le_antisymm hq (hA.2 x))

theorem support_reconstruct_of_le (V : Matrix n m ℂ) (hV : Vᴴ * V = 1)
    (K : Matrix m m ℂ) {Q : Matrix n n ℂ} (hQ : Q.PosSemidef)
    (hle : Q ≤ V * K * Vᴴ) : V * (Vᴴ * Q * V) * Vᴴ = Q := by
  have hzero : V * K * Vᴴ * (1 - V * Vᴴ) = 0 := by
    rw [Matrix.mul_sub, Matrix.mul_one]
    have he : V * K * Vᴴ * (V * Vᴴ) = V * K * Vᴴ := by
      simp only [Matrix.mul_assoc, ← Matrix.mul_assoc Vᴴ V Vᴴ, hV, Matrix.one_mul]
    rw [he, sub_self]
  have hz : Q * (1 - V * Vᴴ) = 0 := by
    apply Matrix.ext_of_mulVec_single
    intro j
    rw [← Matrix.mulVec_mulVec, Matrix.zero_mulVec]
    apply complex_mulVec_zero_of_le hQ hle
    rw [Matrix.mulVec_mulVec, hzero, Matrix.zero_mulVec]
  have hr : Q * (V * Vᴴ) = Q := by
    have he : Q - Q * (V * Vᴴ) = 0 := by
      simpa only [Matrix.mul_sub, Matrix.mul_one] using hz
    exact (sub_eq_zero.mp he).symm
  have hl : (V * Vᴴ) * Q = Q := by
    have he := congrArg Matrix.conjTranspose hr
    simpa only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
      hQ.isHermitian.eq] using he
  calc
    _ = (V * Vᴴ) * Q * (V * Vᴴ) := by simp only [Matrix.mul_assoc]
    _ = Q := by rw [hl, hr]

theorem sourceAdjoint_covarianceKraus (A : ι → Matrix n n ℂ)
    (hA : ∀ i, (A i).IsHermitian) {C : Matrix ι ι ℝ} (hC : C.PosSemidef)
    (X : Matrix n n ℂ) :
    sourceAdjoint (covarianceKraus A C) X = covarianceSource A C X := by
  rw [covarianceSource_eq_kraus A hA hC]
  unfold sourceAdjoint krausChannel
  apply Finset.sum_congr rfl
  intro i _
  simp only [covarianceKraus, (mixedKraus_isHermitian A (CFC.sqrt C) hA i).eq]

/-- The actual optimizing full density, as a Hermitian matrix. -/
def actualDensity [Nonempty n] (H : Matrix n n ℂ) (A : ι → Matrix n n ℂ)
    (C : Matrix ι ι ℝ) (θ : ℝ) : selfAdjoint (Matrix n n ℂ) :=
  hermitianDensityOptimizer H (covarianceKraus A C) θ

/-- The actual old physical-support transport, extended by zero. -/
def transportMatrix [Nonempty n] (H : Matrix n n ℂ) (A : ι → Matrix n n ℂ)
    (C : Matrix ι ι ℝ) (θ : ℝ) : Matrix n n ℂ :=
  let B := covarianceKraus A C
  let V := krausSupportEmbedding B
  V * actualSupportTransport B (actualDensity H A C θ) * Vᴴ

theorem transportMatrix_posSemidef [Nonempty n] (H : Matrix n n ℂ)
    (A : ι → Matrix n n ℂ) (C : Matrix ι ι ℝ) {θ : ℝ} (hθ : 0 < θ) :
    (transportMatrix H A C θ).PosSemidef :=
  (actualSupportTransport_posDef (covarianceKraus A C)
    (hermitianDensityOptimizer_posDef H (covarianceKraus A C) hθ)).posSemidef.mul_mul_conjTranspose_same _

/-- Decreasing an owner while paying the center displacement by its old
transport decreases the actual optimized potential. Every density and
transport in the test is constructed from the old state itself. -/
theorem owner_retire_of_matrix_le [Nonempty n]
    (H Hnew : Matrix n n ℂ) (A : ι → Matrix n n ℂ)
    (hA : ∀ i, (A i).IsHermitian) {C Cnew : Matrix ι ι ℝ}
    (hC : C.PosSemidef) (hCnew : Cnew.PosSemidef) (hdel : Cnew ≤ C)
    {θ : ℝ} (hθ : 0 < θ)
    (hmove : Hnew + covarianceSource A Cnew (transportMatrix H A C θ) ≤
      H + covarianceSource A C (transportMatrix H A C θ)) :
    ownerPotential Hnew A Cnew θ ≤ ownerPotential H A C θ := by
  let B := covarianceKraus A C
  let Bnew := covarianceKraus A Cnew
  let S := actualDensity H A C θ
  let V := krausSupportEmbedding B
  let Z := actualSupportTransport B S
  have hS : (S : Matrix n n ℂ).PosDef := hermitianDensityOptimizer_posDef H B hθ
  have ht : realTrace (S : Matrix n n ℂ) = 1 := hermitianDensityOptimizer_trace H B θ
  have hmax : ∀ T ∈ densitySet, densityObjective H B θ T ≤ densityObjective H B θ S :=
    densityOptimizer_isMaxOn H B θ
  rw [ownerPotential_eq_densityPotential Hnew A hA hCnew θ,
    ownerPotential_eq_densityPotential H A hA hC θ]
  apply retire_of_supported_matrix_le H Hnew B Bnew hθ S hS ht hmax
  · intro X hX
    have hdom : krausChannel Bnew X ≤ krausChannel B X := by
      rw [← covarianceSource_eq_kraus A hA hCnew, ← covarianceSource_eq_kraus A hA hC]
      exact covarianceSource_mono A hA hdel hX.1
    have hr := krausCompressedSource_reconstruct B hX.1
    exact support_reconstruct_of_le V (krausSupportEmbedding_isometry B)
      (krausCompressedSource B X) (krausChannel_posSemidef Bnew hX.1) (by rwa [hr])
  · change Hnew + (V * Z⁻¹ * Vᴴ + sourceAdjoint Bnew (V * Z * Vᴴ)) ≤
      H + (V * Z⁻¹ * Vᴴ + sourceAdjoint B (V * Z * Vᴴ))
    rw [sourceAdjoint_covarianceKraus A hA hCnew,
      sourceAdjoint_covarianceKraus A hA hC]
    have hm : Hnew + covarianceSource A Cnew (V * Z * Vᴴ) ≤
        H + covarianceSource A C (V * Z * Vᴴ) := hmove
    convert add_le_add_right hm (V * Z⁻¹ * Vᴴ) using 1 <;> abel

end MatrixSpencer.KSOwnerRetirement
