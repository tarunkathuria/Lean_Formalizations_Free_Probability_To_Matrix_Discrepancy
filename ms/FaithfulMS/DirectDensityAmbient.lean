import FaithfulMS.DirectDensity

/-!
# Computing the transport without choosing a source basis

The source-range projection is enough to evaluate the exact transport. Add
the identity on the source kernel to both compressed inputs, take the usual
full-dimensional transport, and compress it with the projection. This gives
the same matrix as choosing any orthonormal source frame. Thus the actual
report can use an EVD range projection and ambient matrix operations.
-/

open Matrix
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section
namespace FaithfulMS.DirectDensityAmbient
open MatrixSpencer
set_option maxHeartbeats 2000000
variable {n m : Type*} [Fintype n] [Fintype m] [DecidableEq n] [DecidableEq m]
local instance {j : Type*} [Fintype j] [DecidableEq j] : CStarAlgebra (Matrix j j ℂ) := {}

def complete (V : Matrix n m ℂ) (X : Matrix m m ℂ) : Matrix n n ℂ :=
  V * X * Vᴴ + (1 - V * Vᴴ)

theorem complement_square (V : Matrix n m ℂ) (hV : Vᴴ * V = 1) :
    (1 - V * Vᴴ) * (1 - V * Vᴴ) = 1 - V * Vᴴ := by
  have hp : (V * Vᴴ) * (V * Vᴴ) = V * Vᴴ := by
    calc
      _ = V * (Vᴴ * V) * Vᴴ := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [hV, Matrix.mul_one]
  noncomm_ring [hp]

theorem complement_posSemidef (V : Matrix n m ℂ) (hV : Vᴴ * V = 1) :
    (1 - V * Vᴴ).PosSemidef := by
  have hs : (1 - V * Vᴴ).IsHermitian := by
    have hp : (V * Vᴴ).PosSemidef := by
      simpa only [Matrix.conjTranspose_conjTranspose] using
        Matrix.posSemidef_conjTranspose_mul_self Vᴴ
    exact Matrix.isHermitian_one.sub hp.isHermitian
  have hg := Matrix.posSemidef_conjTranspose_mul_self (1 - V * Vᴴ)
  rw [hs.eq, complement_square V hV] at hg
  exact hg

theorem complete_posSemidef (V : Matrix n m ℂ) (hV : Vᴴ * V = 1)
    {X : Matrix m m ℂ} (hX : X.PosSemidef) : (complete V X).PosSemidef :=
  (hX.mul_mul_conjTranspose_same V).add (complement_posSemidef V hV)

theorem complete_one (V : Matrix n m ℂ) : complete V 1 = 1 := by
  simp only [complete, Matrix.mul_one, add_sub_cancel]

theorem complete_mul (V : Matrix n m ℂ) (hV : Vᴴ * V = 1)
    (X Y : Matrix m m ℂ) : complete V X * complete V Y = complete V (X * Y) := by
  have hxy : V * X * Vᴴ * (V * Y * Vᴴ) = V * (X * Y) * Vᴴ := by
    calc
      _ = V * X * (Vᴴ * V) * Y * Vᴴ := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [hV, Matrix.mul_one]; simp only [Matrix.mul_assoc]
  have hx : V * X * Vᴴ * (V * Vᴴ) = V * X * Vᴴ := by
    calc
      _ = V * X * (Vᴴ * V) * Vᴴ := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [hV, Matrix.mul_one]
  have hy : V * Vᴴ * (V * Y * Vᴴ) = V * Y * Vᴴ := by
    calc
      _ = V * (Vᴴ * V) * Y * Vᴴ := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [hV, Matrix.mul_one]
  have hp : (V * Vᴴ) * (V * Vᴴ) = V * Vᴴ := by
    calc
      _ = V * (Vᴴ * V) * Vᴴ := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [hV, Matrix.mul_one]
  unfold complete
  noncomm_ring [hxy, hx, hy, hp]

theorem complete_inv (V : Matrix n m ℂ) (hV : Vᴴ * V = 1)
    {X : Matrix m m ℂ} (hX : IsUnit X) : (complete V X)⁻¹ = complete V X⁻¹ := by
  letI : Invertible X := hX.invertible
  apply Matrix.inv_eq_right_inv
  rw [complete_mul V hV, Matrix.mul_inv_of_invertible, complete_one]

theorem complete_posDef (V : Matrix n m ℂ) (hV : Vᴴ * V = 1)
    {X : Matrix m m ℂ} (hX : X.PosDef) : (complete V X).PosDef := by
  apply (complete_posSemidef V hV hX.posSemidef).posDef_iff_isUnit.mpr
  letI : Invertible X := hX.isUnit.invertible
  have hm : complete V X * complete V X⁻¹ = 1 := by
    rw [complete_mul V hV, Matrix.mul_inv_of_invertible, complete_one]
  letI : Invertible (complete V X) := Matrix.invertibleOfRightInverse _ _ hm
  exact isUnit_of_invertible _

theorem complete_sqrt (V : Matrix n m ℂ) (hV : Vᴴ * V = 1)
    {X : Matrix m m ℂ} (hX : X.PosSemidef) :
    CFC.sqrt (complete V X) = complete V (CFC.sqrt X) := by
  apply CFC.sqrt_unique
  · rw [complete_mul V hV, CFC.sqrt_mul_sqrt_self X hX.nonneg]
  · exact (complete_posSemidef V hV (CFC.sqrt_nonneg X).posSemidef).nonneg

theorem complete_fidelityCore (V : Matrix n m ℂ) (hV : Vᴴ * V = 1)
    {S M : Matrix m m ℂ} (hS : S.PosSemidef) (hM : M.PosSemidef) :
    fidelityCore (complete V S) (complete V M) = complete V (fidelityCore S M) := by
  have hinner : (CFC.sqrt S * M * CFC.sqrt S).PosSemidef := by
    simpa only [(CFC.sqrt_nonneg S).posSemidef.isHermitian.eq] using
      hM.mul_mul_conjTranspose_same (CFC.sqrt S)
  simp only [fidelityCore, complete_sqrt V hV hS, complete_mul V hV]
  exact complete_sqrt V hV hinner

theorem complete_transport (V : Matrix n m ℂ) (hV : Vᴴ * V = 1)
    {S M : Matrix m m ℂ} (hS : S.PosDef) (hM : M.PosDef) :
    transportOptimizer (complete V S) (complete V M) = complete V (transportOptimizer S M) := by
  simp only [transportOptimizer, complete_sqrt V hV hS.posSemidef,
    complete_fidelityCore V hV hS.posSemidef hM.posSemidef,
    complete_inv V hV (fidelityCore_posDef hS hM).isUnit, complete_mul V hV]

theorem projection_complete_projection (V : Matrix n m ℂ) (hV : Vᴴ * V = 1)
    (X : Matrix m m ℂ) :
    (V * Vᴴ) * complete V X * (V * Vᴴ) = V * X * Vᴴ := by
  have hleft : (V * Vᴴ) * V = V := by
    rw [Matrix.mul_assoc, hV, Matrix.mul_one]
  have hright : Vᴴ * (V * Vᴴ) = Vᴴ := by
    rw [← Matrix.mul_assoc, hV, Matrix.one_mul]
  have hp : (V * Vᴴ) * (V * Vᴴ) = V * Vᴴ := by
    rw [← Matrix.mul_assoc, hleft]
  have hx : (V * Vᴴ) * (V * X * Vᴴ) * (V * Vᴴ) = V * X * Vᴴ := by
    calc
      _ = ((V * Vᴴ) * V) * X * (Vᴴ * (V * Vᴴ)) := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [hleft, hright]
  unfold complete
  rw [Matrix.mul_add, Matrix.add_mul, hx, Matrix.mul_sub, Matrix.mul_one, hp,
    sub_self, Matrix.zero_mul, add_zero]

def ambientTransport (P S M : Matrix n n ℂ) : Matrix n n ℂ :=
  P * transportOptimizer (P * S * P + (1 - P)) (M + (1 - P)) * P

theorem ambientTransport_eq_embedding (V : Matrix n m ℂ) (hV : Vᴴ * V = 1)
    {S : Matrix n n ℂ} (hS : S.PosDef) {M : Matrix m m ℂ} (hM : M.PosDef) :
    ambientTransport (V * Vᴴ) S (V * M * Vᴴ) =
      V * transportOptimizer (Vᴴ * S * V) M * Vᴴ := by
  have hc : (V * Vᴴ) * S * (V * Vᴴ) + (1 - V * Vᴴ) =
      complete V (Vᴴ * S * V) := by simp only [complete, Matrix.mul_assoc]
  unfold ambientTransport
  rw [hc]
  change (V * Vᴴ) * transportOptimizer (complete V (Vᴴ * S * V)) (complete V M) *
    (V * Vᴴ) = _
  rw [complete_transport V hV (posDef_isometry_compression V hV hS) hM,
    projection_complete_projection V hV]

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem completed_density_posDef (B : ι → Matrix n n ℂ)
    {S : Matrix n n ℂ} (hS : S.PosDef) :
    (krausSupportProjection B * S * krausSupportProjection B +
      (1 - krausSupportProjection B)).PosDef := by
  have h := complete_posDef (krausSupportEmbedding B) (krausSupportEmbedding_isometry B)
    (krausCompressedDensity_posDef B hS)
  simpa only [complete, krausCompressedDensity, krausSupportProjection, Matrix.mul_assoc] using h

theorem completed_source_posDef (B : ι → Matrix n n ℂ)
    {S : Matrix n n ℂ} (hS : S.PosDef) :
    (krausChannel B S + (1 - krausSupportProjection B)).PosDef := by
  have h := complete_posDef (krausSupportEmbedding B) (krausSupportEmbedding_isometry B)
    (krausCompressedSource_posDef B hS)
  simpa only [complete, krausCompressedSource_reconstruct B hS.posSemidef,
    krausSupportProjection] using h

/-- The report's supported transport has a basis-free ambient expression. -/
theorem actual_transport_ambient (A : ι → Matrix n n ℂ)
    (hA : ∀ i, (A i).IsHermitian) (C : Matrix ι ι ℝ)
    {S : Matrix n n ℂ} (hS : S.PosDef) :
    ambientTransport (krausSupportProjection (covarianceKraus A C)) S
      (krausChannel (covarianceKraus A C) S) =
    krausSupportEmbedding (covarianceKraus A C) *
      RectangularRidgeOwnerFrame.sourceTransport A C S *
      (krausSupportEmbedding (covarianceKraus A C))ᴴ := by
  rw [← krausCompressedSource_reconstruct (covarianceKraus A C) hS.posSemidef]
  change ambientTransport
    (krausSupportEmbedding (covarianceKraus A C) * (krausSupportEmbedding (covarianceKraus A C))ᴴ) S
    (krausSupportEmbedding (covarianceKraus A C) * krausCompressedSource (covarianceKraus A C) S *
      (krausSupportEmbedding (covarianceKraus A C))ᴴ) =
    krausSupportEmbedding (covarianceKraus A C) *
      transportOptimizer (krausCompressedDensity (covarianceKraus A C) S)
        (krausChannel (krausReducedFamily (covarianceKraus A C))
          (krausCompressedDensity (covarianceKraus A C) S)) *
        (krausSupportEmbedding (covarianceKraus A C))ᴴ
  rw [krausReducedFamily_channel (covarianceKraus A C) (covarianceKraus_isHermitian A hA C) S]
  exact ambientTransport_eq_embedding (krausSupportEmbedding (covarianceKraus A C))
    (krausSupportEmbedding_isometry (covarianceKraus A C)) hS
    (krausCompressedSource_posDef (covarianceKraus A C) hS)

theorem gamma_ambient (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).IsHermitian)
    {C : Matrix ι ι ℝ} (hC : C.PosSemidef) {S : Matrix n n ℂ} (hS : S.PosDef) :
    DirectDensity.gamma A C S = covarianceGram A S
      (ambientTransport (krausSupportProjection (covarianceKraus A C)) S
        (covarianceSource A C S)) := by
  rw [covarianceSource_eq_kraus A hA hC, actual_transport_ambient A hA C hS]
  rfl

end FaithfulMS.DirectDensityAmbient
