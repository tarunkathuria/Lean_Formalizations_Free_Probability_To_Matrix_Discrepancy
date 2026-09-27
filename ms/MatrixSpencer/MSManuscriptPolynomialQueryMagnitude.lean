import MatrixSpencer.MSManuscriptPolynomialQueryFactory
import MatrixSpencer.MSManuscriptPolynomialQueryCleanup

/-! Query-value and reconstructed response magnitudes from primitive input
bounds. The response estimates accept the proved value accuracy of either
the original evaluator or the explicit convex-solver implementation.
-/
open Matrix Set
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section
namespace MatrixSpencer.MSManuscriptPolynomialQueryMagnitude
open MSManuscriptPolynomialQueryCurvature MSManuscriptPolynomialQueryParameters
local instance {m : Type*} [Fintype m] [DecidableEq m] :
    CStarAlgebra (Matrix m m ℂ) := {}
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096

def potentialCap (N d : ℕ) : ℕ := center N d+2*N^2+2*(d+1)
def responseEntry (N d : ℕ) : ℕ := 4*(potentialCap N d+1)*slopeStepInv N d
def responseJacobi (N d : ℕ) : ℕ :=
  KSJacobiPolynomialBounds.jacobi N (responseEntry N d) (64*thresholdInv N)

theorem owner_abs_le {k N d : ℕ} [Nonempty (Fin d)]
    (H : Matrix (Fin d) (Fin d) ℂ) (hH : H.IsHermitian)
    (A : Fin k → Matrix (Fin d) (Fin d) ℂ) (hA : ∀ i, (A i).IsHermitian)
    (hAn : ∀ i, ‖A i‖ ≤ N) {C : Matrix (Fin k) (Fin k) ℝ}
    (hC : C.PosSemidef) (hC1 : C ≤ 1) (hk : k ≤ N)
    (hR : ‖H‖ ≤ center N d) :
    |ownerPotential H A C 1| ≤ potentialCap N d := by
  have hκ := MSManuscriptOptimizerFloorScaled.covariance_budget A hA
    (Nat.cast_nonneg N) hAn hC hC1
  have hsqrt : Real.sqrt ((k:ℝ)^2*(N:ℝ)^2) = (k:ℝ)*N := by
    rw [← mul_pow, Real.sqrt_sq (by positivity)]
  have hk' : (k:ℝ) ≤ N := Nat.cast_le.mpr hk
  have hd' := MSManuscriptPolynomialMovementBounds.sqrt_le_add_one (Nat.cast_nonneg d)
  have hupper : ownerPotential H A C 1 ≤ (center N d:ℝ)+2*(k:ℝ)*N+2*Real.sqrt (d:ℝ) := by
    rw [ownerPotential_eq_densityPotential H A hA hC]
    obtain ⟨S,hS,he⟩ := exists_densityPotential_eq H (covarianceKraus A C) 1
    rw [he]
    have hb := KSOptimizerFloor.objective_le_input_bound H hH _
      (by norm_num : (0:ℝ)≤1) hR hκ hS
    simpa only [Fintype.card_fin, hsqrt, mul_one, one_mul, mul_assoc] using hb
  have hlower : -(center N d:ℝ) ≤ ownerPotential H A C 1 := by
    rw [ownerPotential_eq_densityPotential H A hA hC]
    obtain ⟨S,hS,he⟩ := exists_densityPotential_eq H (covarianceKraus A C) 1
    rw [he]
    have hn := realTrace_mul_density_le_norm hH.neg hS
    simp only [Matrix.neg_mul, realTrace_neg, norm_neg] at hn
    have hf := fidelity_nonneg S (krausChannel (covarianceKraus A C) S)
    have hs := realTrace_nonneg (CFC.sqrt_nonneg S).posSemidef
    unfold densityObjective
    linarith
  have hkn := mul_le_mul_of_nonneg_right hk' (Nat.cast_nonneg N)
  rw [abs_le]
  simp only [potentialCap, Nat.cast_add, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, Nat.cast_one]
  constructor <;> nlinarith [sq_nonneg (N:ℝ), Nat.cast_nonneg (α:=ℝ) d]

theorem abs_report_le {r v V ν : ℝ} (hr : |r-v| ≤ ν) (hv : |v| ≤ V) : |r| ≤ V+ν := by
  have ht := abs_add_le (r-v) v
  rw [sub_add_cancel] at ht
  linarith

theorem slope_abs_le {a b V s : ℝ} (ha : |a| ≤ V) (hb : |b| ≤ V) (hs : 0 < s) :
    |(a-b)/s| ≤ 2*V*s⁻¹ := by
  rw [abs_div, abs_of_pos hs, div_eq_mul_inv]
  exact mul_le_mul_of_nonneg_right ((abs_sub a b).trans (by linarith)) (inv_nonneg.mpr hs.le)

theorem reconstruct_entries {k N d : ℕ} (q : EuclideanSpace ℝ (Fin k) → ℝ)
    (hq : ∀ u, ‖u‖=1 → |q u| ≤ 2*((potentialCap N d:ℝ)+1)*slopeStepInv N d) :
    ∀ i j, |MSManuscriptGammaMatrix.reconstruct q i j| ≤ responseEntry N d := by
  have he := MSManuscriptGammaMatrix.reconstruct_entry_error (0 : Matrix (Fin k) (Fin k) ℝ)
    (by simp [Matrix.IsSymm]) q (by positivity : (0:ℝ)≤2*((potentialCap N d:ℝ)+1)*slopeStepInv N d)
    (by simpa [KSRayleighAccuracy.realRayleigh] using hq)
  intro i j
  have h := he i j
  simp only [Matrix.zero_apply, zero_sub, abs_neg] at h
  convert h using 1 <;> simp only [responseEntry, Nat.cast_mul, Nat.cast_add,
    Nat.cast_ofNat, Nat.cast_one] <;> ring

theorem response_iterationCount_le {k N d : ℕ} (G : Matrix (Fin k) (Fin k) ℝ)
    (hk : k ≤ N) (hG : ∀ i j, |G i j| ≤ responseEntry N d) {t : ℝ}
    (ht : 0 < t) (hti : t⁻¹ ≤ thresholdInv N) :
    KSJacobiIteration.iterationCount (-G) (t/64) ≤ responseJacobi N d := by
  have hinv : (t/64)⁻¹ ≤ (64*thresholdInv N:ℕ) := by
    rw [inv_div, div_eq_mul_inv]
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using mul_le_mul_of_nonneg_left hti
      (by norm_num : (0:ℝ)≤64)
  exact KSJacobiPolynomialBounds.iterationCount_le _ hk
    (by simpa only [Matrix.neg_apply, abs_neg] using hG) (by positivity) hinv

theorem response_ceiling_input_le {k N d : ℕ} (G : Matrix (Fin k) (Fin k) ℝ)
    (hk : k ≤ N) (hG : ∀ i j, |G i j| ≤ responseEntry N d) {t : ℝ}
    (ht : 0 < t) (hti : t⁻¹ ≤ thresholdInv N) :
    KSJacobiIteration.denominator k*KSJacobiStep.offDiagonalEnergy (-G)/(t/64)^2 ≤
      (responseJacobi N d:ℝ) :=
  (Nat.le_ceil _).trans (Nat.cast_le.mpr (response_iterationCount_le G hk hG ht hti))

end MatrixSpencer.MSManuscriptPolynomialQueryMagnitude
