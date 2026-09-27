import MatrixSpencer.RectangularRidgeEpochAcceptanceData
import MatrixSpencer.KSObjectiveValueBound

/-! Every actual epoch endpoint lies in the numerical acceptance query ball.
The saved movement omits snaps; their actual tangent error is charged to the
proved rounding ledger. -/
open Matrix
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section
namespace MatrixSpencer.RectangularRidgeEpochEndpointBounds
open RectangularRidgeEpochInput RectangularRidgeEpochRun RectangularRidgeEpochMoments
open RectangularRidgeEpochAcceptanceData
variable {N d : ℕ} [Nonempty (Fin d)]
local instance ridgeEpochEndpointCStar : CStarAlgebra (Matrix (Fin d) (Fin d) ℂ) := {}
local instance ridgeEpochEndpointSpace : NormedSpace ℝ (selfAdjoint (Matrix (Fin d) (Fin d) ℂ)) := inferInstance
set_option maxHeartbeats 800000
attribute [local irreducible] run RectangularRidgePotential.optimizer RectangularRidgeCertificate.density
  RectangularRidgeCovarianceCalculus.ownerPotential regularizedOwnerPotential

theorem rounding_small (c : Config N d) (s : Certified c) : s.val.rounding ≤ 1 / 16384 := by
  have h := rounding_le c s
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by have := c.count_pos; omega)
  have hl : (live c : ℝ) ≤ N := by exact_mod_cast live_le c
  have hh := mul_le_mul_of_nonneg_left hl (margin_pos c).le
  have he : margin N * (N : ℝ) = 1 / 16384 := by unfold margin; field_simp
  rw [he] at hh
  exact h.trans hh

theorem centered_l1 (c : Config N d) (s : Certified c) : (∑ i, |s.val.centered i|) ≤ 3 * (N : ℝ) := by
  have hi (i : Fin N) : |s.val.centered i| ≤ 2 + |s.val.point i-c.start i-s.val.centered i| := by
    have ha := abs_add_le (s.val.point i-c.start i) (-(s.val.point i-c.start i-s.val.centered i))
    have hb := abs_sub (s.val.point i) (c.start i)
    have hs := s.property.1.regular.1 i
    have hx := c.start_regular.1 i
    rw [abs_neg] at ha
    have he : s.val.point i-c.start i+-(s.val.point i-c.start i-s.val.centered i)=s.val.centered i := by ring
    rw [he] at ha
    linarith
  have hh := Finset.sum_le_sum (fun i (_ : i∈Finset.univ) => hi i)
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hh
  have hcent := s.property.2.1
  change (∑ i, |s.val.point i-c.start i-s.val.centered i|) ≤ s.val.rounding at hcent
  have hn : (1 : ℝ) ≤ N := by exact_mod_cast c.count_pos
  linarith [rounding_small c s]

theorem movement_norm (c : Config N d) (s : Certified c) :
    ‖((endpoint c s).movement : Matrix (Fin d) (Fin d) ℂ)‖ ≤ 3 * (N : ℝ) := by
  change ‖ownerPhysicalIncrement c.atoms c.hermitian s.val.centered‖ ≤ _
  apply le_trans (norm_sum_le _ _)
  calc
    (∑ i, ‖s.val.centered i • hermitianMatrixFamily c.atoms c.hermitian i‖) ≤ ∑ i, |s.val.centered i| := by
      apply Finset.sum_le_sum
      intro i _
      rw [norm_smul, Real.norm_eq_abs]
      exact (mul_le_mul_of_nonneg_left (c.contractions i) (abs_nonneg _)).trans_eq (mul_one _)
    _ ≤ _ := centered_l1 c s

theorem displacement_norm (c : Config N d) (s : Certified c) :
    ‖((endpoint c s).center : Matrix (Fin d) (Fin d) ℂ) - (anchor c : Matrix (Fin d) (Fin d) ℂ)‖ ≤ 2 * (N : ℝ) := by
  exact (norm_sub_le _ _).trans ((add_le_add (center_norm_le c _ s.property.1.regular.1)
    (center_norm_le c _ c.start_regular.1)).trans_eq (by ring))

theorem frobenius_le (A : Matrix (Fin d) (Fin d) ℂ) (hd : 1 ≤ d) :
    Real.sqrt (realTrace (A*A)) ≤ (d : ℝ) * ‖A‖ := by
  have hh := (le_abs_self (realTrace (A*A))).trans (KSObjectiveValueBound.abs_realTrace_mul_le A A)
  simp only [Fintype.card_fin] at hh
  have hd' : (1 : ℝ) ≤ d := by exact_mod_cast hd
  apply Real.sqrt_le_iff.mpr
  constructor
  · positivity
  · nlinarith [sq_nonneg ‖A‖, mul_nonneg (show 0 ≤ (d : ℝ)*(d-1) by exact mul_nonneg (by linarith) (by linarith)) (sq_nonneg ‖A‖)]

theorem endpoint_valid (a : Fin d) (c : Config N d) (s : Certified c) :
    (endpoint c s).Valid (acceptanceConfig a c) := by
  have hd : 1 ≤ d := c.count_pos.trans c.rectangular
  have hn : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hdn : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hS : (d : ℝ) * N ≤ RectangularRidgeNumericalOptimizerFloor.size d N ^ 2 := by
    dsimp [RectangularRidgeNumericalOptimizerFloor.size]
    nlinarith [sq_nonneg ((d : ℝ)-(N : ℝ))]
  constructor
  · change Real.sqrt (realTrace (_*_)) ≤ 3 * RectangularRidgeNumericalOptimizerFloor.size d N ^ 2
    exact (frobenius_le _ hd).trans ((mul_le_mul_of_nonneg_left (displacement_norm c s) hdn).trans (by nlinarith))
  · change Real.sqrt (realTrace (_*_)) ≤ 3 * RectangularRidgeNumericalOptimizerFloor.size d N ^ 2
    exact (frobenius_le _ hd).trans ((mul_le_mul_of_nonneg_left (movement_norm c s) hdn).trans (by nlinarith))

theorem movement_coe (c : Config N d) (s : Certified c) :
    ((endpoint c s).movement : Matrix (Fin d) (Fin d) ℂ) = ∑ i, s.val.centered i • c.atoms i := by
  change (selfAdjoint (Matrix (Fin d) (Fin d) ℂ)).subtype
    (∑ i, s.val.centered i • hermitianMatrixFamily c.atoms c.hermitian i) = _
  rw [map_sum]
  rfl

theorem tangent_eq (a : Fin d) (c : Config N d) (s : Certified c) :
    RectangularRidgeSolverAcceptance.tangent (acceptanceConfig a c) (endpoint c s) = tangent c s.val := by
  change realTrace (RectangularRidgeCertificate.density (anchor c) (depth c) (theta c) (ridge c)*
    ((endpoint c s).movement : Matrix (Fin d) (Fin d) ℂ)) = _
  rw [movement_coe]
  simp only [Matrix.mul_sum, realTrace_sum, Matrix.mul_smul, realTrace_smul,
    tangent, RectangularRidgeEpochMoments.gradient, RectangularRidgeCertificate.gradient, dotProduct]
  apply Finset.sum_congr rfl
  intro i _
  exact mul_comm _ _

theorem rounding_tangent_le (a : Fin d) (c : Config N d) (s : Certified c) :
    |RectangularRidgeSolverAcceptance.roundingTangent (acceptanceConfig a c) (endpoint c s)| ≤ s.val.rounding := by
  let X : Matrix (Fin d) (Fin d) ℂ := ∑ i, (s.val.point i-c.start i-s.val.centered i) • c.atoms i
  have he : ((endpoint c s).center : Matrix (Fin d) (Fin d) ℂ) - (anchor c : Matrix (Fin d) (Fin d) ℂ) -
      ((endpoint c s).movement : Matrix (Fin d) (Fin d) ℂ) = X := by
    rw [movement_coe]
    simp only [endpoint, anchor, center, epochCenter_coe, ZeroMemClass.coe_zero, zero_add, X,
      sub_smul, Finset.sum_sub_distrib]
  have hX : X.IsHermitian := by
    change (∑ i, (s.val.point i-c.start i-s.val.centered i) • c.atoms i)ᴴ = _
    simp only [Matrix.conjTranspose_sum, Matrix.conjTranspose_smul, star_trivial, fun i => (c.hermitian i).eq]
    rfl
  have hn : ‖X‖ ≤ ∑ i, |s.val.point i-c.start i-s.val.centered i| := by
    apply (norm_sum_le _ _).trans
    apply Finset.sum_le_sum
    intro i _
    rw [norm_smul, Real.norm_eq_abs]
    exact (mul_le_mul_of_nonneg_left (c.contractions i) (abs_nonneg _)).trans_eq (mul_one _)
  change |realTrace (RectangularRidgeCertificate.density (anchor c : Matrix (Fin d) (Fin d) ℂ) (depth c) (theta c) (ridge c)*
    (((endpoint c s).center : Matrix (Fin d) (Fin d) ℂ)-(anchor c : Matrix (Fin d) (Fin d) ℂ)-((endpoint c s).movement : Matrix (Fin d) (Fin d) ℂ)))| ≤ s.val.rounding
  rw [he, realTrace_mul_comm]
  exact (abs_realTrace_mul_density_le_norm hX (RectangularRidgeCertificate.density_mem _ _ _ _)).trans
    (hn.trans s.property.2.1)

theorem rounding_budget (a : Fin d) (c : Config N d) (s : Certified c) :
    RectangularRidgeSolverAcceptance.roundingTangent (acceptanceConfig a c) (endpoint c s) ≤
      RectangularRidgeSolverAcceptance.scale (acceptanceConfig a c) / 100 := by
  have hs : (1 : ℝ) ≤ Real.sqrt (live c : ℝ) := Real.one_le_sqrt.mpr (by exact_mod_cast (show 1 ≤ live c by have := live_large c; omega))
  exact (le_abs_self _).trans ((rounding_tangent_le a c s).trans ((rounding_small c s).trans (by
    change (1 / 16384 : ℝ) ≤ Real.sqrt (live c : ℝ) / 100
    linarith)))

end MatrixSpencer.RectangularRidgeEpochEndpointBounds
