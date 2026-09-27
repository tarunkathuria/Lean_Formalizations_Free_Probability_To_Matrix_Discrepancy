import MatrixSpencer.MSManuscriptPolynomialQueryMagnitude

/-! Uniform magnitudes and Jacobi cutoffs for the actual supported response
queries. The generic value-accuracy bridge also applies to the named convex
variant; the original numerical evaluator is instantiated explicitly below.
-/
open Matrix Set
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section
namespace MatrixSpencer.MSManuscriptPolynomialQueryResponse
open MSManuscriptSupportedGamma MSManuscriptSupportedOwner
  MSManuscriptPolynomialQueryCurvature MSManuscriptPolynomialQueryParameters
  MSManuscriptPolynomialQueryMagnitude MSManuscriptGammaDifference
local instance {m : Type*} [Fintype m] [DecidableEq m] :
    CStarAlgebra (Matrix m m ℂ) := {}
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096
attribute [local irreducible] ownerPotential KSNumericalOwnerPotential.report

variable {m N d : ℕ} (P : Parameters m d) (hP : P.Valid) (hm : m ≤ N)
  (hθ : P.regularizer = 1) (hδ : P.floor = 1/8192)
  (ht : P.threshold = 4096/Real.sqrt (m:ℝ))
  (hR : P.centerCap ≤ center N d)
  (O : Owner m) (hO : O.Valid P.floor) (hO1 : O.physical ≤ 1)
  (hOm : O.dim ≤ m) (hk : 0 < O.dim)

abbrev curvatureCap := MSManuscriptGammaInputBoundScaled.secondCap O.dim d
  P.centerCap P.regularizer P.floor m
abbrev precision := MSManuscriptGammaMatrix.topPrecision O.dim P.threshold
abbrev spacing := stepSize P.floor (curvatureCap P O) (precision P O)
abbrev tolerance := valueTolerance P.floor (curvatureCap P O) (precision P O)

include hP in
theorem curvature_nonneg : 0 ≤ curvatureCap P O :=
  MSManuscriptGammaInputBoundScaled.secondCap_nonneg
    ((norm_nonneg _).trans hP.2.2.2.2.2.2) hP.2.2.1

include hP hk in
theorem spacing_pos : 0 < spacing P O :=
  stepSize_pos hP.2.2.2.1 (curvature_nonneg P hP O)
    (MSManuscriptGammaMatrix.topPrecision_pos hk hP.2.2.2.2.2.1)

include hP hk in
theorem tolerance_pos : 0 < tolerance P O :=
  valueTolerance_pos hP.2.2.2.1 (curvature_nonneg P hP O)
    (MSManuscriptGammaMatrix.topPrecision_pos hk hP.2.2.2.2.2.1)

include hP hδ ht hOm hk in
theorem tolerance_le_one : tolerance P O ≤ 1 := by
  have hm0 : 0 < m := hk.trans_le hOm
  have hsqrt : 1 ≤ Real.sqrt (m:ℝ) := by
    simpa using Real.sqrt_le_sqrt (show (1:ℝ) ≤ m by exact_mod_cast hm0)
  have hthreshold : P.threshold ≤ 4096 := by
    rw [ht]
    apply (div_le_iff₀ (lt_of_lt_of_le zero_lt_one hsqrt)).mpr
    linarith
  have heta : precision P O ≤ 32 := by
    have hk' : (1:ℝ) ≤ O.dim := by exact_mod_cast hk
    change P.threshold/(128*(O.dim:ℝ)) ≤ 32
    apply (div_le_iff₀ (by positivity : (0:ℝ)<128*O.dim)).mpr
    linarith
  have heta0 := (MSManuscriptGammaMatrix.topPrecision_pos hk hP.2.2.2.2.2.1).le
  have hs : spacing P O ≤ (1/8192)/4 := by
    change min (P.floor/4) _ ≤ _
    rw [hδ]
    exact min_le_left _ _
  have hm := mul_le_mul heta hs (spacing_pos P hP O hk).le (by norm_num : (0:ℝ)≤32)
  change precision P O*spacing P O/4 ≤ 1
  norm_num at hm
  linarith

include hP hm hθ hδ ht hR hOm hk in
theorem spacing_inverse_le : (spacing P O)⁻¹ ≤ slopeStepInv N d := by
  have hR0 := (norm_nonneg _).trans hP.2.2.2.2.2.2
  have hL := MSManuscriptPolynomialQueryCurvature.secondCap_le (hOm.trans hm) hm
    P.physicalDimension_pos hR0 hR
  have hti : P.threshold⁻¹ ≤ thresholdInv N := by rw [ht]; exact threshold_inverse_le hm
  have heta := topPrecision_inverse_le (hOm.trans hm) hP.2.2.2.2.2.1 hti
  have hη := MSManuscriptGammaMatrix.topPrecision_pos hk hP.2.2.2.2.2.1
  change (stepSize P.floor (curvatureCap P O) (precision P O))⁻¹ ≤ _
  rw [hδ]
  apply slopeStep_inverse_le (curvature_nonneg P hP O) hη ?_ heta
  simpa only [curvatureCap, hθ, hδ] using hL

include hP hm hθ hR hO hO1 hOm hk in
theorem query_potential_abs (u : EuclideanSpace ℝ (Fin O.dim)) (hu : ‖u‖=1) :
    |ownerPotential P.center (family P O) O.matrix P.regularizer| ≤ potentialCap N d ∧
    |ownerPotential P.center (family P O)
      (O.matrix-spacing P O • realRankOne (WithLp.ofLp u)) P.regularizer| ≤ potentialCap N d := by
  letI : Nonempty (Fin d) := Fin.pos_iff_nonempty.mp P.physicalDimension_pos
  have hA := family_isHermitian P hP O
  have hAn : ∀ i, ‖family P O i‖ ≤ N := fun i =>
    (MSManuscriptFrameFamily.stored_family_norm_le P.atoms hP.2.1 O hO i).trans (Nat.cast_le.mpr hm)
  have hC := hO.matrix_posSemidef O hP.2.2.2.1.le
  have hC1 := MSManuscriptFrameFamily.stored_matrix_le_one O hO hO1
  have hs0 := spacing_pos P hP O hk
  have hsδ : spacing P O < P.floor :=
    (min_le_left _ _).trans_lt (by linarith [hP.2.2.2.1] : P.floor/4<P.floor)
  have hCs := MSManuscriptGammaSmoothness.query_posDef hO.2 hs0.le hsδ u hu
  have hCs1 : O.matrix-spacing P O • realRankOne (WithLp.ofLp u) ≤ 1 :=
    (sub_le_self O.matrix ((realRankOne_posSemidef (WithLp.ofLp u)).smul hs0.le).nonneg).trans hC1
  rw [hθ]
  exact ⟨owner_abs_le _ P.center.property _ hA hAn hC hC1 (hOm.trans hm)
      (hP.2.2.2.2.2.2.trans hR),
    owner_abs_le _ P.center.property _ hA hAn hCs.posSemidef hCs1 (hOm.trans hm)
      (hP.2.2.2.2.2.2.trans hR)⟩

/- Both query magnitudes follow from value accuracy on PSD inputs; no
bounded-report hypothesis remains for either actual response implementation. -/
include hP hm hθ hδ ht hR hO hO1 hOm hk in
theorem reported_slope_abs (r : Matrix (Fin O.dim) (Fin O.dim) ℝ → ℝ)
    (hr : ∀ C, C.PosSemidef →
      |r C-ownerPotential P.center (family P O) C P.regularizer| ≤ tolerance P O)
    (u : EuclideanSpace ℝ (Fin O.dim)) (hu : ‖u‖=1) :
    |(r O.matrix-r (O.matrix-spacing P O • realRankOne (WithLp.ofLp u)))/spacing P O| ≤
      2*((potentialCap N d:ℝ)+1)*slopeStepInv N d := by
  have hs := spacing_pos P hP O hk
  have hC := hO.matrix_posSemidef O hP.2.2.2.1.le
  have hsδ : spacing P O < P.floor :=
    (min_le_left _ _).trans_lt (by linarith [hP.2.2.2.1] : P.floor/4<P.floor)
  have hCs := (MSManuscriptGammaSmoothness.query_posDef hO.2 hs.le hsδ u hu).posSemidef
  have hv := query_potential_abs P hP hm hθ hR O hO hO1 hOm hk u hu
  have ht1 := tolerance_le_one P hP hδ ht O hOm hk
  have h0 := (abs_report_le (hr O.matrix hC) hv.1).trans (add_le_add_left ht1 _)
  have h1 := (abs_report_le (hr _ hCs) hv.2).trans (add_le_add_left ht1 _)
  exact (slope_abs_le h0 h1 hs).trans (mul_le_mul_of_nonneg_left
    (spacing_inverse_le P hP hm hθ hδ ht hR O hOm hk) (by positivity))

include hP hm hθ hδ ht hR hO hO1 hOm hk in
theorem reported_entries (r : Matrix (Fin O.dim) (Fin O.dim) ℝ → ℝ)
    (hr : ∀ C, C.PosSemidef →
      |r C-ownerPotential P.center (family P O) C P.regularizer| ≤ tolerance P O) :
    ∀ i j, |MSManuscriptGammaMatrix.reconstruct
      (fun u => (r O.matrix-r (O.matrix-spacing P O • realRankOne (WithLp.ofLp u)))/spacing P O) i j| ≤
      responseEntry N d :=
  reconstruct_entries _ (reported_slope_abs P hP hm hθ hδ ht hR O hO hO1 hOm hk r hr)

include hP hm hθ hδ ht hR hO hO1 hOm hk in
theorem original_response_entries : ∀ i j, |response P O i j| ≤ responseEntry N d := by
  letI : Nonempty (Fin d) := Fin.pos_iff_nonempty.mp P.physicalDimension_pos
  have hr : ∀ C, C.PosSemidef →
      |KSNumericalOwnerPotential.report P.center (family P O) C P.regularizer
        P.physicalDimension_pos (tolerance P O)-
        ownerPotential P.center (family P O) C P.regularizer| ≤ tolerance P O := by
    intro C hC
    exact KSNumericalOwnerPotential.report_accuracy _ P.center.property _
      (family_isHermitian P hP O) hC hP.2.2.1 (tolerance_pos P hP O hk) P.physicalDimension_pos
  have he := reported_entries P hP hm hθ hδ ht hR O hO hO1 hOm hk _ hr
  have hprobe : probe P.center (family P O) O.matrix P.regularizer P.physicalDimension_pos
      (spacing P O) (tolerance P O) =
      (fun u => (KSNumericalOwnerPotential.report P.center (family P O) O.matrix P.regularizer
        P.physicalDimension_pos (tolerance P O)-
        KSNumericalOwnerPotential.report P.center (family P O)
          (O.matrix-spacing P O • realRankOne (WithLp.ofLp u)) P.regularizer
          P.physicalDimension_pos (tolerance P O))/spacing P O) := by
    funext u
    simp only [probe, negativeSlope, valueCurve, zero_smul, sub_zero]
  change ∀ i j, |MSManuscriptGammaMatrix.reconstruct
    (probe P.center (family P O) O.matrix P.regularizer P.physicalDimension_pos
      (spacing P O) (tolerance P O)) i j| ≤ responseEntry N d
  rw [hprobe]
  exact he

include hP hm hθ hδ ht hR hO hO1 hOm hk in
theorem original_iterationCount_le :
    KSJacobiIteration.iterationCount (-(response P O)) (P.threshold/64) ≤ responseJacobi N d := by
  apply response_iterationCount_le _ (hOm.trans hm)
    (original_response_entries P hP hm hθ hδ ht hR O hO hO1 hOm hk) hP.2.2.2.2.2.1
  rw [ht]
  exact threshold_inverse_le hm

end MatrixSpencer.MSManuscriptPolynomialQueryResponse
