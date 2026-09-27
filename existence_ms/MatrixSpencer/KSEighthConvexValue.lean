import MatrixSpencer.KSConvexValueOracle
import MatrixSpencer.KSManuscriptReportMagnitudeBounds


open Matrix Set
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section
namespace MatrixSpencer.KSEighthConvexValue
open KSPotentialModels KSEighthHessianQueries KSEighthFacePotential
variable {N d : ℕ}

def nonnegativeOwners (c : Fin N → ℝ) : Fin N → ℝ := fun i => max 0 (c i)

theorem nonnegativeOwners_eq (c : Fin N → ℝ) (hc : ∀i,0≤c i) : nonnegativeOwners c=c := by
  funext i
  exact max_eq_right (hc i)

def ownerReport (O : KSConvexValueOracle.Solver) (v : Fin N → Fin d → ℂ)
    (θ : ℝ) (hd : 0<d) (c : Fin N → ℝ) (ν : ℝ) (x : Fin N → ℝ) : ℝ :=
  KSConvexValueOracle.reindexedOwnerReport O ⟨0,by omega⟩ (KSEighthNumericalValue.blockIndex d)
    (signedLift (center (fun i => KSRankOne.atom (v i)) x))
    (KSIndependentSource.family (fun i => KSRankOne.atom (v i)))
    (KSIndependentSource.family_isHermitian _ (fun i => KSRankOne.atom_isHermitian (v i)))
    (KSIndependentSource.coefficientCovariance (nonnegativeOwners c))
    (KSIndependentSource.coefficientCovariance_posSemidef (fun i => le_max_left _ _))
    (by omega) θ ν

theorem ownerReport_accuracy (O : KSConvexValueOracle.Solver) (v : Fin N → Fin d → ℂ)
    {θ ν : ℝ} (hθ : 0<θ) (hν : 0<ν) (hd : 0<d) (c : Fin N → ℝ)
    (hc : ∀i,0≤c i) (x : Fin N → ℝ) :
    |ownerReport O v θ hd c ν x-commonPotential (fun i => KSRankOne.atom (v i)) θ x c|≤ν := by
  letI : Nonempty (Fin d) := ⟨⟨0,hd⟩⟩
  have h := KSConvexValueOracle.reindexedOwnerReport_accuracy O ⟨0,by omega⟩
    (KSEighthNumericalValue.blockIndex d)
    (signedLift (center (fun i => KSRankOne.atom (v i)) x))
    (KSIndependentSource.family (fun i => KSRankOne.atom (v i)))
    (KSIndependentSource.family_isHermitian _ (fun i => KSRankOne.atom_isHermitian (v i)))
    (KSIndependentSource.coefficientCovariance (nonnegativeOwners c))
    (KSIndependentSource.coefficientCovariance_posSemidef (fun i => le_max_left _ _))
    (by omega) hθ hν
  change |ownerReport O v θ hd c ν x-ownerPotential _ _ _ θ|≤ν at h
  rw [nonnegativeOwners_eq c hc] at h
  rw [commonPotential,KSCommonSource.potential_eq_independent _ _
    (fun i => KSRankOne.atom_isHermitian (v i)) hc hθ]
  exact h

def stateReport (O : KSConvexValueOracle.Solver) (v : Fin N → Fin d → ℂ)
    (θ : ℝ) (hd : 0<d) (ν : ℝ) (x : Fin N → ℝ) : ℝ :=
  ownerReport O v θ hd (truncatedOwners (1/8) 64 x) ν x

def retainedReport (O : KSConvexValueOracle.Solver) (v : Fin N → Fin d → ℂ)
    (θ : ℝ) (hd : 0<d) (L : Finset (Fin N)) (ν : ℝ) (x : Fin N → ℝ) : ℝ :=
  ownerReport O v θ hd (maskedOwners 64 L x) ν x

theorem stateReport_accuracy (O : KSConvexValueOracle.Solver) (v : Fin N → Fin d → ℂ)
    {θ ν : ℝ} (hθ : 0<θ) (hν : 0<ν) (hd : 0<d)
    {x : Fin N → ℝ} (hx : x∈ksCube (1/8)) :
    |stateReport O v θ hd ν x-eighthPotential (fun i => KSRankOne.atom (v i)) θ x|≤ν :=
  ownerReport_accuracy O v hθ hν hd _
    (maskedOwners_nonneg (by norm_num) (by norm_num) hx (live (1/8) x)) x

theorem retainedReport_accuracy (O : KSConvexValueOracle.Solver) (v : Fin N → Fin d → ℂ)
    {θ ν a : ℝ} (hθ : 0<θ) (hν : 0<ν) (hd : 0<d) (L : Finset (Fin N))
    (ha : a≤1) {x : Fin N → ℝ} (hx : x∈ksCube a) :
    |retainedReport O v θ hd L ν x-commonPotential (fun i => KSRankOne.atom (v i)) θ x (maskedOwners 64 L x)|≤ν :=
  ownerReport_accuracy O v hθ hν hd _ (maskedOwners_nonneg (by norm_num) ha hx L) x

def faceReport (O : KSConvexValueOracle.Solver) (v : Fin N → Fin d → ℂ)
    (θ κ : ℝ) (hd : 0<d) (x : Fin N → ℝ) : Space x → ℝ :=
  fun z => retainedReport O v θ hd (live (1/8) x) (queryTolerance v θ κ x)
    (KSEighthLiveCoordinates.face x z)

theorem faceReport_accuracy (O : KSConvexValueOracle.Solver) (v : Fin N → Fin d → ℂ)
    {θ κ : ℝ} (hθ : 0<θ) (hκ : 0<κ) (hd : 0<d)
    {x : Fin N → ℝ} (hx : x∈ksCube (1/8)) (hlive : 0<KSEighthLiveEnumeration.count x)
    (z : Space x) (hz : ‖z‖≤1/16) :
    |faceReport O v θ κ hd x z-potential v θ x z|≤queryTolerance v θ κ x := by
  letI : Nonempty (Fin d) := ⟨⟨0,hd⟩⟩
  rw [potential_eq_retained v hθ x z (by norm_num : (1/4:ℝ)≤1) (query_ball_cube hx z hz)]
  exact retainedReport_accuracy O v hθ (queryTolerance_pos v hθ hκ hd x hlive) hd _
    (by norm_num) (query_ball_cube hx z hz)

theorem query_accuracy (O : KSConvexValueOracle.Solver) (v : Fin N → Fin d → ℂ)
    {θ κ : ℝ} (hθ : 0<θ) (hκ : 0<κ) (hd : 0<d)
    {x : Fin N → ℝ} (hx : x∈ksCube (1/8)) (hlive : 0<KSEighthLiveEnumeration.count x) :
    KSNumericalHessian.QueryAccuracy (potential v θ x) (faceReport O v θ κ hd x)
      0 (queryMesh v θ κ x) (queryTolerance v θ κ x) := by
  intro i j
  have hp := scaled_query_norm v hθ hκ hd x hlive _ (coordinate_add_norm i j)
  have hm := scaled_query_norm v hθ hκ hd x hlive _ (coordinate_sub_norm i j)
  have ha := faceReport_accuracy O v hθ hκ hd hx hlive
  refine ⟨?_,?_,?_,?_⟩
  · simpa only [zero_add] using ha _ hp
  · simpa only [zero_add] using ha _ hm
  · simpa only [zero_sub] using ha (-(queryMesh v θ κ x •
      (KSNumericalHessian.coordinate i-KSNumericalHessian.coordinate j))) (by rwa [norm_neg])
  · simpa only [zero_sub] using ha (-(queryMesh v θ κ x •
      (KSNumericalHessian.coordinate i+KSNumericalHessian.coordinate j))) (by rwa [norm_neg])

end MatrixSpencer.KSEighthConvexValue
