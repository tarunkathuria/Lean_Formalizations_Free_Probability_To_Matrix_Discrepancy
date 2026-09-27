import MatrixSpencer.KSDebitHessian
import MatrixSpencer.KSDebitFullRetirement
import MatrixSpencer.KSSpinLiveSource

/-!
# Full-label rejected queries force actual curvature on the live face

Full and live potentials are related by the existing exact source restriction.
The curvature frame is used directly in the debit-assisted retirement theorem;
no equality between independently chosen transport frames is assumed. Zero
live vectors are ruled out by their actual nonincreasing endpoint queries.
-/

open Matrix Filter Topology Set
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section
namespace MatrixSpencer.KSDebitLiveHessian

open KSPotentialModels KSLiveCurve KSDebitActualRetirement

variable {N : ℕ} {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
local instance {k : Type*} [Fintype k] [DecidableEq k] : CStarAlgebra (Matrix k k ℂ) := {}

/-- A zero vector can always be retired; no bound on its endpoint step is
needed because its signed atom and additional physical debit are both zero. -/
theorem queriedValue_le_of_vector_zero
    (M : Matrix (n ⊕ n) (n ⊕ n) ℂ) (v : Fin N → n → ℂ)
    (c : Fin N → ℝ) (hc : ∀ i, 0 ≤ c i) (θ : ℝ)
    (i : Fin N) (t δ : ℝ) (hz : v i = 0) :
    queriedValue M v c θ i t δ ≤ value M v c θ := by
  have hcov := KSEndpointRetirement.spin_covariance_delete_le c hc i
  have hm := ownerPotential_mono_covariance M
    (KSSpinSource.family (fun j => KSRankOne.atom (v j)))
    (KSSpinSource.family_isHermitian _ (fun j => KSRankOne.atom_isHermitian (v j)))
    (KSSpinSource.coefficientCovariance_posSemidef
      (KSEndpointRetirement.update_zero_nonneg hc i))
    (KSSpinSource.coefficientCovariance_posSemidef hc) hcov θ
  have hcenter : M + t • signedLift (KSRankOne.atom (v i)) -
      δ • KSSpinSource.doubled (KSRankOne.atom (v i)) = M := by
    simp [hz, KSRankOne.atom_zero, signedLift, KSSpinSource.doubled]
  simpa only [queriedValue, value, KSSpinLocalState.atoms, hcenter] using hm

/-- The no-safe transport hypotheses are derived internally from rejected
queries of the full original family. A nonempty live face then has a nonzero
critical direction of strictly negative actual second derivative. -/
theorem exists_live_negative_second_of_full_rejection
    (M : Matrix (n ⊕ n) (n ⊕ n) ℂ) (hMherm : M.IsHermitian)
    (hJM : Commute KSSignSymmetry.signMatrix M)
    (v : Fin N → n → ℂ) {x : Fin N → ℝ} (hx : x ∈ ksCube 1)
    [Nonempty (Live 1 x)] {θ δ : ℝ} (hθ : 0 < θ) (hδ : 0 ≤ δ)
    (hreject : ∀ i : Live 1 x,
      value M v (naturalOwners 64 x) θ <
        queriedValue M v (naturalOwners 64 x) θ i (nearestSign (x i) - x i) δ) :
    ∃ h : Live 1 x → ℝ, h ≠ 0 ∧
      deriv (KSDebitLocalState.curvePotential M (fun i : Live 1 x => v i) θ
        (fun i : Live 1 x => x i) h) 0 = 0 ∧
      iteratedDeriv 2 (KSDebitLocalState.curvePotential M (fun i : Live 1 x => v i) θ
        (fun i : Live 1 x => x i) h) 0 < 0 := by
  let A := fun i => KSRankOne.atom (v i)
  let vl : Live 1 x → n → ℂ := fun i => v i
  let xl : Live 1 x → ℝ := fun i => x i
  let c := naturalOwners 64 x
  let cl : Live 1 x → ℝ := fun i => 64 * (1 - xl i ^ 2)
  have hA : ∀ i, (A i).IsHermitian := fun i => KSRankOne.atom_isHermitian _
  have hc : ∀ i, 0 ≤ c i := naturalOwners_nonneg (by norm_num) le_rfl hx
  have hxl : ∀ i : Live 1 x, |xl i| < 1 := fun i => i.property
  have hcl : ∀ i, 0 < cl i := KSSpinLocalState.owners_pos hxl
  have hvl : ∀ i, vl i ≠ 0 := by
    intro i hz
    have hs := queriedValue_le_of_vector_zero M v c hc θ i
      (nearestSign (x i) - x i) δ hz
    exact (not_lt_of_ge hs) (hreject i)
  obtain ⟨S, hSmem, hS, _, hmax⟩ := exists_ownerOptimizer M (KSSpinSource.family A)
    (KSSpinSource.family_isHermitian A hA) (KSSpinSource.coefficientCovariance_posSemidef hc) hθ
  let Sh : selfAdjoint (Matrix (n ⊕ n) (n ⊕ n) ℂ) := ⟨S, hS.isHermitian⟩
  have hobjective (T : Matrix (n ⊕ n) (n ⊕ n) ℂ) :
      ownerObjective M (KSSpinSource.family A) (KSSpinSource.coefficientCovariance c) θ T =
      ownerObjective M (KSSpinSource.family (KSSpinLocalState.atoms vl))
        (KSSpinSource.coefficientCovariance cl) θ T :=
    KSSpinLiveSource.objective_restrict v 1 x c (naturalOwner_dead hx 64) M θ T
  have hmaxl : ∀ T ∈ densitySet,
      ownerObjective M (KSSpinSource.family (KSSpinLocalState.atoms vl))
        (KSSpinSource.coefficientCovariance cl) θ T ≤
      ownerObjective M (KSSpinSource.family (KSSpinLocalState.atoms vl))
        (KSSpinSource.coefficientCovariance cl) θ S := by
    intro T hT
    rw [← hobjective T, ← hobjective S]
    exact hmax T hT
  let V := KSSpinCompression.embedding (KSSpinLocalState.atoms vl)
  let Z := KSSpinLocalState.stateTransport vl xl S
  have hV : Vᴴ * V = 1 := KSSpinCompression.embedding_isometry _
  have hS0 := KSSupportSymmetry.compress_posDef V hV hS
  have hM := KSSpinCompression.compressed_source_posDef vl hcl hS
  have hZ : Z.PosDef := transportOptimizer_posDef hS0 hM
  have hsolve := transportOptimizer_solve hS0 hM
  have he (T : Matrix (n ⊕ n) (n ⊕ n) ℂ) :
      covarianceSource (KSSpinSource.family A) (KSSpinSource.coefficientCovariance c) T =
      covarianceSource (KSSpinSource.family (KSSpinLocalState.atoms vl))
        (KSSpinSource.coefficientCovariance cl) T :=
    KSSpinLiveSource.source_at_state v hx T
  have hmaxd : ∀ T ∈ densitySet,
      densityObjective M
        (covarianceKraus (KSSpinSource.family A) (KSSpinSource.coefficientCovariance c)) θ T ≤
      densityObjective M
        (covarianceKraus (KSSpinSource.family A) (KSSpinSource.coefficientCovariance c)) θ Sh := by
    intro T hT
    rw [← ownerObjective_eq_densityObjective _ _ (KSSpinSource.family_isHermitian A hA)
      (KSSpinSource.coefficientCovariance_posSemidef hc),
      ← ownerObjective_eq_densityObjective _ _ (KSSpinSource.family_isHermitian A hA)
      (KSSpinSource.coefficientCovariance_posSemidef hc)]
    exact hmax T hT
  have hfail : ∀ i : Live 1 x, cl i * realTrace (Z * KSSpinCompression.compressedAtom
      (KSSpinLocalState.atoms vl) i) < 1 - |xl i| := by
    intro i
    have hf : c i * realTrace (KSSpinSource.doubled (KSRankOne.atom (v i)) * (V * Z * Vᴴ)) + δ <
        1 - |x i| := by
      apply KSDebitRetirement.rejected_nearest_retirement_gap M v c hc V hV hθ Sh hS hSmem.2 hmaxd hZ
        (by change (Vᴴ * covarianceSource (KSSpinSource.family A) _ S * V).PosDef
            rw [he S]; exact hM)
        (by change Z * (Vᴴ * covarianceSource (KSSpinSource.family A) _ S * V) * Z = Vᴴ * S * V
            rw [he S]; exact hsolve)
        (by intro T hT; change V * (Vᴴ * covarianceSource (KSSpinSource.family A) _ T * V) * Vᴴ = _
            rw [he T]; exact KSSpinCompression.source_reconstruct vl cl T)
        i (x i) δ ⟨hx.1 i, hx.2 i⟩
      exact hreject i
    have hf' : c i * realTrace (KSSpinSource.doubled (KSRankOne.atom (v i)) * (V * Z * Vᴴ)) <
        1 - |x i| := by linarith
    change cl i * realTrace (KSSpinSource.doubled (KSRankOne.atom (vl i)) * (V * Z * Vᴴ)) < _ at hf'
    have hp : realTrace (KSSpinSource.doubled (KSRankOne.atom (vl i)) * (V * Z * Vᴴ)) =
        realTrace (KSSpinCompression.compressedAtom (KSSpinLocalState.atoms vl) i * Z) :=
      KSSpinCompression.transport_probe (KSSpinLocalState.atoms vl) Z i
    rw [hp, realTrace_mul_comm] at hf'
    exact hf'
  exact KSDebitHessian.exists_negative_second_curve M hMherm hJM
    vl hvl xl hxl hθ S hS hSmem.2 hmaxl hfail

/-- The genuine full original-label potential along a fixed live face. The
center increment uses the original label extension, and frozen owners remain
zero along this path. The initial center may already contain a fixed debit. -/
def fullCurvePotential (M : Matrix (n ⊕ n) (n ⊕ n) ℂ)
    (v : Fin N → n → ℂ) (θ : ℝ) (x : Fin N → ℝ)
    (h : Live 1 x → ℝ) (t : ℝ) : ℝ :=
  value (M + t • (∑ i, extend 1 x h i • signedLift (KSRankOne.atom (v i))))
    v (naturalOwners 64 (path 1 x h t)) θ

omit [Nonempty n] in
/-- Exact source restriction identifies the full-label path potential with
the actual live curve used in the negative-curvature theorem. -/
theorem fullCurvePotential_eq
    (M : Matrix (n ⊕ n) (n ⊕ n) ℂ) (v : Fin N → n → ℂ)
    (θ : ℝ) {x : Fin N → ℝ} (hx : x ∈ ksCube 1) (h : Live 1 x → ℝ) (t : ℝ) :
    fullCurvePotential M v θ x h t =
      KSDebitLocalState.curvePotential M (fun i : Live 1 x => v i) θ
        (fun i : Live 1 x => x i) h t := by
  unfold fullCurvePotential value KSSpinLocalState.atoms
  rw [sum_extend_smul]
  have hzero : ∀ i, ¬ |x i| < 1 → naturalOwners 64 (path 1 x h t) i = 0 := by
    intro i hi
    change 64 * (1 - (path 1 x h t i) ^ 2) = 0
    rw [path_dead 1 x h t i hi]
    exact naturalOwner_dead hx 64 i hi
  rw [KSSpinLiveSource.potential_restrict v 1 x (naturalOwners 64 (path 1 x h t)) hzero]
  unfold KSDebitLocalState.curvePotential KSDebitLocalState.curveCenter
  congr 2
  funext i
  simp only [naturalOwners, path_live, KSSpinLocalState.ownerCurve]

/-- Full original-label endpoint rejection implies actual negative curvature
of the full original-label potential along a nonzero live-face direction. -/
theorem exists_negative_second_of_full_rejection
    (M : Matrix (n ⊕ n) (n ⊕ n) ℂ) (hMherm : M.IsHermitian)
    (hJM : Commute KSSignSymmetry.signMatrix M)
    (v : Fin N → n → ℂ) {x : Fin N → ℝ} (hx : x ∈ ksCube 1)
    [Nonempty (Live 1 x)] {θ δ : ℝ} (hθ : 0 < θ) (hδ : 0 ≤ δ)
    (hreject : ∀ i : Live 1 x,
      value M v (naturalOwners 64 x) θ <
        queriedValue M v (naturalOwners 64 x) θ i (nearestSign (x i) - x i) δ) :
    ∃ h : Live 1 x → ℝ, h ≠ 0 ∧ extend 1 x h ≠ 0 ∧
      deriv (fullCurvePotential M v θ x h) 0 = 0 ∧
      iteratedDeriv 2 (fullCurvePotential M v θ x h) 0 < 0 := by
  obtain ⟨h, hh, hfirst, hsecond⟩ :=
    exists_live_negative_second_of_full_rejection M hMherm hJM v hx hθ hδ hreject
  refine ⟨h, hh, extend_ne_zero 1 x hh, ?_⟩
  have heq : fullCurvePotential M v θ x h =
      KSDebitLocalState.curvePotential M (fun i : Live 1 x => v i) θ
        (fun i : Live 1 x => x i) h :=
    funext (fullCurvePotential_eq M v θ hx h)
  rw [heq]
  exact ⟨hfirst, hsecond⟩

/-- The actual debit center supplies Hermitian symmetry internally. Zero
live input vectors are handled by the rejection hypothesis, not excluded as
an extra input assumption. -/
theorem exists_negative_second_of_debit_rejection
    (H B : Matrix n n ℂ) (hH : H.IsHermitian) (hB : B.PosSemidef)
    (v : Fin N → n → ℂ) {x : Fin N → ℝ} (hx : x ∈ ksCube 1)
    [Nonempty (Live 1 x)] {θ δ : ℝ} (hθ : 0 < θ) (hδ : 0 ≤ δ)
    (hreject : ∀ i : Live 1 x,
      value (KSDebitCenter.center H B) v (naturalOwners 64 x) θ <
        queriedValue (KSDebitCenter.center H B) v (naturalOwners 64 x) θ i
          (nearestSign (x i) - x i) δ) :
    ∃ h : Live 1 x → ℝ, h ≠ 0 ∧ extend 1 x h ≠ 0 ∧
      deriv (fullCurvePotential (KSDebitCenter.center H B) v θ x h) 0 = 0 ∧
      iteratedDeriv 2 (fullCurvePotential (KSDebitCenter.center H B) v θ x h) 0 < 0 :=
  exists_negative_second_of_full_rejection (KSDebitCenter.center H B)
    (KSDebitCenter.center_isHermitian_of_posSemidef hH hB)
    (KSDebitCenter.signMatrix_commute_center H B) v hx hθ hδ hreject

end MatrixSpencer.KSDebitLiveHessian
