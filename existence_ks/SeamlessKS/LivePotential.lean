import SeamlessKS.StatePotential
import SeamlessKS.SmoothPotential
import SeamlessKS.NormalizedHessian
import MatrixSpencer.KSFullManuscriptLiveCoordinates
import MatrixSpencer.KSSpinLiveSource

/-! Exact restriction of the actual smooth potential to its current live face. -/
open Matrix Filter Topology Set
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator ContDiff
noncomputable section
namespace SeamlessKS.LivePotential
open MatrixSpencer SeamlessKS.State SeamlessKS.StatePotential
open MatrixSpencer.KSLiveEnumeration (count liveEquiv)
open MatrixSpencer.KSFullManuscriptLiveCoordinates (face)

variable {N : ℕ} {ρ : ℝ} {n : Type*} [Fintype n] [DecidableEq n]
local instance {k : Type*} [Fintype k] [DecidableEq k] : CStarAlgebra (Matrix k k ℂ) := {}

def liveVectors (v : Fin N → n → ℂ) (x : Fin N → ℝ) : Fin (count x) → n → ℂ :=
  fun i => v (liveEquiv x i)

def livePositions (x : Fin N → ℝ) : Fin (count x) → ℝ := fun i => x (liveEquiv x i)

theorem livePositions_interior (x : Fin N → ℝ) (i : Fin (count x)) :
    |livePositions x i| < 1 := (liveEquiv x i).property

theorem weights_dead (ζ : ℝ) {x : Fin N → ℝ} (hx : x ∈ ksCube 1)
    (i : Fin N) (hi : ¬ |x i| < 1) : SourceTransport.smoothWeights ζ x i = 0 := by
  have ha : |x i| = 1 := le_antisymm (abs_le.mpr ⟨hx.1 i, hx.2 i⟩) (not_lt.mp hi)
  have hs : x i ^ 2 = 1 := by nlinarith [sq_abs (x i)]
  simp [SourceTransport.smoothWeights, Source.weight, hs]

theorem source_restrict_fin (v : Fin N → n → ℂ) (x c : Fin N → ℝ)
    (hzero : ∀ i, ¬ |x i| < 1 → c i = 0)
    (X : Matrix (n ⊕ n) (n ⊕ n) ℂ) :
    covarianceSource (KSSpinSource.family (fun i => KSRankOne.atom (v i)))
      (KSSpinSource.coefficientCovariance c) X =
    covarianceSource (KSSpinSource.family (fun i => KSRankOne.atom (liveVectors v x i)))
      (KSSpinSource.coefficientCovariance (fun i => c (liveEquiv x i))) X := by
  rw [KSSpinSource.source_eq_tracePrepare v c X,
    KSSpinSource.source_eq_tracePrepare (liveVectors v x) _ X]
  rw [KSLiveCurve.sum_restrict_live 1 x _ (by
    intro i hi
    simp only [hzero i hi, Complex.ofReal_zero, zero_mul, zero_smul])]
  exact ((liveEquiv x).sum_comp _).symm

theorem potential_restrict_fin (v : Fin N → n → ℂ) (x c : Fin N → ℝ)
    (hzero : ∀ i, ¬ |x i| < 1 → c i = 0)
    (M : Matrix (n ⊕ n) (n ⊕ n) ℂ) (θ : ℝ) :
    ownerPotential M (KSSpinSource.family (fun i => KSRankOne.atom (v i)))
      (KSSpinSource.coefficientCovariance c) θ =
    ownerPotential M (KSSpinSource.family (fun i => KSRankOne.atom (liveVectors v x i)))
      (KSSpinSource.coefficientCovariance (fun i => c (liveEquiv x i))) θ := by
  unfold ownerPotential
  congr 2
  funext X
  unfold ownerObjective
  rw [source_restrict_fin v x c hzero X]

def faceValue (v : Fin N → n → ℂ) (θ ζ : ℝ) (s : CubeState N ρ)
    (z : EuclideanSpace ℝ (Fin (count s.coeff))) : ℝ :=
  KSDebitPotential.potential (signedSum v (face s.coeff z)) (debit v s) v
    (SourceTransport.smoothWeights ζ (face s.coeff z)) θ

@[simp] theorem faceValue_zero (v : Fin N → n → ℂ) (θ ζ : ℝ) (s : CubeState N ρ) :
    faceValue v θ ζ s 0 = potential v θ ζ s := by
  simp only [faceValue, KSFullManuscriptLiveCoordinates.face_zero, potential]

def center (v : Fin N → n → ℂ) (s : CubeState N ρ) :=
  KSDebitCenter.center (signedSum v s.coeff) (debit v s)

def restrictedValue {k : ℕ} (M : Matrix (n ⊕ n) (n ⊕ n) ℂ)
    (v : Fin k → n → ℂ) (x : Fin k → ℝ) (θ ζ : ℝ)
    (z : EuclideanSpace ℝ (Fin k)) : ℝ :=
  ownerPotential (M + ∑ i, z i • signedLift (KSRankOne.atom (v i)))
    (KSSpinSource.family (fun i => KSRankOne.atom (v i)))
    (KSSpinSource.coefficientCovariance (SourceTransport.smoothWeights ζ (fun i => x i + z i))) θ

@[simp] theorem restrictedValue_zero {k : ℕ} (M : Matrix (n ⊕ n) (n ⊕ n) ℂ)
    (v : Fin k → n → ℂ) (x : Fin k → ℝ) (θ ζ : ℝ) :
    restrictedValue M v x θ ζ 0 = ownerPotential M
      (KSSpinSource.family (fun i => KSRankOne.atom (v i)))
      (KSSpinSource.coefficientCovariance (SourceTransport.smoothWeights ζ x)) θ := by
  simp [restrictedValue]

theorem face_live (x : Fin N → ℝ) (z : EuclideanSpace ℝ (Fin (count x))) (i : Fin (count x)) :
    face x z (liveEquiv x i) = livePositions x i + z i := by
  rw [face, KSFullManuscriptLiveCoordinates.linear_apply, KSLiveEnumeration.extend_live,
    Equiv.symm_apply_apply]
  rfl

theorem center_face (v : Fin N → n → ℂ) (s : CubeState N ρ)
    (z : EuclideanSpace ℝ (Fin (count s.coeff))) :
    KSDebitCenter.center (signedSum v (face s.coeff z)) (debit v s) =
      center v s + ∑ i, z i • signedLift (KSRankOne.atom (liveVectors v s.coeff i)) := by
  have hp := KSFullManuscriptLiveCoordinates.face_smul_eq_path s.coeff z (1 : ℝ)
  rw [one_smul] at hp
  unfold KSDebitCenter.center
  change signedLift (KSPotentialModels.center (fun i => KSRankOne.atom (v i)) (face s.coeff z)) - _ = _
  rw [hp, KSSpinLiveSource.signed_center_path, one_smul]
  have hs : (∑ i : KSLiveCurve.Live 1 s.coeff,
      KSFullManuscriptLiveCoordinates.coefficientDirection s.coeff z i •
        signedLift (KSRankOne.atom (v i))) =
      ∑ i, z i • signedLift (KSRankOne.atom (liveVectors v s.coeff i)) := by
    have he := (liveEquiv s.coeff).sum_comp (fun i =>
      z ((liveEquiv s.coeff).symm i) • signedLift (KSRankOne.atom (v i)))
    calc
      _ = ∑ i, z ((liveEquiv s.coeff).symm (liveEquiv s.coeff i)) •
          signedLift (KSRankOne.atom (v (liveEquiv s.coeff i))) := he.symm
      _ = _ := by
        apply Finset.sum_congr rfl
        intro i _
        change z ((liveEquiv s.coeff).symm (liveEquiv s.coeff i)) • _ = z i • _
        rw [Equiv.symm_apply_apply]
        rfl
  rw [hs]
  unfold center KSDebitCenter.center KSPotentialModels.center StatePotential.signedSum
  change _ + _ - _ = (_ - _) + _
  abel

theorem faceValue_eq_restricted (v : Fin N → n → ℂ) (θ ζ : ℝ) (s : CubeState N ρ)
    (z : EuclideanSpace ℝ (Fin (count s.coeff))) :
    faceValue v θ ζ s z = restrictedValue (center v s) (liveVectors v s.coeff)
      (livePositions s.coeff) θ ζ z := by
  have hzero : ∀ i, ¬ |s.coeff i| < 1 →
      SourceTransport.smoothWeights ζ (face s.coeff z) i = 0 := by
    intro i hi
    change Source.weight 64 ζ (face s.coeff z i) = 0
    rw [KSFullManuscriptLiveCoordinates.face_dead s.coeff z i hi]
    exact weights_dead ζ s.cube i hi
  unfold faceValue KSDebitPotential.potential
  rw [center_face, potential_restrict_fin v s.coeff _ hzero]
  unfold restrictedValue
  congr 2
  funext i
  change Source.weight 64 ζ (face s.coeff z (liveEquiv s.coeff i)) = _
  rw [face_live]
  rfl

theorem restrictedValue_curve {k : ℕ} (M : Matrix (n ⊕ n) (n ⊕ n) ℂ)
    (v : Fin k → n → ℂ) (x : Fin k → ℝ) (θ ζ : ℝ)
    (h : EuclideanSpace ℝ (Fin k)) (t : ℝ) :
    restrictedValue M v x θ ζ (t • h) =
      SmoothPotential.curvePotential M v θ ζ x (fun i => h i) t := by
  unfold restrictedValue SmoothPotential.curvePotential KSDebitLocalState.curveCenter
  simp only [PiLp.smul_apply, smul_eq_mul, MulAction.mul_smul, ← Finset.smul_sum, KSSpinLocalState.atoms]
  rfl

theorem contDiffAt_restrictedValue [Nonempty n] {k : ℕ}
    (M : Matrix (n ⊕ n) (n ⊕ n) ℂ) (hM : M.IsHermitian)
    (v : Fin k → n → ℂ) (x : Fin k → ℝ) (hx : ∀ i, |x i|<1)
    {θ ζ : ℝ} (hθ : 0<θ) (hζ : 0<ζ) :
    ContDiffAt ℝ ∞ (restrictedValue M v x θ ζ) 0 := by
  let Hh : selfAdjoint (Matrix (n ⊕ n) (n ⊕ n) ℂ) := ⟨M,hM⟩
  let Ah : Fin k → selfAdjoint (Matrix (n ⊕ n) (n ⊕ n) ℂ) :=
    fun i => ⟨signedLift (KSRankOne.atom (v i)),
      signedLift_isHermitian (KSRankOne.atom_isHermitian _)⟩
  let C := fun z : EuclideanSpace ℝ (Fin k) => SourceTransport.smoothWeights ζ (fun i => x i+z i)
  let P := fun z : EuclideanSpace ℝ (Fin k) =>
    (Hh+∑ i,z i • Ah i,KSDebitSmoothness.coefficientCovarianceCLM (C z))
  have hc : ContDiff ℝ ∞ C := by
    apply contDiff_pi.mpr
    intro i
    exact (Source.weight_contDiff hζ 64 ∞).comp (contDiff_const.add (by fun_prop))
  have hP : ContDiff ℝ ∞ P := by
    apply ContDiff.prodMk
    · fun_prop
    · exact KSDebitSmoothness.coefficientCovarianceCLM.contDiff.comp hc
  have hC : ((P 0).2 : Matrix (Fin k × Fin 4) (Fin k × Fin 4) ℝ).PosDef := by
    apply KSSpinCompression.coefficientCovariance_posDef
    intro i
    change 0<Source.weight 64 ζ (x i+(0 : EuclideanSpace ℝ (Fin k)) i)
    simpa using Source.weight_pos (ζ := ζ) (by norm_num : (0:ℝ)<64) (hx i)
  have hj := contDiffAt_jointHermitianOwnerPotential
    (KSSpinSource.family (fun i => KSRankOne.atom (v i)))
    (KSSpinSource.family_isHermitian _ (fun i => KSRankOne.atom_isHermitian (v i)))
    hθ (P 0).1 (P 0).2 hC
  convert hj.comp 0 hP.contDiffAt using 1
  funext z
  simp [restrictedValue,P,Hh,Ah,C,jointHermitianOwnerPotential,
    KSDebitSmoothness.coefficientCovarianceCLM]

theorem contDiffAt_faceValue [Nonempty n] (v : Fin N → n → ℂ)
    (s : CubeState N ρ) (hB : (debit v s).PosSemidef)
    {θ ζ : ℝ} (hθ : 0<θ) (hζ : 0<ζ) :
    ContDiffAt ℝ ∞ (faceValue v θ ζ s) 0 := by
  have he : faceValue v θ ζ s = restrictedValue (center v s)
      (liveVectors v s.coeff) (livePositions s.coeff) θ ζ := by
    funext z
    exact faceValue_eq_restricted v θ ζ s z
  rw [he]
  exact contDiffAt_restrictedValue (center v s)
    (KSDebitCenter.center_isHermitian_of_posSemidef (signedSum_isHermitian v s.coeff) hB)
    (liveVectors v s.coeff) (livePositions s.coeff) (livePositions_interior s.coeff) hθ hζ

theorem face_weighted_proposal (x : Fin N → ℝ) (ζ : ℝ)
    (w : EuclideanSpace ℝ (Fin (count x))) (t : ℝ) :
    face x (t • NormalizedHessian.diagonalMap
      (NormalizedHessian.sourceWeight ζ (livePositions x)) w) =
    Progress.proposal x (State.weights ζ x) (KSLiveEnumeration.extend x w) t := by
  funext i
  rw [face, map_smul, KSFullManuscriptLiveCoordinates.linear_apply]
  simp only [PiLp.smul_apply,smul_eq_mul,Progress.proposal]
  by_cases hi : |x i|<1
  · rw [KSLiveEnumeration.extend_live x _ ⟨i,hi⟩,
      NormalizedHessian.diagonalMap_apply,KSLiveEnumeration.extend_live x w ⟨i,hi⟩]
    unfold NormalizedHessian.sourceWeight livePositions State.weights
    rw [Equiv.apply_symm_apply]
  · rw [KSLiveEnumeration.extend_dead x _ i hi,KSLiveEnumeration.extend_dead x w i hi]
    ring

theorem single_positions {k : ℕ} (x : Fin k → ℝ) (i : Fin k) (t : ℝ) :
    (fun j => x j+EuclideanSpace.single i t j) = Function.update x i (x i+t) := by
  funext j
  by_cases hj : j=i
  · subst j
    simp
  · simp [EuclideanSpace.single_apply,hj,Function.update_of_ne hj]

theorem face_single (x : Fin N → ℝ) (i : Fin (count x)) (t : ℝ) :
    face x (EuclideanSpace.single i t) =
      Function.update x (liveEquiv x i) (x (liveEquiv x i)+t) := by
  funext j
  by_cases hj : |x j|<1
  · let k := (liveEquiv x).symm ⟨j,hj⟩
    have hk : (liveEquiv x k).val=j := congrArg Subtype.val ((liveEquiv x).apply_symm_apply ⟨j,hj⟩)
    have he : j=(liveEquiv x i).val ↔ k=i := by
      constructor
      · intro hh
        apply (liveEquiv x).injective
        apply Subtype.ext
        exact hk.trans hh
      · intro hh
        rw [← hk,hh]
    rw [← hk,face_live]
    by_cases hki : k=i
    · rw [hki]
      simp [livePositions]
    · have hji : (liveEquiv x k).val ≠ (liveEquiv x i).val := by
        intro hh
        exact hki ((liveEquiv x).injective (Subtype.ext hh))
      simp [EuclideanSpace.single_apply,hki,Function.update_of_ne hji,
        livePositions]
  · have hji : j≠(liveEquiv x i).val := by
      intro hh
      exact hj (hh ▸ (liveEquiv x i).property)
    rw [KSFullManuscriptLiveCoordinates.face_dead x _ j hj,Function.update_of_ne hji]

theorem restrictedValue_single {k : ℕ} (M : Matrix (n ⊕ n) (n ⊕ n) ℂ)
    (v : Fin k → n → ℂ) (x : Fin k → ℝ) (θ ζ : ℝ) (i : Fin k) (t : ℝ) :
    restrictedValue M v x θ ζ (EuclideanSpace.single i t) =
      ownerPotential (M+t • signedLift (KSRankOne.atom (v i)))
        (KSSpinSource.family (fun j => KSRankOne.atom (v j)))
        (KSSpinSource.coefficientCovariance
          (SourceTransport.smoothWeights ζ (Function.update x i (x i+t)))) θ := by
  unfold restrictedValue
  rw [single_positions]
  congr 2
  simp [EuclideanSpace.single_apply]

end SeamlessKS.LivePotential
