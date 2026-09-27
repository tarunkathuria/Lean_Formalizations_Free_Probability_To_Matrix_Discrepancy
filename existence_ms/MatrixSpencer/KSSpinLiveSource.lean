import MatrixSpencer.KSLiveCurve
import MatrixSpencer.KSSpinChosenRetirement

/-! Exact restriction of the spin source to original live labels. -/

open Matrix Filter Topology
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section
namespace MatrixSpencer.KSSpinLiveSource
open KSPotentialModels KSLiveCurve

variable {N : ℕ} {n : Type*} [Fintype n] [DecidableEq n]

theorem source_restrict (v : Fin N → n → ℂ) (a : ℝ) (x c : Fin N → ℝ)
    (hzero : ∀ i, ¬ |x i| < a → c i = 0)
    (X : Matrix (n ⊕ n) (n ⊕ n) ℂ) :
    covarianceSource (KSSpinSource.family (fun i => KSRankOne.atom (v i)))
      (KSSpinSource.coefficientCovariance c) X =
    covarianceSource (KSSpinSource.family (fun i : Live a x => KSRankOne.atom (v i)))
      (KSSpinSource.coefficientCovariance (fun i : Live a x => c i)) X := by
  rw [KSSpinSource.source_eq_tracePrepare v c X,
    KSSpinSource.source_eq_tracePrepare (fun i : Live a x => v i) (fun i => c i) X]
  apply sum_restrict_live a x
  intro i hi
  simp only [hzero i hi, Complex.ofReal_zero, zero_mul, zero_smul]

theorem objective_restrict (v : Fin N → n → ℂ) (a : ℝ) (x c : Fin N → ℝ)
    (hzero : ∀ i, ¬ |x i| < a → c i = 0)
    (H : Matrix (n ⊕ n) (n ⊕ n) ℂ) (θ : ℝ)
    (X : Matrix (n ⊕ n) (n ⊕ n) ℂ) :
    ownerObjective H (KSSpinSource.family (fun i => KSRankOne.atom (v i)))
      (KSSpinSource.coefficientCovariance c) θ X =
    ownerObjective H (KSSpinSource.family (fun i : Live a x => KSRankOne.atom (v i)))
      (KSSpinSource.coefficientCovariance (fun i : Live a x => c i)) θ X := by
  unfold ownerObjective
  rw [source_restrict v a x c hzero X]

theorem potential_restrict (v : Fin N → n → ℂ) (a : ℝ) (x c : Fin N → ℝ)
    (hzero : ∀ i, ¬ |x i| < a → c i = 0)
    (H : Matrix (n ⊕ n) (n ⊕ n) ℂ) (θ : ℝ) :
    ownerPotential H (KSSpinSource.family (fun i => KSRankOne.atom (v i)))
      (KSSpinSource.coefficientCovariance c) θ =
    ownerPotential H (KSSpinSource.family (fun i : Live a x => KSRankOne.atom (v i)))
      (KSSpinSource.coefficientCovariance (fun i : Live a x => c i)) θ := by
  unfold ownerPotential
  congr 2
  funext X
  exact objective_restrict v a x c hzero H θ X

theorem source_at_state (v : Fin N → n → ℂ) {x : Fin N → ℝ} (hx : x ∈ ksCube 1)
    (X : Matrix (n ⊕ n) (n ⊕ n) ℂ) :
    covarianceSource (KSSpinSource.family (fun i => KSRankOne.atom (v i)))
      (KSSpinSource.coefficientCovariance (naturalOwners 64 x)) X =
    covarianceSource (KSSpinSource.family (fun i : Live 1 x => KSRankOne.atom (v i)))
      (KSSpinSource.coefficientCovariance (fun i : Live 1 x => 64 * (1 - x i ^ 2))) X :=
  source_restrict v 1 x (naturalOwners 64 x) (naturalOwner_dead hx 64) X

theorem signed_center_path (A : Fin N → Matrix n n ℂ) (a : ℝ) (x : Fin N → ℝ)
    (h : Live a x → ℝ) (t : ℝ) :
    signedLift (center A (path a x h t)) =
      signedLift (center A x) + t • (∑ i : Live a x, h i • signedLift (A i)) := by
  rw [center_path, ← signedLift_sum_smul]
  ext i j
  cases i <;> cases j <;>
    simp [signedLift, Matrix.fromBlocks, Matrix.add_apply, Matrix.smul_apply, Matrix.neg_apply,
      smul_add, smul_neg] <;> ring

theorem potential_path (v : Fin N → n → ℂ) {x : Fin N → ℝ} (hx : x ∈ ksCube 1)
    (θ : ℝ) (h : Live 1 x → ℝ) (t : ℝ) :
    spinPotential (fun i => KSRankOne.atom (v i)) θ (path 1 x h t) =
    ownerPotential
      (signedLift (center (fun i => KSRankOne.atom (v i)) x) +
        t • (∑ i : Live 1 x, h i • signedLift (KSRankOne.atom (v i))))
      (KSSpinSource.family (fun i : Live 1 x => KSRankOne.atom (v i)))
      (KSSpinSource.coefficientCovariance (fun i : Live 1 x => 64 * (1 - (x i + t * h i) ^ 2))) θ := by
  unfold spinPotential
  rw [signed_center_path]
  have hzero : ∀ i, ¬ |x i| < 1 → naturalOwners 64 (path 1 x h t) i = 0 := by
    intro i hi
    change 64 * (1 - (path 1 x h t i) ^ 2) = 0
    rw [path_dead 1 x h t i hi]
    exact naturalOwner_dead hx 64 i hi
  rw [potential_restrict v 1 x (naturalOwners 64 (path 1 x h t)) hzero]
  congr 2
  funext i
  simp only [naturalOwners, path_live]

end MatrixSpencer.KSSpinLiveSource
