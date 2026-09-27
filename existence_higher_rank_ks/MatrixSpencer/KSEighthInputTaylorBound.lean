import MatrixSpencer.KSEighthJointBoundPoint

/-!
# Input-only uniform Taylor bound for the actual eighth-cube potential

Every budget is an arithmetic expression in the original matrix entries and
the regularizer. The theorem ranges over all retained faces and all bounded
directions; it supplies the actual fourth derivative bound without analytic
or numerical oracle premises.
-/

open Matrix Set
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator ContDiff
noncomputable section
namespace MatrixSpencer.KSEighthInputTaylorBound
open KSLiveCurve KSEighthJointBoundPoint KSOwnerInputBounds

variable {N : ℕ} {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
local instance {k : Type*} [Fintype k] [DecidableEq k] : CStarAlgebra (Matrix k k ℂ) := {}

def slopeBudget (v : Fin N → n → ℂ) : ℝ := KSComplexPolynomialBounds.slopeBudget v
def centerCap (v : Fin N → n → ℂ) : ℝ := 3 * slopeBudget v
def directionCap (v : Fin N → n → ℂ) : ℝ := 2 * slopeBudget v
def sourceCap (v : Fin N → n → ℂ) : ℝ :=
  KSComplexTraceBounds.sourceBudget (KSEighthActualState.family v)
def jointBudget (v : Fin N → n → ℂ) (θ : ℝ) : ℝ :=
  jointCap (n := n) (centerCap v) (directionCap v) (sourceCap v) θ
def fourthBudget (v : Fin N → n → ℂ) (θ : ℝ) : ℝ :=
  (jointBudget v θ + 3*(jointBudget v θ)^2/(θ/2)) * (1+jointBudget v θ/(θ/2))^4

theorem slopeBudget_pos (v : Fin N → n → ℂ) : 0 < slopeBudget v :=
  KSComplexPolynomialBounds.slopeBudget_pos v

theorem jointBudget_pos (v : Fin N → n → ℂ) {θ : ℝ} (hθ : 0 < θ) : 0 < jointBudget v θ := by
  have hs := slopeBudget_pos v
  exact jointCap_pos (by unfold centerCap; positivity) (by unfold directionCap; positivity) hθ

theorem fourthBudget_pos (v : Fin N → n → ℂ) {θ : ℝ} (hθ : 0 < θ) : 0 < fourthBudget v θ := by
  have hB := jointBudget_pos v hθ
  unfold fourthBudget
  positivity

theorem sourceCap_restrict (v : Fin N → n → ℂ) (x : Fin N → ℝ) :
    KSComplexTraceBounds.sourceBudget
      (KSEighthActualState.family (fun i : Live (1/8) x => v i)) ≤ sourceCap v := by
  let f : Fin N → ℝ := fun i => ∑ b : Bool, matrixBound (KSEighthActualState.family v (i,b))^2
  have hs := Fintype.sum_subtype_add_sum_subtype (fun i : Fin N => |x i| < (1/8 : ℝ)) f
  have hn : 0 ≤ ∑ i : {i : Fin N // ¬ |x i| < (1/8 : ℝ)}, f i :=
    Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun _ _ => sq_nonneg _))
  have hle : (∑ i : Live (1/8) x, f i) ≤ ∑ i, f i := by linarith
  unfold sourceCap KSComplexTraceBounds.sourceBudget
  simp only [Fintype.sum_prod_type]
  exact add_le_add_left (mul_le_mul_of_nonneg_left hle (by positivity)) _

theorem slopeBudget_restrict (v : Fin N → n → ℂ) (x : Fin N → ℝ) :
    KSComplexPolynomialBounds.slopeBudget (fun i : Live (1/8) x => v i) ≤ slopeBudget v := by
  exact KSComplexTraceBounds.slopeBudget_restrict (fun i => signedLift (KSRankOne.atom (v i)))
    (fun i => |x i| < (1/8 : ℝ))

theorem signed_center_norm_le (v : Fin N → n → ℂ) (x : Fin N → ℝ)
    (hx : x ∈ ksCube (1/8)) :
    ‖signedLift (KSPotentialModels.center (fun i => KSRankOne.atom (v i)) x)‖ ≤ slopeBudget v := by
  rw [KSPotentialModels.center, signedLift_sum_smul]
  calc _ ≤ ∑ i, ‖x i • signedLift (KSRankOne.atom (v i))‖ := norm_sum_le _ _
    _ ≤ ∑ i, matrixBound (signedLift (KSRankOne.atom (v i))) := by
      apply Finset.sum_le_sum
      intro i _
      rw [norm_smul, Real.norm_eq_abs]
      have hxi : |x i| ≤ 1 := (abs_le.mpr ⟨hx.1 i,hx.2 i⟩).trans (by norm_num)
      calc _ ≤ 1 * matrixBound (signedLift (KSRankOne.atom (v i))) :=
          mul_le_mul hxi (norm_le_matrixBound _ (signedLift_isHermitian (KSRankOne.atom_isHermitian _)))
            (norm_nonneg _) (by norm_num)
        _ = _ := one_mul _
    _ ≤ slopeBudget v := by unfold slopeBudget KSComplexPolynomialBounds.slopeBudget; linarith

theorem direction_norm_le (v : Fin N → n → ℂ) (x : Fin N → ℝ)
    (h : Live (1/8) x → ℝ) (hh : ∀ i, |h i| ≤ 2) :
    ‖KSComplexOwnerObjective.slope (fun i : Live (1/8) x => v i) h‖ ≤ directionCap v := by
  exact (KSComplexPolynomialBounds.slope_norm_le _ h hh).trans
    (mul_le_mul_of_nonneg_left (slopeBudget_restrict v x) (by norm_num))

theorem curve_center_norm_le (v : Fin N → n → ℂ) (x : Fin N → ℝ)
    (hx : x ∈ ksCube (1/8)) (h : Live (1/8) x → ℝ) (hh : ∀ i, |h i| ≤ 2)
    {t : ℝ} (ht : |t| ≤ 1/32) :
    ‖KSEighthLocalState.curveCenter (KSPotentialModels.center (fun i => KSRankOne.atom (v i)) x)
      (fun i : Live (1/8) x => v i) h t‖ ≤ centerCap v := by
  apply (norm_add_le _ _).trans
  rw [norm_smul, Real.norm_eq_abs]
  have htone : |t| ≤ 1 := ht.trans (by norm_num)
  have hm := mul_le_mul htone (direction_norm_le v x h hh) (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
  have hc := signed_center_norm_le v x hx
  unfold centerCap directionCap at *
  unfold KSComplexOwnerObjective.slope at hm
  linarith

theorem joint_bounds (v : Fin N → n → ℂ) {θ : ℝ} (hθ : 0 < θ)
    (x : Fin N → ℝ) (hx : x ∈ ksCube (1/8)) (h : Live (1/8) x → ℝ)
    (hh : ∀ i, |h i| ≤ 2) {t : ℝ} (ht : |t| ≤ 1/32) :
    let Q := KSPotentialModels.center (fun i => KSRankOne.atom (v i)) x
    let hQ := KSPotentialModels.center_isHermitian _ (fun i => KSRankOne.atom_isHermitian (v i)) x
    let vr := fun i : Live (1/8) x => v i
    let F := KSEighthAnalyticCurve.objective Q hQ vr θ (fun i => x i) h
    let q := KSEighthAnalyticCurve.branch Q hQ vr θ (fun i => x i) h t
    KSActualEnvelope.secondNorm F (t,q) ≤ jointBudget v θ ∧
      KSActualEnvelope.thirdNorm F (t,q) ≤ jointBudget v θ ∧
      KSActualEnvelope.fourthNorm F (t,q) ≤ jointBudget v θ := by
  dsimp only
  apply KSEighthJointBoundPoint.joint_bounds _ _ _ hθ _ h
    (fun i => abs_le.mpr ⟨hx.1 i,hx.2 i⟩) hh ht
  · exact curve_center_norm_le v x hx h hh ht
  · exact direction_norm_le v x h hh
  · exact sourceCap_restrict v x

/-- Uniform actual fourth derivative bound, computed from original input only. -/
theorem curve_fourth_bound (v : Fin N → n → ℂ) {θ : ℝ} (hθ : 0 < θ)
    (x : Fin N → ℝ) (hx : x ∈ ksCube (1/8)) (h : Live (1/8) x → ℝ)
    (hh : ∀ i, |h i| ≤ 2) {t : ℝ} (ht : |t| ≤ 1/32) :
    |iteratedDeriv 4 (KSEighthLocalState.curvePotential
      (KSPotentialModels.center (fun i => KSRankOne.atom (v i)) x)
      (fun i : Live (1/8) x => v i) θ (fun i => x i) h) t| ≤ fourthBudget v θ := by
  let Q := KSPotentialModels.center (fun i => KSRankOne.atom (v i)) x
  have hQ := KSPotentialModels.center_isHermitian _ (fun i => KSRankOne.atom_isHermitian (v i)) x
  have hpos : ∀ z ∈ Ioo (-(1/8 : ℝ)) (1/8), ∀ i : Live (1/8) x, |x i+z*h i| < 1 := by
    intro z hz i
    have hxi : |x i| ≤ (1/8 : ℝ) := abs_le.mpr ⟨hx.1 i,hx.2 i⟩
    have hzabs : |z| < (1/8 : ℝ) := abs_lt.mpr hz
    have hm := mul_le_mul hzabs.le (hh i) (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1/8)
    rw [← abs_mul] at hm
    have ha := abs_add_le (x i) (z*h i)
    linarith
  have hti : t ∈ Ioo (-(1/8 : ℝ)) (1/8) := by
    have ha := abs_le.mp ht
    constructor <;> linarith
  obtain ⟨h₂,h₃,h₄⟩ := joint_bounds v hθ x hx h hh ht
  exact KSEighthAnalyticCurve.curvePotential_fourth_le Q hQ _ hθ _ h isOpen_Ioo
    hpos hti (jointBudget_pos v hθ).le h₂ h₃ h₄

end MatrixSpencer.KSEighthInputTaylorBound
