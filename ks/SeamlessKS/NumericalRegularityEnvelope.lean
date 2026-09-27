import SeamlessKS.NumericalRegularityParseval
import SeamlessKS.StateBounds
import SeamlessKS.SmoothPotential

/-!
The polynomial fourth derivative bound for the actual smooth-source optimized
potential. Joint derivatives, canonical optimizer floor, stationarity,
coercivity, and the envelope correction are all derived in the proof.
-/
open Matrix Set Filter
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator ContDiff Topology
noncomputable section
namespace SeamlessKS
namespace NumericalRegularityEnvelope
open MatrixSpencer NumericalRegularityJoint
variable {ι n : Type*} [Fintype ι] [DecidableEq ι] [Fintype n] [DecidableEq n] [Nonempty n]
local instance {k : Type*} [Fintype k] [DecidableEq k] : CStarAlgebra (Matrix k k ℂ) := {}
set_option maxHeartbeats 400000

def densityFloor (θ : ℝ) : ℝ := (θ / 40) ^ 2

def derivativeCap (ρ ζ θ : ℝ) : ℝ :=
  let X := NumericalRegularityParseval.jointCap (n := n) (densityFloor θ) ρ ζ
  (X + 3 * X ^ 2 / (θ / 2)) * (1 + X / (θ / 2)) ^ 4

theorem contDiffAt_curvePotential {ζ θ : ℝ} (hζ : 0 < ζ) (hθ : 0 < θ)
    (M : Matrix (n ⊕ n) (n ⊕ n) ℂ) (hM : M.IsHermitian)
    (v : ι → n → ℂ) (x h : ι → ℝ) (t : ℝ)
    (hx : ∀ i, |x i + t * h i| < 1) :
    ContDiffAt ℝ ∞ (SmoothPotential.curvePotential M v θ ζ x h) t := by
  let H := KSActualEnvelope.curveH M hM v h
  let C := curveC ζ x h
  have hP : ContDiff ℝ ∞ (fun z : ℝ => (H z,C z)) :=
    (KSActualEnvelope.contDiff_curveH M hM v h).prodMk (contDiff_curveC hζ x h)
  have hCt : (C t : Matrix (ι × Fin 4) (ι × Fin 4) ℝ).PosDef :=
    KSSpinCompression.coefficientCovariance_posDef (fun i => Source.weight_pos (by norm_num) (hx i))
  have hj := contDiffAt_jointHermitianOwnerPotential
    (KSSpinSource.family (KSSpinLocalState.atoms v))
    (KSSpinSource.family_isHermitian _ (fun i => KSRankOne.atom_isHermitian (v i)))
    hθ (H t) (C t) hCt
  have hf := hj.comp t hP.contDiffAt
  convert hf using 1


theorem curve_fourth_le {ζ ρ θ : ℝ} (hζ : 0 < ζ) (hζone : ζ ≤ 1)
    (hρ : 0 < ρ) (hθ : 0 < θ)
    (hreg : θ * Real.sqrt (Fintype.card (n ⊕ n) : ℝ) ≤ 1)
    (M : Matrix (n ⊕ n) (n ⊕ n) ℂ) (hM : M.IsHermitian)
    (v : ι → n → ℂ) (hparseval : (∑ i, KSRankOne.atom (v i)) ≤ 1)
    (x h : ι → ℝ) (t : ℝ) (hx : ∀ i, |x i + t * h i| ≤ 1 - ρ)
    (hh : ∀ i, |h i| ≤ 2)
    (hcenter : ‖KSDebitLocalState.curveCenter M v h t‖ ≤ 2) :
    |iteratedDeriv 4 (SmoothPotential.curvePotential M v θ ζ x h) t| ≤
      derivativeCap (n := n) ρ ζ θ := by
  let A := KSSpinSource.family (KSSpinLocalState.atoms v)
  have hA : ∀ j, (A j).IsHermitian :=
    KSSpinSource.family_isHermitian _ (fun i => KSRankOne.atom_isHermitian (v i))
  let H := KSActualEnvelope.curveH M hM v h
  let C := curveC ζ x h
  let q := KSActualEnvelope.branch A θ H C t
  have hH : ContDiff ℝ ∞ H := KSActualEnvelope.contDiff_curveH M hM v h
  have hC : ContDiff ℝ ∞ C := contDiff_curveC hζ x h
  have hμ : 0 < densityFloor θ := by unfold densityFloor; positivity
  have hθone : θ ≤ 1 := by
    have hcard : (1 : ℝ) ≤ Fintype.card (n ⊕ n) := by exact_mod_cast Fintype.card_pos
    have hs := Real.one_le_sqrt.mpr hcard
    nlinarith
  have howners : ∀ i, 0 ≤ Source.weight 64 ζ (x i + t * h i) := by
    intro i
    exact Source.weight_nonneg (by norm_num) (by have hi := hx i; linarith)
  have hcap : ∀ i, Source.weight 64 ζ (x i + t * h i) ≤ 128 := by
    intro i
    have hu := Source.weight_upper (u := 64) (ζ := ζ) (by norm_num) hζ.le (x i + t * h i)
    norm_num at hu
    exact hu
  have hHt : (KSDebitLocalState.curveCenter M v h t).IsHermitian := (H t).property
  have hqeq : (KSFrobeniusTangent.chart (n ⊕ n) q : Matrix (n ⊕ n) (n ⊕ n) ℂ) =
      densityOptimizer (KSDebitLocalState.curveCenter M v h t)
        (covarianceKraus (KSSpinSource.family (fun i => KSRankOne.atom (v i)))
          (KSSpinSource.coefficientCovariance (fun i => Source.weight 64 ζ (x i + t * h i)))) θ := by
    rw [KSActualEnvelope.chart_branch]
    rfl
  have hfloor : densityFloor θ • (1 : Matrix (n ⊕ n) (n ⊕ n) ℂ) ≤
      (KSFrobeniusTangent.chart (n ⊕ n) q : Matrix (n ⊕ n) (n ⊕ n) ℂ) := by
    rw [hqeq]
    exact StateBounds.optimizer_floor v hparseval (fun i => Source.weight 64 ζ (x i + t * h i))
      howners hcap (KSDebitLocalState.curveCenter M v h t) hHt hcenter hθ hreg
  have hSnorm : ‖(KSFrobeniusTangent.chart (n ⊕ n) q : Matrix (n ⊕ n) (n ⊕ n) ℂ)‖ ≤ 1 := by
    rw [hqeq]
    exact StateBounds.optimizer_norm_le_one (KSDebitLocalState.curveCenter M v h t) v
      (fun i => Source.weight 64 ζ (x i + t * h i)) θ
  have hcenter' : ‖NumericalRegularityObjective.complexCenter M v h (t : ℂ)‖ ≤ 2 := by
    rw [NumericalRegularityObjective.complexCenter_real]
    exact hcenter
  obtain ⟨h₂,h₃,h₄⟩ := NumericalRegularityParseval.joint_bounds hζ hζone hμ hρ hθ.le hθone
    M hM v hparseval x h t q hfloor hSnorm hx hh hcenter'
  let I := Set.Ioo (t - ρ / 4) (t + ρ / 4)
  have hI : IsOpen I := isOpen_Ioo
  have ht : t ∈ I := by constructor <;> linarith
  have hpositive : ∀ z ∈ I, (C z : Matrix (ι × Fin 4) (ι × Fin 4) ℝ).PosDef := by
    intro z hz
    change (KSSpinSource.coefficientCovariance (fun i => Source.weight 64 ζ (x i + z * h i))).PosDef
    apply KSSpinCompression.coefficientCovariance_posDef
    intro i
    apply Source.weight_pos (by norm_num)
    have hzt : |z-t| ≤ ρ / 4 := by
      apply abs_le.mpr
      constructor <;> have hl := hz.1 <;> have hu := hz.2 <;> linarith
    have hmul := mul_le_mul hzt (hh i) (abs_nonneg _) (by positivity : 0 ≤ ρ / 4)
    rw [← abs_mul] at hmul
    have ha := abs_add_le (x i+t*h i) ((z-t)*h i)
    have he : x i+t*h i+(z-t)*h i = x i+z*h i := by ring
    rw [he] at ha
    have hi := hx i
    linarith
  have hout := KSActualEnvelope.potential_fourth_le A hA hθ H C hH hC hI hpositive ht
    (NumericalRegularityParseval.jointCap_nonneg (n := n) (densityFloor θ) ρ ζ) h₂ h₃ h₄
  have hfun : (fun z => ownerPotential (H z) A (C z) θ) = SmoothPotential.curvePotential M v θ ζ x h := rfl
  rw [hfun] at hout
  exact hout

end NumericalRegularityEnvelope
end SeamlessKS
