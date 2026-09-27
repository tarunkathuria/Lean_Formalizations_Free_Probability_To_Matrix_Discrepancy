import MatrixSpencer.KSFrobeniusTangent
import MatrixSpencer.KSEnvelopeFourth
import MatrixSpencer.KSFourthDifference
import MatrixSpencer.JointOwnerResponse
import MatrixSpencer.KSDebitLiveHessian
import MatrixSpencer.KSOwnerRelativeSource

/-!
# The fourth-derivative envelope bound for the actual KS live curve

The branch is the existing canonical density optimizer in the full trace-zero
Frobenius chart. Its smoothness, vertical stationarity and `θ/2` coercivity are
proved from the original owner objective. The actual live coefficient curve
stays positive on an explicit margin-based interval. Exact source restriction
then transfers the estimate to the full original-label curve, retaining frozen
zero owners.

The only remaining analytic inputs to the final curve theorems are upper bounds
on the actual joint second, third and fourth Fréchet derivative norms. The norm
wrappers below are definitionally those ordinary operator norms; they avoid
repeated typeclass elaboration for nested matrix-coordinate map spaces.
No optimizer, response, envelope identity, or Taylor remainder oracle is assumed.
-/

open Matrix Set Filter
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator ContDiff Topology
noncomputable section
namespace MatrixSpencer.KSActualEnvelope
set_option maxHeartbeats 1000000
section DerivativeNorms
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
local instance : NormedAddCommGroup ((ℝ × E) →L[ℝ] ℝ) := inferInstance
local instance : NormedSpace ℝ ((ℝ × E) →L[ℝ] ℝ) := inferInstance
local instance : NormedAddCommGroup ((ℝ × E) →L[ℝ] (ℝ × E) →L[ℝ] ℝ) := inferInstance
local instance : NormedSpace ℝ ((ℝ × E) →L[ℝ] (ℝ × E) →L[ℝ] ℝ) := inferInstance
local instance : NormedAddCommGroup ((ℝ × E) →L[ℝ] (ℝ × E) →L[ℝ] (ℝ × E) →L[ℝ] ℝ) := inferInstance
local instance : NormedSpace ℝ ((ℝ × E) →L[ℝ] (ℝ × E) →L[ℝ] (ℝ × E) →L[ℝ] ℝ) := inferInstance

/-- Exact joint operator norm, packaged before specializing the coordinate type. -/
def secondNorm (F : (ℝ × E) → ℝ) (p : ℝ × E) : ℝ := ‖KSEnvelopeFourth.second F p‖
def thirdNorm (F : (ℝ × E) → ℝ) (p : ℝ × E) : ℝ := ‖KSEnvelopeFourth.third F p‖
def fourthNorm (F : (ℝ × E) → ℝ) (p : ℝ × E) : ℝ := ‖KSEnvelopeFourth.fourth F p‖
end DerivativeNorms

variable {ι n : Type*} [Fintype ι] [DecidableEq ι] [Fintype n] [DecidableEq n] [Nonempty n]
local instance {k : Type*} [Fintype k] [DecidableEq k] : CStarAlgebra (Matrix k k ℂ) := {}
local instance : NormedAddCommGroup (selfAdjoint (Matrix n n ℂ)) := inferInstance
local instance : NormedSpace ℝ (selfAdjoint (Matrix n n ℂ)) := inferInstance
local instance : NormedAddCommGroup (selfAdjoint (Matrix ι ι ℝ)) := inferInstance
local instance : NormedSpace ℝ (selfAdjoint (Matrix ι ι ℝ)) := inferInstance
local instance : NormedAddCommGroup (KSFrobeniusTangent.Coordinates n) := inferInstance
local instance : NormedSpace ℝ (KSFrobeniusTangent.Coordinates n) := inferInstance

open KSFrobeniusTangent
local instance : NormedAddCommGroup (ℝ × Coordinates n) := inferInstance
local instance : NormedSpace ℝ (ℝ × Coordinates n) := inferInstance

/-- The original objective in the full affine trace-one Frobenius chart. -/
def objective (A : ι → Matrix n n ℂ) (θ : ℝ)
    (H : ℝ → selfAdjoint (Matrix n n ℂ)) (C : ℝ → selfAdjoint (Matrix ι ι ℝ))
    (P : ℝ × Coordinates n) : ℝ := ownerObjective (H P.1) A (C P.1) θ (chart n P.2)

/-- Coordinates of the already defined canonical density optimizer. -/
def branch (A : ι → Matrix n n ℂ) (θ : ℝ)
    (H : ℝ → selfAdjoint (Matrix n n ℂ)) (C : ℝ → selfAdjoint (Matrix ι ι ℝ))
    (t : ℝ) : Coordinates n :=
  project n (jointOwnerDensityOptimizer A θ (H t, C t))

theorem chart_branch (A : ι → Matrix n n ℂ) (θ : ℝ)
    (H : ℝ → selfAdjoint (Matrix n n ℂ)) (C : ℝ → selfAdjoint (Matrix ι ι ℝ)) (t : ℝ) :
    chart n (branch A θ H C t) = jointOwnerDensityOptimizer A θ (H t, C t) :=
  chart_project_of_trace_one n _ (hermitianDensityOptimizer_trace _ _ θ)

theorem branch_posDef (A : ι → Matrix n n ℂ) {θ : ℝ} (hθ : 0 < θ)
    (H : ℝ → selfAdjoint (Matrix n n ℂ)) (C : ℝ → selfAdjoint (Matrix ι ι ℝ)) (t : ℝ) :
    (chart n (branch A θ H C t) : Matrix n n ℂ).PosDef := by
  rw [chart_branch]
  exact hermitianDensityOptimizer_posDef _ _ hθ

variable (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).IsHermitian)
  {θ : ℝ} (hθ : 0 < θ)
  (H : ℝ → selfAdjoint (Matrix n n ℂ)) (C : ℝ → selfAdjoint (Matrix ι ι ℝ))
  (hH : ContDiff ℝ ∞ H) (hC : ContDiff ℝ ∞ C)

include hA hH hC

theorem objective_contDiffAt {t : ℝ} {x : Coordinates n}
    (hCt : (C t : Matrix ι ι ℝ).PosDef) (hS : (chart n x : Matrix n n ℂ).PosDef) :
    ContDiffAt ℝ ∞ (objective A θ H C) (t,x) := by
  have hh : ContDiffAt ℝ ∞ (fun P : ℝ × Coordinates n => (H P.1 : Matrix n n ℂ)) (t,x) :=
    (hermitianInclusion (n := n)).contDiff.contDiffAt.comp (t,x) (hH.contDiffAt.comp (t,x) contDiffAt_fst)
  have hs : ContDiffAt ℝ ∞ (fun P : ℝ × Coordinates n => (chart n P.2 : Matrix n n ℂ)) (t,x) :=
    (hermitianInclusion (n := n)).contDiff.contDiffAt.comp (t,x) ((contDiff_chart n).contDiffAt.comp (t,x) contDiffAt_snd)
  have hl := realTraceCLM.contDiff.contDiffAt.comp (t,x) (hh.mul hs)
  have hp : ContDiffAt ℝ ∞ (fun P : ℝ × Coordinates n => (C P.1, chart n P.2)) (t,x) :=
    (hC.contDiffAt.comp (t,x) contDiffAt_fst).prodMk
      ((contDiff_chart n).contDiffAt.comp (t,x) contDiffAt_snd)
  have hj := (contDiffAt_jointOwnerObjective (0 : Matrix n n ℂ) A hA θ (C t) (chart n x) hCt hS).comp (t,x) hp
  apply (hl.add hj).congr_of_eventuallyEq
  filter_upwards [] with P
  change ownerObjective (H P.1) A (C P.1) θ (chart n P.2) =
    realTrace ((H P.1 : Matrix n n ℂ) * (chart n P.2 : Matrix n n ℂ)) +
      ownerObjective (0 : Matrix n n ℂ) A (C P.1) θ (chart n P.2)
  simp only [ownerObjective, Matrix.zero_mul, realTrace_zero, zero_add]
  ring

include hθ in
theorem branch_contDiffAt {t : ℝ} (hCt : (C t : Matrix ι ι ℝ).PosDef) :
    ContDiffAt ℝ ∞ (branch A θ H C) t := by
  have hj : ContDiffAt ℝ ∞ (jointOwnerDensityOptimizer A θ) (H t,C t) :=
    contDiffAt_jointOwnerDensityOptimizer A hA hθ (H t) (C t) hCt
  have hpair : ContDiffAt ℝ ∞ (fun z => (H z,C z)) t := hH.contDiffAt.prodMk hC.contDiffAt
  have hc := ContDiffAt.comp (g := jointOwnerDensityOptimizer A θ) (f := fun z => (H z,C z)) t hj hpair
  exact ContDiffAt.comp (g := project n) (f := fun z => jointOwnerDensityOptimizer A θ (H z,C z)) t
    (project n).contDiff.contDiffAt hc

omit hH hC in
theorem vertical_line_eq {t : ℝ} (hCt : (C t : Matrix ι ι ℝ).PosDef)
    (x u : Coordinates n) :
    (fun z : ℝ => objective A θ H C ((t,x) + z • ((0 : ℝ),u))) =
      (fun z => hermitianDensityObjective (H t : Matrix n n ℂ) (covarianceKraus A (C t)) θ
        (chart n x + z • embedding n u)) := by
  funext z
  have he : chart n (x + z • u) = chart n x + z • embedding n u := by
    simp only [chart, map_add, map_smul]
    module
  change ownerObjective (H (t + z * 0)) A (C (t + z * 0)) θ (chart n (x + z • u)) = _
  rw [mul_zero, add_zero, he, ownerObjective_eq_densityObjective _ A hA hCt.posSemidef]
  rfl

/-- The actual joint vertical derivative is the original density derivative. -/
theorem vertical_derivative {t : ℝ} (hCt : (C t : Matrix ι ι ℝ).PosDef)
    (x u : Coordinates n) (hS : (chart n x : Matrix n n ℂ).PosDef) :
    fderiv ℝ (objective A θ H C) (t,x) (0,u) =
      fderiv ℝ (hermitianDensityObjective (H t : Matrix n n ℂ) (covarianceKraus A (C t)) θ)
        (chart n x) (embedding n u) := by
  have ho := ((objective_contDiffAt A hA (θ := θ) H C hH hC hCt hS).differentiableAt (by simp)).hasFDerivAt
  have hf := ((contDiffAt_hermitianDensityObjective_source_unrestricted
    (H t : Matrix n n ℂ) (covarianceKraus A (C t)) θ (chart n x) hS).differentiableAt (by simp)).hasFDerivAt
  have hline := ho.comp_hasDerivAt_of_eq 0
    (((hasDerivAt_id (0 : ℝ)).smul_const ((0 : ℝ),u)).const_add (t,x)) (by simp)
  have hline' := hf.comp_hasDerivAt_of_eq 0
    (((hasDerivAt_id (0 : ℝ)).smul_const (embedding n u)).const_add (chart n x)) (by simp)
  simp only [Function.comp_def, id_eq, one_smul] at hline hline'
  rw [vertical_line_eq A hA (θ := θ) H C hCt x u] at hline
  exact hline.unique hline'

/-- The actual joint vertical Hessian is the original density Hessian. -/
theorem vertical_hessian {t : ℝ} (hCt : (C t : Matrix ι ι ℝ).PosDef)
    (x u : Coordinates n) (hS : (chart n x : Matrix n n ℂ).PosDef) :
    KSEnvelopeFourth.second (objective A θ H C) (t,x) (0,u) (0,u) =
      fderiv ℝ (fderiv ℝ (hermitianDensityObjective (H t : Matrix n n ℂ) (covarianceKraus A (C t)) θ))
        (chart n x) (embedding n u) (embedding n u) := by
  rw [← KSFourthDifference.line_second (objective A θ H C) (t,x) (0,u)
    ((objective_contDiffAt A hA (θ := θ) H C hH hC hCt hS).of_le (WithTop.coe_le_coe.mpr (show (2 : ℕ∞) ≤ ⊤ from le_top)))]
  rw [vertical_line_eq A hA (θ := θ) H C hCt x u]
  exact KSFourthDifference.line_second _ _ _
    ((contDiffAt_hermitianDensityObjective_source_unrestricted
      (H t : Matrix n n ℂ) (covarianceKraus A (C t)) θ (chart n x) hS).of_le (WithTop.coe_le_coe.mpr (show (2 : ℕ∞) ≤ ⊤ from le_top)))


include hθ

/-- Vertical stationarity of the canonical optimizer, discharged internally. -/
theorem branch_stationary {t : ℝ} (hCt : (C t : Matrix ι ι ℝ).PosDef)
    (u : Coordinates n) :
    fderiv ℝ (objective A θ H C) (t,branch A θ H C t) (0,u) = 0 := by
  rw [vertical_derivative A hA H C hH hC hCt _ u (branch_posDef A hθ H C t), chart_branch]
  let U : densityTangent (n := n) := ⟨embedding n u, (mem_densityTangent_iff _).mpr (embedding_trace n u)⟩
  have hs := DFunLike.congr_fun (densityOptimizer_stationary_source_unrestricted
    (H t : Matrix n n ℂ) (covarianceKraus A (C t)) hθ) U
  exact hs

/-- The actual vertical Hessian has the explicit Frobenius coercivity `θ/2`. -/
theorem branch_coercive {t : ℝ} (hCt : (C t : Matrix ι ι ℝ).PosDef)
    (u : Coordinates n) :
    θ / 2 * ‖u‖ ^ 2 ≤
      -KSEnvelopeFourth.second (objective A θ H C) (t,branch A θ H C t) (0,u) (0,u) := by
  rw [vertical_hessian A hA H C hH hC hCt _ u (branch_posDef A hθ H C t), chart_branch]
  have hh := KSObjectiveCurvature.densityNegativeHessian_ge_of_density
    (H t : Matrix n n ℂ) (covarianceKraus A (C t)) θ hθ
    (jointOwnerDensityOptimizer A θ (H t,C t)) (embedding n u)
    (hermitianDensityOptimizer_posDef _ _ hθ) (hermitianDensityOptimizer_trace _ _ θ)
  rw [embedding_trace_square] at hh
  exact hh

omit hθ hH hC in
/-- The envelope is exactly the original supremum potential. -/
theorem value_eq {t : ℝ} (hCt : (C t : Matrix ι ι ℝ).PosDef) :
    objective A θ H C (t,branch A θ H C t) = ownerPotential (H t) A (C t) θ := by
  unfold objective
  rw [chart_branch]
  exact (ownerPotential_eq_chosenObjective (H t : Matrix n n ℂ) A hA θ (C t) hCt.posSemidef).symm

/-- Actual optimizer, stationarity and coercivity are all instantiated here.
Only the actual joint second-through-fourth derivative caps remain hypotheses. -/
theorem potential_fourth_le {I : Set ℝ} (hI : IsOpen I)
    (hpositive : ∀ t ∈ I, (C t : Matrix ι ι ℝ).PosDef)
    {t B : ℝ} (ht : t ∈ I) (hB : 0 ≤ B)
    (h₂ : secondNorm (objective A θ H C) (t,branch A θ H C t) ≤ B)
    (h₃ : thirdNorm (objective A θ H C) (t,branch A θ H C t) ≤ B)
    (h₄ : fourthNorm (objective A θ H C) (t,branch A θ H C t) ≤ B) :
    |iteratedDeriv 4 (fun z => ownerPotential (H z) A (C z) θ) t| ≤
      (B + 3 * B ^ 2 / (θ / 2)) * (1 + B / (θ / 2)) ^ 4 := by
  have hs : ContDiffOn ℝ 4 (branch A θ H C) I := by
    intro z hz
    exact ((branch_contDiffAt A hA hθ H C hH hC (hpositive z hz)).of_le
      (WithTop.coe_le_coe.mpr (show (4 : ℕ∞) ≤ ⊤ from le_top))).contDiffWithinAt
  have hf : ∀ z ∈ I, ContDiffAt ℝ 4 (objective A θ H C)
      (KSEnvelopeFourth.lift (branch A θ H C) z) := by
    intro z hz
    exact (objective_contDiffAt A hA H C hH hC (hpositive z hz) (branch_posDef A hθ H C z)).of_le
      (WithTop.coe_le_coe.mpr (show (4 : ℕ∞) ≤ ⊤ from le_top))
  have hstat : ∀ z ∈ I, ∀ u : Coordinates n,
      fderiv ℝ (objective A θ H C) (KSEnvelopeFourth.lift (branch A θ H C) z) (0,u) = 0 :=
    fun z hz u => branch_stationary A hA hθ H C hH hC (hpositive z hz) u
  have hh := KSEnvelopeFourth.value_fourth_le hI hs hf hstat ht
    (div_pos hθ (by norm_num)) hB h₂ h₃ h₄ (branch_coercive A hA hθ H C hH hC (hpositive t ht))
  have he : (fun z => objective A θ H C (KSEnvelopeFourth.lift (branch A θ H C) z)) =ᶠ[𝓝 t]
      (fun z => ownerPotential (H z) A (C z) θ) := by
    filter_upwards [hI.mem_nhds ht] with z hz
    exact value_eq A hA H C (hpositive z hz)
  rwa [Filter.EventuallyEq.iteratedDeriv_eq 4 he] at hh


omit hA hθ hH hC

/-- The actual fixed-debit affine center as a Hermitian-valued curve. -/
def curveH (M : Matrix (n ⊕ n) (n ⊕ n) ℂ) (hM : M.IsHermitian)
    (v : ι → n → ℂ) (h : ι → ℝ) (t : ℝ) : selfAdjoint (Matrix (n ⊕ n) (n ⊕ n) ℂ) :=
  ⟨M,hM⟩ + t • ⟨∑ i, h i • signedLift (KSSpinLocalState.atoms v i), by
    change (∑ i, h i • signedLift (KSSpinLocalState.atoms v i))ᴴ = _
    simp only [Matrix.conjTranspose_sum, Matrix.conjTranspose_smul, star_trivial]
    exact Finset.sum_congr rfl (fun i _ => congrArg (fun Q => h i • Q)
      (signedLift_isHermitian (KSRankOne.atom_isHermitian (v i))).eq)⟩

def curveC (x h : ι → ℝ) (t : ℝ) : selfAdjoint (Matrix (ι × Fin 4) (ι × Fin 4) ℝ) :=
  KSDebitSmoothness.coefficientCovarianceCLM (KSSpinLocalState.ownerCurve x h t)

def curveObjective (M : Matrix (n ⊕ n) (n ⊕ n) ℂ) (hM : M.IsHermitian)
    (v : ι → n → ℂ) (θ : ℝ) (x h : ι → ℝ) : ℝ × Coordinates (n ⊕ n) → ℝ :=
  objective (KSSpinSource.family (KSSpinLocalState.atoms v)) θ (curveH M hM v h) (curveC x h)

def curveBranch (M : Matrix (n ⊕ n) (n ⊕ n) ℂ) (hM : M.IsHermitian)
    (v : ι → n → ℂ) (θ : ℝ) (x h : ι → ℝ) : ℝ → Coordinates (n ⊕ n) :=
  branch (KSSpinSource.family (KSSpinLocalState.atoms v)) θ (curveH M hM v h) (curveC x h)

/-- Explicit open interval on which all live owners stay positive. -/
def curveDomain (δ d : ℝ) : Set ℝ :=
  Ioo (-KSOwnerRelativeSource.relativeRadius δ 1 d) (KSOwnerRelativeSource.relativeRadius δ 1 d)

theorem curveC_posDef {x h : ι → ℝ} {δ d : ℝ} (hδ : 0 < δ) (hd : 0 ≤ d)
    (hmargin : ∀ i, δ ≤ 1 - |x i|) (hdir : ∀ i, |h i| ≤ d)
    {t : ℝ} (ht : t ∈ curveDomain δ d) :
    (curveC x h t : Matrix (ι × Fin 4) (ι × Fin 4) ℝ).PosDef := by
  apply KSSpinCompression.coefficientCovariance_posDef
  have hstep : |t| ≤ KSOwnerRelativeSource.relativeRadius δ 1 d := (abs_lt.mpr ht).le
  apply KSSpinLocalState.owners_pos (x := fun i => x i + t * h i)
  intro i
  have he := KSOwnerRelativeSource.displacement_le_of_radius hδ.le (show (0 : ℝ) ≤ 1 by norm_num)
    hd (hdir i) hstep
  have ha := abs_add_le (x i) (t * h i)
  have hm := hmargin i
  simp only [mul_one] at he
  linarith

omit [DecidableEq ι] [Nonempty n] in
theorem contDiff_curveH (M : Matrix (n ⊕ n) (n ⊕ n) ℂ) (hM : M.IsHermitian)
    (v : ι → n → ℂ) (h : ι → ℝ) : ContDiff ℝ ∞ (curveH M hM v h) :=
  contDiff_const.add (contDiff_id.smul contDiff_const)

theorem contDiff_curveC (x h : ι → ℝ) : ContDiff ℝ ∞ (curveC x h) :=
  (KSDebitSmoothness.coefficientCovarianceCLM (ι := ι)).contDiff.comp (KSDebitSmoothness.contDiff_ownerCurve x h)

/-- The actual KS local curve now meets the envelope theorem's branch,
stationarity, positive-coefficient and Frobenius-coercivity requirements.
Its joint derivative caps are the sole remaining analytic estimates. -/
theorem curvePotential_fourth_le
    (M : Matrix (n ⊕ n) (n ⊕ n) ℂ) (hM : M.IsHermitian)
    (v : ι → n → ℂ) {θ δ d B : ℝ} (hθ : 0 < θ) (hδ : 0 < δ) (hd : 0 ≤ d)
    (x h : ι → ℝ) (hmargin : ∀ i, δ ≤ 1 - |x i|) (hdir : ∀ i, |h i| ≤ d)
    {t : ℝ} (ht : t ∈ curveDomain δ d) (hB : 0 ≤ B)
    (h₂ : secondNorm (curveObjective M hM v θ x h) (t,curveBranch M hM v θ x h t) ≤ B)
    (h₃ : thirdNorm (curveObjective M hM v θ x h) (t,curveBranch M hM v θ x h t) ≤ B)
    (h₄ : fourthNorm (curveObjective M hM v θ x h) (t,curveBranch M hM v θ x h t) ≤ B) :
    |iteratedDeriv 4 (KSDebitLocalState.curvePotential M v θ x h) t| ≤
      (B + 3 * B ^ 2 / (θ / 2)) * (1 + B / (θ / 2)) ^ 4 := by
  exact potential_fourth_le (KSSpinSource.family (KSSpinLocalState.atoms v))
    (KSSpinSource.family_isHermitian _ (fun i => KSRankOne.atom_isHermitian (v i))) hθ
    (curveH M hM v h) (curveC x h) (contDiff_curveH M hM v h) (contDiff_curveC x h)
    isOpen_Ioo (fun z hz => curveC_posDef hδ hd hmargin hdir hz) ht hB h₂ h₃ h₄

/-- Full original labels, including frozen zero owners, use the same actual
fourth-derivative bound through the proved source restriction identity. -/
theorem fullCurvePotential_fourth_le {N : ℕ}
    (M : Matrix (n ⊕ n) (n ⊕ n) ℂ) (hM : M.IsHermitian)
    (v : Fin N → n → ℂ) {θ δ d B : ℝ} (hθ : 0 < θ) (hδ : 0 < δ) (hd : 0 ≤ d)
    {x : Fin N → ℝ} (hx : x ∈ ksCube 1)
    (h : KSLiveCurve.Live 1 x → ℝ)
    (hmargin : ∀ i : KSLiveCurve.Live 1 x, δ ≤ 1 - |x i|) (hdir : ∀ i, |h i| ≤ d)
    {t : ℝ} (ht : t ∈ curveDomain δ d) (hB : 0 ≤ B)
    (h₂ : secondNorm (curveObjective M hM (fun i : KSLiveCurve.Live 1 x => v i)
      θ (fun i => x i) h) (t,curveBranch M hM (fun i : KSLiveCurve.Live 1 x => v i) θ (fun i => x i) h t) ≤ B)
    (h₃ : thirdNorm (curveObjective M hM (fun i : KSLiveCurve.Live 1 x => v i)
      θ (fun i => x i) h) (t,curveBranch M hM (fun i : KSLiveCurve.Live 1 x => v i) θ (fun i => x i) h t) ≤ B)
    (h₄ : fourthNorm (curveObjective M hM (fun i : KSLiveCurve.Live 1 x => v i)
      θ (fun i => x i) h) (t,curveBranch M hM (fun i : KSLiveCurve.Live 1 x => v i) θ (fun i => x i) h t) ≤ B) :
    |iteratedDeriv 4 (KSDebitLiveHessian.fullCurvePotential M v θ x h) t| ≤
      (B + 3 * B ^ 2 / (θ / 2)) * (1 + B / (θ / 2)) ^ 4 := by
  rw [show KSDebitLiveHessian.fullCurvePotential M v θ x h =
    KSDebitLocalState.curvePotential M (fun i : KSLiveCurve.Live 1 x => v i) θ (fun i => x i) h from
      funext (KSDebitLiveHessian.fullCurvePotential_eq M v θ hx h)]
  exact curvePotential_fourth_le M hM _ hθ hδ hd _ h hmargin hdir ht hB h₂ h₃ h₄

end MatrixSpencer.KSActualEnvelope
