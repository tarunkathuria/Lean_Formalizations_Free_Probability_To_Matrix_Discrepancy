import MatrixSpencer.MSManuscriptComplexValueBound
import MatrixSpencer.KSComplexEnvelopeChart

/-!
# Complex extension along an actual matched movement

The center is H+tB and the coefficient covariance is C−t²Q. This module
controls the actual polynomial pullback on a complex time/density ball;
no affine surrogate or bound on a positive physical-source eigenvalue is used.
-/
open Matrix Set Metric
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator ContDiff
noncomputable section
namespace MatrixSpencer.MSManuscriptMatchedComplex
open MSManuscriptComplexObjective KSCompactResolvent
variable {ι n : Type*} [Fintype ι] [DecidableEq ι] [Fintype n] [DecidableEq n]
local instance {k : Type*} [Fintype k] [DecidableEq k] : CStarAlgebra (Matrix k k ℂ) := {}
set_option maxHeartbeats 1000000

abbrev Space (n : Type*) := ℂ × Matrix n n ℂ

def radius (γ μ : ℝ) : ℝ := MSManuscriptComplexSourceDomain.radius γ μ/4

def center (H B : Matrix n n ℂ) (z : ℂ) : Matrix n n ℂ := H+z•B

def coefficient (C Q : Matrix ι ι ℝ) (z : ℂ) : Matrix ι ι ℂ :=
  realMatrixEmbedding C-z^2•realMatrixEmbedding Q

def query (C Q : Matrix ι ι ℝ) (p : Space n) : MSManuscriptComplexObjective.Space ι n :=
  (coefficient C Q p.1,p.2)

def objective (H B : Matrix n n ℂ) (A : ι → Matrix n n ℂ) (C Q : Matrix ι ι ℝ)
    (θ : ℝ) (p : Space n) : ℂ :=
  MSManuscriptComplexObjective.objective (center H B p.1) A θ (query C Q p)

theorem contDiff_center (H B : Matrix n n ℂ) : ContDiff ℂ ∞ (center H B) :=
  contDiff_const.add (contDiff_id.smul contDiff_const)

theorem contDiff_query (C Q : Matrix ι ι ℝ) : ContDiff ℂ ∞ (query (n := n) C Q) :=
  (contDiff_const.sub ((contDiff_fst.pow 2).smul contDiff_const)).prodMk contDiff_snd

theorem contDiffAt_objective_of_domain (H B : Matrix n n ℂ) (A : ι → Matrix n n ℂ)
    (C Q : Matrix ι ι ℝ) (θ : ℝ) {p : Space n} (hS : Domain p.2)
    (hP : Domain (product A (query C Q p))) : ContDiffAt ℂ ∞ (objective H B A C Q θ) p := by
  have hl : ContDiffAt ℂ ∞ (fun p : Space n => Matrix.trace (center H B p.1*p.2)) p :=
    (traceCLM (n := n)).contDiff.contDiffAt.comp p
      (((contDiff_center H B).contDiffAt.comp p contDiffAt_fst).mul contDiffAt_snd)
  have hq := (traceRoot_analyticAt hP).contDiffAt.comp p
    (((contDiff_product A).comp (contDiff_query C Q)).contDiffAt)
  have hr : ContDiffAt ℂ ∞ (fun p : Space n => traceRoot p.2) p :=
    (traceRoot_analyticAt hS).contDiffAt.comp p contDiffAt_snd
  exact (hl.add (contDiffAt_const.mul hq)).add (contDiffAt_const.mul hr)

theorem coefficient_real (C Q : Matrix ι ι ℝ) (t : ℝ) :
    coefficient C Q (t : ℂ)=realMatrixEmbedding (C-t^2•Q) := by
  ext i j
  simp only [coefficient,Matrix.sub_apply,Matrix.smul_apply,realMatrixEmbedding_apply,
    Complex.ofReal_sub,Complex.ofReal_mul,Complex.ofReal_pow,smul_eq_mul]

theorem square_sub_norm_le {t r : ℝ} {z : ℂ} (ht : |t| ≤ 1)
    (hr : r ≤ 1) (hz : ‖z-(t:ℂ)‖ ≤ r) : ‖z^2-(t:ℂ)^2‖ ≤ 3*r := by
  have he : z+(t:ℂ)=(z-(t:ℂ))+2*(t:ℂ) := by ring
  have hs : ‖z+(t:ℂ)‖ ≤ 3 := by
    rw [he]
    have hn := norm_add_le (z-(t:ℂ)) (2*(t:ℂ))
    simp only [norm_mul,Complex.norm_real,Real.norm_eq_abs] at hn
    norm_num at hn
    linarith
  rw [sq_sub_sq,norm_mul]
  exact mul_le_mul hs hz (norm_nonneg _) (by norm_num)

theorem coefficient_sub_norm_le (C Q : Matrix ι ι ℝ) (hQ : ‖realMatrixEmbedding Q‖ ≤ 1)
    {t r : ℝ} {z : ℂ} (ht : |t| ≤ 1) (hr : r ≤ 1) (hz : ‖z-(t:ℂ)‖ ≤ r) :
    ‖coefficient C Q z-realMatrixEmbedding (C-t^2•Q)‖ ≤ 3*r := by
  rw [← coefficient_real]
  have he : coefficient C Q z-coefficient C Q (t:ℂ)=-( (z^2-(t:ℂ)^2)•realMatrixEmbedding Q) := by
    unfold coefficient
    module
  rw [he,norm_neg,norm_smul]
  have hr0 : 0 ≤ r := (norm_nonneg _).trans hz
  calc _ ≤ (3*r)*1 := mul_le_mul (square_sub_norm_le ht hr hz) hQ (norm_nonneg _) (by positivity)
    _ = _ := mul_one _

theorem center_norm_le (H B : Matrix n n ℂ) {R b r t : ℝ} {z : ℂ}
    (hcenter : ‖center H B (t:ℂ)‖ ≤ R) (hB : ‖B‖ ≤ b) (hr : r ≤ 1)
    (hz : ‖z-(t:ℂ)‖ ≤ r) : ‖center H B z‖ ≤ R+b := by
  have he : center H B z=center H B (t:ℂ)+(z-(t:ℂ))•B := by unfold center; module
  rw [he]
  have hn := norm_add_le (center H B (t:ℂ)) ((z-(t:ℂ))•B)
  rw [norm_smul] at hn
  have hm := mul_le_mul (hz.trans hr) hB (norm_nonneg _) (by norm_num : (0:ℝ)≤1)
  linarith

theorem radius_pos {γ μ : ℝ} (hγ : 0 < γ) (hμ : 0 < μ) : 0 < radius γ μ :=
  div_pos (MSManuscriptComplexSourceDomain.radius_pos hγ hμ) (by norm_num)

theorem radius_le_one {γ μ : ℝ} (hγ : 0 < γ) (hγ1 : γ ≤ 1) (hμ : 0 < μ) (hμ1 : μ ≤ 1) :
    radius γ μ ≤ 1 := by
  have hh := MSManuscriptComplexValueBound.radius_le_one hγ hγ1 hμ hμ1
  unfold radius
  linarith

/-- Both source arguments stay within the proved general relative-source ball. -/
theorem query_domain (A : ι → Matrix n n ℂ) (hA : ∀i, (A i).IsHermitian)
    (C Q : Matrix ι ι ℝ) (hQ : ‖realMatrixEmbedding Q‖ ≤ 1)
    {S : Matrix n n ℂ} {t γ μ : ℝ} (ht : |t| ≤ 1)
    (hγ : 0 < γ) (hγ1 : γ ≤ 1) (hμ : 0 < μ) (hμ1 : μ ≤ 1)
    (hC : γ•(1 : Matrix ι ι ℝ) ≤ C-t^2•Q) (hS : μ•(1 : Matrix n n ℂ) ≤ S)
    (p : Space n) (hp : p ∈ ball ((t:ℂ),S) (radius γ μ)) :
    Domain p.2 ∧ Domain (product A (query C Q p)) := by
  have hn : ‖p-((t:ℂ),S)‖ < radius γ μ := by simpa only [mem_ball,dist_eq_norm] using hp
  have ht' : ‖p.1-(t:ℂ)‖ ≤ radius γ μ := (le_max_left _ _).trans hn.le
  have hs' : ‖p.2-S‖ ≤ radius γ μ := (le_max_right _ _).trans hn.le
  have hr := radius_pos hγ hμ
  have hc := coefficient_sub_norm_le C Q hQ ht (radius_le_one hγ hγ1 hμ hμ1) ht'
  have hcb : ‖coefficient C Q p.1-realMatrixEmbedding (C-t^2•Q)‖ ≤ MSManuscriptComplexSourceDomain.radius γ μ := by
    unfold radius at hc hr
    linarith
  have hsb : ‖p.2-S‖ ≤ MSManuscriptComplexSourceDomain.radius γ μ := by
    unfold radius at hs' hr
    linarith
  exact ⟨density_domain hγ1 hμ hS hsb,
    product_domain A hA hγ hγ1 hμ hμ1 hC hS (query C Q p) hcb hsb⟩

/-- The actual matched objective is complex smooth on the stated ball. -/
theorem contDiffOn_objective (H B : Matrix n n ℂ) (A : ι → Matrix n n ℂ)
    (hA : ∀i, (A i).IsHermitian) (C Q : Matrix ι ι ℝ) (hQ : ‖realMatrixEmbedding Q‖ ≤ 1) (θ : ℝ)
    {S : Matrix n n ℂ} {t γ μ : ℝ} (ht : |t| ≤ 1)
    (hγ : 0 < γ) (hγ1 : γ ≤ 1) (hμ : 0 < μ) (hμ1 : μ ≤ 1)
    (hC : γ•(1 : Matrix ι ι ℝ) ≤ C-t^2•Q) (hS : μ•(1 : Matrix n n ℂ) ≤ S) :
    ContDiffOn ℂ ∞ (objective H B A C Q θ) (ball ((t:ℂ),S) (radius γ μ)) := by
  intro p hp
  have hh := query_domain A hA C Q hQ ht hγ hγ1 hμ hμ1 hC hS p hp
  exact (contDiffAt_objective_of_domain H B A C Q θ hh.1 hh.2).contDiffWithinAt

/-- On real data the extension is the actual matched ownerObjective. -/
theorem objective_real (H B : Matrix n n ℂ) (hH : H.IsHermitian) (hB : B.IsHermitian)
    (A : ι → Matrix n n ℂ) (hA : ∀i, (A i).IsHermitian) (C Q : Matrix ι ι ℝ) (θ t : ℝ)
    {S : Matrix n n ℂ} (hC : (C-t^2•Q).PosDef) (hS : S.PosDef) :
    objective H B A C Q θ ((t:ℂ),S) = (ownerObjective (H+t•B) A (C-t^2•Q) θ S : ℂ) := by
  have he : center H B (t:ℂ)=H+t•B := by
    ext i j
    simp only [center,Matrix.add_apply,Matrix.smul_apply]
    rfl
  change MSManuscriptComplexObjective.objective (center H B (t:ℂ)) A θ (coefficient C Q (t:ℂ),S)=_
  rw [he,coefficient_real]
  have hHB : (H+t•B).IsHermitian := by
    change Hᴴ=H at hH
    change Bᴴ=B at hB
    simp only [Matrix.IsHermitian,Matrix.conjTranspose_add,Matrix.conjTranspose_smul,hH,hB,star_trivial]
  exact MSManuscriptComplexObjective.objective_real (H+t•B) hHB A hA θ hC hS

end MatrixSpencer.MSManuscriptMatchedComplex
