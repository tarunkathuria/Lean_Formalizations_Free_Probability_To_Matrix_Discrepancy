import MatrixSpencer.KSEighthSmoothness
import MatrixSpencer.KSComplexTraceValueBound

/-!
# The actual independent eighth-cube source as a trace source

Each original coefficient owns both independent sign blocks. The duplicated
index here labels source summands, not independently signed walk coordinates.
The canonical support is used only in the analytic proof.
-/

open Matrix
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator ContDiff
noncomputable section
namespace MatrixSpencer.KSEighthTraceSource

variable {ι n : Type*} [Fintype ι] [DecidableEq ι] [Fintype n] [DecidableEq n]
local instance {k : Type*} [Fintype k] [DecidableEq k] : CStarAlgebra (Matrix k k ℂ) := {}

def liftedVector (v : ι → n → ℂ) (j : ι × Bool) : n ⊕ n → ℂ :=
  if j.2 then Sum.elim (v j.1) (fun _ => 0) else Sum.elim (fun _ => 0) (v j.1)

theorem family_eq_atom (v : ι → n → ℂ) (j : ι × Bool) :
    KSEighthActualState.family v j = KSRankOne.atom (liftedVector v j) := by
  rcases j with ⟨i,b⟩
  cases b <;> ext a c <;> cases a <;> cases c <;>
    simp [KSEighthActualState.family, KSIndependentSource.family, liftedVector,
      leftDensity, rightDensity, KSRankOne.atom, Matrix.vecMulVec]

theorem family_posSemidef (v : ι → n → ℂ) (j : ι × Bool) :
    (KSEighthActualState.family v j).PosSemidef := by
  rw [family_eq_atom]
  exact KSRankOne.atom_posSemidef _

def owners (x : ι → ℝ) : ι × Bool → ℝ := fun j => x j.1

theorem source_real (v : ι → n → ℂ) (x h : ι → ℝ) (t : ℝ)
    (S : Matrix (n ⊕ n) (n ⊕ n) ℂ) :
    KSComplexTraceSource.source (KSEighthActualState.family v) (owners x) (owners h) ((t : ℂ),S) =
      covarianceSource (KSEighthActualState.family v)
        (KSIndependentSource.coefficientCovariance (KSEighthLocalState.curveOwners x h t)) S := by
  simp only [covarianceSource, KSIndependentSource.coefficientCovariance,
    Matrix.diagonal_apply, ite_smul, zero_smul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  unfold KSComplexTraceSource.source
  apply Finset.sum_congr rfl
  intro j _
  rw [family_eq_atom, KSRankOne.atom_sandwich]
  ext a b
  simp only [owners, KSEighthLocalState.curveOwners, Matrix.smul_apply, smul_eq_mul,
    Complex.real_smul, Complex.ofReal_mul, Complex.ofReal_sub, Complex.ofReal_add,
    Complex.ofReal_pow, Complex.ofReal_one, Complex.ofReal_ofNat]
  ring

abbrev Support (v : ι → n → ℂ) :=
  Fin (Module.finrank ℂ (krausSupport (KSEighthActualState.family v)))

def frame (v : ι → n → ℂ) : Matrix (n ⊕ n) (Support v) ℂ :=
  krausSupportEmbedding (KSEighthActualState.family v)

theorem frame_isometry (v : ι → n → ℂ) : (frame v)ᴴ * frame v = 1 :=
  krausSupportEmbedding_isometry _

theorem support_card_le (v : ι → n → ℂ) : Fintype.card (Support v) ≤ Fintype.card (n ⊕ n) := by
  simpa only [Support, Fintype.card_fin, Module.finrank_pi, Module.finrank_self,
    mul_one, finrank_euclideanSpace] using Submodule.finrank_le (krausSupport (KSEighthActualState.family v))

theorem coefficient_posDef (x h : ι → ℝ) (t : ℝ)
    (hx : ∀ i, |x i+t*h i| < 1) :
    (KSIndependentSource.coefficientCovariance (KSEighthLocalState.curveOwners x h t)).PosDef := by
  apply Matrix.posDef_diagonal_iff.mpr
  intro j
  change 0 < 64 * (1-(x j.1+t*h j.1)^2)
  have hh := (sq_lt_one_iff_abs_lt_one _).mpr (hx j.1)
  exact mul_pos (by norm_num) (sub_pos.mpr hh)

theorem compressedSource_posDef (v : ι → n → ℂ) (x h : ι → ℝ) (t : ℝ)
    {S : Matrix (n ⊕ n) (n ⊕ n) ℂ} (hS : S.PosDef)
    (hx : ∀ i, |x i+t*h i| < 1) :
    (KSComplexTraceDomain.compressedSource (frame v) (KSEighthActualState.family v)
      (owners x) (owners h) ((t : ℂ),S)).PosDef := by
  unfold KSComplexTraceDomain.compressedSource
  rw [source_real]
  exact covarianceCompressedSource_posDef _ (fun j => (family_posSemidef v j).isHermitian)
    (coefficient_posDef x h t hx) hS

theorem source_reconstruct (v : ι → n → ℂ) (x h : ι → ℝ) (t : ℝ)
    {S : Matrix (n ⊕ n) (n ⊕ n) ℂ} (hS : S.PosDef)
    (hx : ∀ i, |x i+t*h i| < 1) :
    frame v * KSComplexTraceDomain.compressedSource (frame v) (KSEighthActualState.family v)
      (owners x) (owners h) ((t : ℂ),S) * (frame v)ᴴ =
      KSComplexTraceSource.source (KSEighthActualState.family v) (owners x) (owners h) ((t : ℂ),S) := by
  unfold KSComplexTraceDomain.compressedSource KSSupportSymmetry.compress
  rw [source_real]
  have hl := covarianceSource_fixed_projection_left _ (fun j => (family_posSemidef v j).isHermitian)
    (coefficient_posDef x h t hx) hS
  have hr := covarianceSource_fixed_projection_right _ (fun j => (family_posSemidef v j).isHermitian)
    (coefficient_posDef x h t hx) hS
  let T := covarianceSource (KSEighthActualState.family v)
    (KSIndependentSource.coefficientCovariance (KSEighthLocalState.curveOwners x h t)) S
  change frame v * ((frame v)ᴴ * T * frame v) * (frame v)ᴴ = T
  calc _ = (frame v * (frame v)ᴴ) * T * (frame v * (frame v)ᴴ) := by simp only [Matrix.mul_assoc]
    _ = T := by dsimp only [frame,T]; rw [hl,hr]

end MatrixSpencer.KSEighthTraceSource
