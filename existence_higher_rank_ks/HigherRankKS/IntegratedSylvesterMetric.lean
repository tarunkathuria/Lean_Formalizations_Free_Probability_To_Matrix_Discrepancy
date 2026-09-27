import HigherRankKS.SylvesterMetric
import MatrixSpencer.TsallisHessian
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# Integrated cross-Gram control of inverse-Sylvester energy

The column parameter may belong to any measure space.  We integrate the
finite rectangular completed-square inequality directly.  Only the matrix
Gram output, its Hermitian cross output, and the scalar squared column size
must be integrable; no infinite-dimensional row-operator construction is
needed.
-/

open Matrix MatrixSpencer MeasureTheory
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator

noncomputable section
namespace HigherRankKS.IntegratedSylvesterMetric

open SylvesterMetric

variable {n m T : Type*} [Fintype n] [DecidableEq n] [Fintype m]
  [MeasurableSpace T]

/-- A fixed output test acts continuously and real-linearly on the cross
output. -/
def linearTest (Y : Matrix n n ℂ) : Matrix n n ℂ →L[ℝ] ℝ :=
  realTraceCLM.comp ((LinearMap.mulRight ℝ Y).toContinuousLinearMap)

omit [DecidableEq n] in
@[simp] theorem linearTest_apply (Y R : Matrix n n ℂ) :
    linearTest Y R = realTrace (R * Y) := rfl

/-- The quadratic test is linear in the Sylvester weight. -/
def weightTest (Y : Matrix n n ℂ) : Matrix n n ℂ →L[ℝ] ℝ :=
  realTraceCLM.comp (((LinearMap.mulLeft ℝ Y).comp
    (LinearMap.mulRight ℝ Y + LinearMap.mulLeft ℝ Y)).toContinuousLinearMap)

omit [DecidableEq n] in
@[simp] theorem weightTest_apply (Y W : Matrix n n ℂ) :
    weightTest Y W = realTrace (Y * sylvester W Y) := rfl

/-- Real-linear conjugate transpose, used to preserve Hermitian symmetry
under the actual Bochner integral. -/
def adjointMap : Matrix n n ℂ →L[ℝ] Matrix n n ℂ :=
  ({ toFun := Matrix.conjTranspose
     map_add' := Matrix.conjTranspose_add
     map_smul' := by intro r A; simp } : Matrix n n ℂ →ₗ[ℝ] Matrix n n ℂ).toContinuousLinearMap

omit [DecidableEq n] in
@[simp] theorem adjointMap_apply (A : Matrix n n ℂ) : adjointMap A = Aᴴ := rfl

theorem integral_isHermitian (μ : Measure T) (R : T → Matrix n n ℂ)
    (hR : Integrable R μ) (hHermitian : ∀ᵐ t ∂μ, (R t).IsHermitian) :
    (∫ t, R t ∂μ).IsHermitian := by
  have hi := (adjointMap (n := n)).integral_comp_comm hR
  have heq : (∫ t, adjointMap (R t) ∂μ) = ∫ t, R t ∂μ := by
    apply integral_congr_ae
    filter_upwards [hHermitian] with t ht
    exact ht.eq
  change (∫ t, R t ∂μ)ᴴ = ∫ t, R t ∂μ
  exact hi.symm.trans heq

theorem integrable_variational (μ : Measure T) (W R : T → Matrix n n ℂ)
    (hW : Integrable W μ) (hR : Integrable R μ) (Y : Matrix n n ℂ) :
    Integrable (fun t => variational (W t) (R t) Y) μ :=
  ((linearTest Y).integrable_comp hR |>.const_mul 2).sub ((weightTest Y).integrable_comp hW)

/-- A fixed variational test commutes with integration of both of its
matrix inputs. -/
theorem variational_integral (μ : Measure T) (W R : T → Matrix n n ℂ)
    (hW : Integrable W μ) (hR : Integrable R μ) (Y : Matrix n n ℂ) :
    variational (∫ t, W t ∂μ) (∫ t, R t ∂μ) Y =
      ∫ t, variational (W t) (R t) Y ∂μ := by
  change 2 * linearTest Y (∫ t, R t ∂μ) - weightTest Y (∫ t, W t ∂μ) =
    ∫ t, 2 * linearTest Y (R t) - weightTest Y (W t) ∂μ
  rw [integral_sub ((linearTest Y).integrable_comp hR |>.const_mul 2)
      ((weightTest Y).integrable_comp hW), integral_const_mul,
    (linearTest Y).integral_comp_comm hR, (weightTest Y).integral_comp_comm hW]

/-- Integrated rectangular completed-square upper bound for every
Hermitian test matrix. -/
theorem integrated_crossGram_variational_le (μ : Measure T)
    (A B : T → Matrix n m ℂ)
    (hA : Integrable (fun t => A t * (A t)ᴴ) μ)
    (hR : Integrable (fun t => A t * (B t)ᴴ + B t * (A t)ᴴ) μ)
    (hB : Integrable (fun t => realTrace (B t * (B t)ᴴ)) μ)
    {Y : Matrix n n ℂ} (hY : Y.IsHermitian) :
    variational (∫ t, A t * (A t)ᴴ ∂μ)
      (∫ t, A t * (B t)ᴴ + B t * (A t)ᴴ ∂μ) Y ≤
        2 * ∫ t, realTrace (B t * (B t)ᴴ) ∂μ := by
  rw [variational_integral μ _ _ hA hR Y]
  calc
    (∫ t, variational (A t * (A t)ᴴ) (A t * (B t)ᴴ + B t * (A t)ᴴ) Y ∂μ) ≤
        ∫ t, 2 * realTrace (B t * (B t)ᴴ) ∂μ :=
      integral_mono (integrable_variational μ _ _ hA hR Y) (hB.const_mul 2)
        (fun t => crossGram_variational_le (A t) (B t) hY)
    _ = _ := integral_const_mul 2 _

/-- The cross-Gram estimate for measure-indexed rectangular columns and
the actual inverse Sylvester operator.  Integrability and positive
definiteness are explicit; no source-response estimate is assumed. -/
theorem integrated_crossGram_energy_le (μ : Measure T)
    (A B : T → Matrix n m ℂ)
    (hA : Integrable (fun t => A t * (A t)ᴴ) μ)
    (hR : Integrable (fun t => A t * (B t)ᴴ + B t * (A t)ᴴ) μ)
    (hB : Integrable (fun t => realTrace (B t * (B t)ᴴ)) μ)
    (hW : (∫ t, A t * (A t)ᴴ ∂μ).PosDef) :
    energy (∫ t, A t * (A t)ᴴ ∂μ) hW
      (∫ t, A t * (B t)ᴴ + B t * (A t)ᴴ ∂μ) ≤
        2 * ∫ t, realTrace (B t * (B t)ᴴ) ∂μ := by
  have hHermitian : (∫ t, A t * (B t)ᴴ + B t * (A t)ᴴ ∂μ).IsHermitian := by
    apply integral_isHermitian μ _ hR
    filter_upwards [] with t
    change (A t * (B t)ᴴ + B t * (A t)ᴴ)ᴴ = A t * (B t)ᴴ + B t * (A t)ᴴ
    simp only [Matrix.conjTranspose_add, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose]
    exact add_comm _ _
  rw [← variational_inverse _ hW _]
  exact integrated_crossGram_variational_le μ A B hA hR hB
    (inverse_isHermitian _ hW hHermitian)

/-- A matrix-integrable column Gram gives the equivalent formulation with
the trace taken after integration. -/
theorem integrated_crossGram_energy_le_trace_integral (μ : Measure T)
    (A B : T → Matrix n m ℂ)
    (hA : Integrable (fun t => A t * (A t)ᴴ) μ)
    (hR : Integrable (fun t => A t * (B t)ᴴ + B t * (A t)ᴴ) μ)
    (hB : Integrable (fun t => B t * (B t)ᴴ) μ)
    (hW : (∫ t, A t * (A t)ᴴ ∂μ).PosDef) :
    energy (∫ t, A t * (A t)ᴴ ∂μ) hW
      (∫ t, A t * (B t)ᴴ + B t * (A t)ᴴ ∂μ) ≤
        2 * realTrace (∫ t, B t * (B t)ᴴ ∂μ) := by
  have h := integrated_crossGram_energy_le μ A B hA hR
    (realTraceCLM.integrable_comp hB) hW
  have he := realTraceCLM.integral_comp_comm hB
  simpa only [realTraceCLM_apply] using h.trans_eq (congrArg (fun z : ℝ => 2 * z) he)

end HigherRankKS.IntegratedSylvesterMetric
