import MatrixSpencer.MSManuscriptComplexSourceDomain
import MatrixSpencer.KSHolomorphicFidelity
import MatrixSpencer.KSComplexOwnerPerturbation

/-!
# Actual holomorphic objective for a general covariance source

The coefficient matrix and density matrix are complex coordinates. The
extension uses the proved fixed-support trace-root domain for the actual
bilinear Kraus source. On positive real covariance/density data it agrees
exactly with the original ownerObjective, including singular physical sources.
-/

open Matrix Set Metric
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator ContDiff
noncomputable section
namespace MatrixSpencer.MSManuscriptComplexObjective
open MSManuscriptComplexCovarianceSource MSManuscriptComplexSourceDomain KSCompactResolvent
variable {ι n : Type*} [Fintype ι] [DecidableEq ι] [Fintype n] [DecidableEq n]
local instance {k : Type*} [Fintype k] [DecidableEq k] : CStarAlgebra (Matrix k k ℂ) := {}

abbrev Space (ι n : Type*) := Matrix ι ι ℂ × Matrix n n ℂ
abbrev Support (A : ι → Matrix n n ℂ) := Fin (Module.finrank ℂ (krausSupport A))

def compression (A : ι → Matrix n n ℂ) (S : Matrix n n ℂ) : Matrix (Support A) (Support A) ℂ :=
  (krausSupportEmbedding A)ᴴ*S*krausSupportEmbedding A

def compressionCLM (A : ι → Matrix n n ℂ) : Matrix n n ℂ →L[ℂ] Matrix (Support A) (Support A) ℂ :=
  LinearMap.toContinuousLinearMap
    { toFun := compression A
      map_add' := by intro X Y; simp only [compression,Matrix.mul_add,Matrix.add_mul]
      map_smul' := by intro a X; simp only [compression,Matrix.mul_smul,Matrix.smul_mul,RingHom.id_apply] }

def product (A : ι → Matrix n n ℂ) (p : Space ι n) : Matrix (Support A) (Support A) ℂ :=
  compression A p.2*compression A (source A p.1 p.2)

def objective (H : Matrix n n ℂ) (A : ι → Matrix n n ℂ) (θ : ℝ) (p : Space ι n) : ℂ :=
  Matrix.trace (H*p.2)+2*traceRoot (product A p)+2*(θ:ℂ)*traceRoot p.2

theorem contDiff_product (A : ι → Matrix n n ℂ) : ContDiff ℂ ∞ (product A) :=
  ((compressionCLM A).contDiff.comp contDiff_snd).mul
    ((compressionCLM A).contDiff.comp (MSManuscriptComplexSourcePerturbation.contDiff_source A))

theorem contDiffAt_objective_of_domain (H : Matrix n n ℂ) (A : ι → Matrix n n ℂ) (θ : ℝ)
    {p : Space ι n} (hS : Domain p.2) (hp : Domain (product A p)) :
    ContDiffAt ℂ ∞ (objective H A θ) p := by
  have hl : ContDiffAt ℂ ∞ (fun q : Space ι n => Matrix.trace (H*q.2)) p :=
    (traceCLM (n := n)).contDiff.contDiffAt.comp p (contDiffAt_const.mul contDiffAt_snd)
  have hq := (traceRoot_analyticAt hp).contDiffAt.comp p (contDiff_product A).contDiffAt
  have hr : ContDiffAt ℂ ∞ (fun p : Space ι n => traceRoot p.2) p :=
    (traceRoot_analyticAt hS).contDiffAt.comp p contDiffAt_snd
  exact (hl.add (contDiffAt_const.mul hq)).add (contDiffAt_const.mul hr)

theorem density_domain {S₀ S : Matrix n n ℂ} {γ μ : ℝ}
    (hγ1 : γ ≤ 1) (hμ : 0 < μ) (hfloor : μ • (1 : Matrix n n ℂ) ≤ S₀)
    (hS : ‖S-S₀‖ ≤ radius γ μ) : Domain S := by
  have hnorm : ‖S-S₀‖ < μ := by
    have hr := radius_le_density hμ.le hγ1
    linarith
  have he : S₀+(S-S₀)=S := by abel
  have ha := KSComplexSpinDomain.density_strictAccretive hfloor hnorm
  rw [he] at ha
  have hi : KSAccretiveProductDomain.StrictAccretive (1 : Matrix n n ℂ) := by
    simpa only [add_zero] using KSAccretiveProductDomain.one_add_strictAccretive
      (show ‖(0 : Matrix n n ℂ)‖<1 by simp)
  simpa only [Matrix.mul_one] using KSAccretiveProductDomain.product_spectrum_subset_slitPlane ha hi

/-- The full complex coefficient/density ball is in the actual product domain. -/
theorem product_domain (A : ι → Matrix n n ℂ) (hA : ∀i, (A i).IsHermitian)
    {C₀ : Matrix ι ι ℝ} {S₀ : Matrix n n ℂ} {γ μ : ℝ}
    (hγ : 0 < γ) (hγ1 : γ ≤ 1) (hμ : 0 < μ) (hμ1 : μ ≤ 1)
    (hC : γ • (1 : Matrix ι ι ℝ) ≤ C₀) (hS : μ • (1 : Matrix n n ℂ) ≤ S₀)
    (p : Space ι n) (hpc : ‖p.1-realMatrixEmbedding C₀‖ ≤ radius γ μ)
    (hps : ‖p.2-S₀‖ ≤ radius γ μ) : Domain (product A p) := by
  have hh := actual_product_spectrum_subset_slitPlane A hA hγ hγ1 hμ hμ1 hC hS hpc hps
  have heC : realMatrixEmbedding C₀+(p.1-realMatrixEmbedding C₀)=p.1 := by abel
  have heS : S₀+(p.2-S₀)=p.2 := by abel
  dsimp only at hh
  rw [heC,heS] at hh
  exact hh

/-- Every analytic premise is discharged from the original coefficient and density floors. -/
theorem contDiffOn_objective (H : Matrix n n ℂ) (A : ι → Matrix n n ℂ)
    (hA : ∀i, (A i).IsHermitian) (θ : ℝ) {C₀ : Matrix ι ι ℝ} {S₀ : Matrix n n ℂ} {γ μ : ℝ}
    (hγ : 0 < γ) (hγ1 : γ ≤ 1) (hμ : 0 < μ) (hμ1 : μ ≤ 1)
    (hC : γ • (1 : Matrix ι ι ℝ) ≤ C₀) (hS : μ • (1 : Matrix n n ℂ) ≤ S₀) :
    ContDiffOn ℂ ∞ (objective H A θ) (ball (realMatrixEmbedding C₀,S₀) (radius γ μ)) := by
  intro p hp
  have hn : ‖p-(realMatrixEmbedding C₀,S₀)‖ < radius γ μ := by
    simpa only [mem_ball,dist_eq_norm] using hp
  have hc : ‖p.1-realMatrixEmbedding C₀‖ ≤ radius γ μ := (le_max_left _ _).trans hn.le
  have hs : ‖p.2-S₀‖ ≤ radius γ μ := (le_max_right _ _).trans hn.le
  exact (contDiffAt_objective_of_domain H A θ (density_domain hγ1 hμ hS hs)
    (product_domain A hA hγ hγ1 hμ hμ1 hC hS p hc hs)).contDiffWithinAt

/-- Exact agreement with the real owner objective; no full-source invertibility is assumed. -/
theorem objective_real (H : Matrix n n ℂ) (hH : H.IsHermitian)
    (A : ι → Matrix n n ℂ) (hA : ∀i, (A i).IsHermitian) (θ : ℝ)
    {C : Matrix ι ι ℝ} (hC : C.PosDef) {S : Matrix n n ℂ} (hS : S.PosDef) :
    objective H A θ (realMatrixEmbedding C,S) = (ownerObjective H A C θ S : ℂ) := by
  have hp : product A (realMatrixEmbedding C,S) = krausCompressedDensity A S*covarianceCompressedSource A C S := by
    unfold product
    change compression A S*compression A (source A (fun i j => (C i j : ℂ)) S) = _
    rw [source_real]
    rfl
  rw [objective,KSComplexOwnerPerturbation.trace_pairing_real H S hH hS.isHermitian,hp,
    KSHolomorphicFidelity.traceRoot_covariance_eq_fidelity A hA hC hS,KSHolomorphicFidelity.traceRoot_posDef hS]
  simp only [ownerObjective,Complex.ofReal_add,Complex.ofReal_mul,Complex.ofReal_ofNat]

end MatrixSpencer.MSManuscriptComplexObjective
