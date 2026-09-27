import HigherRankKS.SourceMetricAggregation
import AugmentedHigherRankKS.FourBlockProbe
import AugmentedHigherRankKS.FourBlockSupportedSource
import HigherRankKS.LinearDerivative
import Mathlib.Data.Matrix.ColumnRowPartitioned

/-!
# Concrete Kraus representation of the supported nonlinear source

The two spin outputs are represented by two rectangular maps from each
atom's fixed carrier. The maps below are constructed from the actual atom,
its carrier embedding, and the chosen supported output map.
-/

open Matrix MatrixSpencer HigherRankKS Set Filter
open scoped Topology ContDiff BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator

noncomputable section
namespace AugmentedHigherRankKS.SupportedSourceCalculus

open PowerGramMetric

variable {n m : Type*} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]
local instance supportedSourceCalculusCStar {l : Type*} [Fintype l] [DecidableEq l] :
    CStarAlgebra (Matrix l l ℂ) := {}

local instance supportedSourceCalculusSpace :
    NormedSpace ℝ (selfAdjoint (Matrix (FourSpin n) (FourSpin n) ℂ)) := inferInstance

theorem dyadic_mem_Ioo (k : ℕ) (hk : 1 ≤ k) :
    (1 : ℝ) / 2 ^ k ∈ Ioo (0 : ℝ) 1 := by
  refine ⟨by positivity, ?_⟩
  exact (div_lt_one (by positivity)).2 (one_lt_pow₀ (by norm_num) (by omega))

/-- The atom-to-physical output map from its fixed carrier. -/
def atomOutput (A : Matrix n n ℂ) : Matrix n (AtomCarrierIndex A) ℂ :=
  CFC.sqrt A * atomEmbedding A

/-- The two spin columns belong to the same original matrix label. -/
def spinOutput (A : Matrix n n ℂ) : Bool × Bool → Matrix (FourSpin n) (AtomCarrierIndex A) ℂ
  | (false, false) => Matrix.fromRows (Matrix.fromRows (atomOutput A) 0) 0
  | (false, true) => Matrix.fromRows (Matrix.fromRows 0 (atomOutput A)) 0
  | (true, false) => Matrix.fromRows 0 (Matrix.fromRows (atomOutput A) 0)
  | (true, true) => Matrix.fromRows 0 (Matrix.fromRows 0 (atomOutput A))

/-- The concrete rectangular output maps after a fixed support/balance map. -/
def outputKraus (A : Matrix n n ℂ) (D : Matrix m (FourSpin n) ℂ) :
    Bool × Bool → Matrix m (AtomCarrierIndex A) ℂ := fun b => D * spinOutput A b

omit [Fintype m] [DecidableEq m] in
theorem spinOutput_apply (A : Matrix n n ℂ)
    (X : Matrix (AtomCarrierIndex A) (AtomCarrierIndex A) ℂ) :
    krausMap (spinOutput A) X = spinAtom (atomOutput A * X * (atomOutput A)ᴴ) := by
  simp only [krausMap_apply, Fintype.sum_prod_type, Fintype.sum_bool, spinOutput,
    Matrix.fromRows_mul, Matrix.conjTranspose_fromRows_eq_fromCols_conjTranspose,
    Matrix.conjTranspose_zero, Matrix.zero_mul]
  ext (i | i) (j | j) <;> cases i <;> cases j <;>
    simp [spinAtom, HigherRankKS.spinAtom]

omit [Fintype m] [DecidableEq m] in
theorem outputKraus_apply (A : Matrix n n ℂ) (D : Matrix m (FourSpin n) ℂ)
    (X : Matrix (AtomCarrierIndex A) (AtomCarrierIndex A) ℂ) :
    krausMap (outputKraus A D) X = D * krausMap (spinOutput A) X * Dᴴ := by
  simp only [krausMap_apply, outputKraus, Matrix.conjTranspose_mul,
    Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_assoc]

omit [Fintype m] [DecidableEq m] in
theorem output_carrier_eq (A : Matrix n n ℂ) (D : Matrix m (FourSpin n) ℂ)
    (k : ℕ) (hk : 1 ≤ k) (S : selfAdjoint (Matrix (FourSpin n) (FourSpin n) ℂ))
    (hS : (S : Matrix (FourSpin n) (FourSpin n) ℂ).PosSemidef) :
    krausMap (outputKraus A D)
      (CarrierMetric.carrier ((1 : ℝ) / 2 ^ k) (compressedCarrierCLM A S)) =
      D * sourceTerm ((1 : ℝ) / 2 ^ k) A (S : Matrix (FourSpin n) (FourSpin n) ℂ) * Dᴴ := by
  rw [outputKraus_apply, spinOutput_apply]
  have he : atomOutput A * CarrierMetric.carrier ((1 : ℝ) / 2 ^ k)
      (compressedCarrierCLM A S) * (atomOutput A)ᴴ =
      sourceBlock ((1 : ℝ) / 2 ^ k) A (S : Matrix (FourSpin n) (FourSpin n) ℂ) := by
    change CFC.sqrt A * atomEmbedding A * _ * _ = CFC.sqrt A * carrierPower _ (carrier A S) * CFC.sqrt A
    rw [carrierPower_reconstruct A hS k hk]
    simp only [atomOutput, CarrierMetric.carrier, compressedCarrierCLM_coe,
      Matrix.conjTranspose_mul, (CFC.sqrt_nonneg A).posSemidef.isHermitian.eq,
      Matrix.mul_assoc]
  rw [he]
  rfl

/-- A fixed rectangular output applied to the actual physical source. -/
def sourceOutput (A : Matrix n n ℂ) (D : Matrix m (FourSpin n) ℂ) (β : ℝ)
    (S : selfAdjoint (Matrix (FourSpin n) (FourSpin n) ℂ)) : Matrix m m ℂ :=
  D * sourceTerm β A (S : Matrix (FourSpin n) (FourSpin n) ℂ) * Dᴴ

omit [Fintype m] [DecidableEq m] in
theorem sourceOutput_eventuallyEq (A : Matrix n n ℂ) (D : Matrix m (FourSpin n) ℂ)
    (k : ℕ) (hk : 1 ≤ k) (S : selfAdjoint (Matrix (FourSpin n) (FourSpin n) ℂ))
    (hS : (S : Matrix (FourSpin n) (FourSpin n) ℂ).PosDef) :
    sourceOutput A D ((1 : ℝ) / 2 ^ k) =ᶠ[𝓝 S]
      (fun T => krausMap (outputKraus A D)
        (CarrierMetric.carrier ((1 : ℝ) / 2 ^ k) (compressedCarrierCLM A T))) := by
  filter_upwards [eventually_posDef_of_posDef S hS] with T hT
  exact (output_carrier_eq A D k hk T hT.posSemidef).symm

/-- Actual first derivative of the physical output, on the positive face. -/
theorem sourceOutput_first (A : Matrix n n ℂ) (D : Matrix m (FourSpin n) ℂ)
    (k : ℕ) (hk : 1 ≤ k) (S U : selfAdjoint (Matrix (FourSpin n) (FourSpin n) ℂ))
    (hS : (S : Matrix (FourSpin n) (FourSpin n) ℂ).PosDef) :
    fderiv ℝ (sourceOutput A D ((1 : ℝ) / 2 ^ k)) S U =
      krausMap (outputKraus A D) (CarrierMetric.first ((1 : ℝ) / 2 ^ k)
        (compressedCarrierCLM A S) (compressedCarrierCLM A U)) := by
  rw [(sourceOutput_eventuallyEq A D k hk S hS).fderiv_eq]
  apply LinearDerivative.first
  exact (CarrierMetric.smooth (dyadic_mem_Ioo k hk) _
    (by simpa only [compressedCarrierCLM_coe] using compressedCarrier_posDef A hS)).differentiableAt
      (by simp)

/-- Actual diagonal Hessian of the physical output. -/
theorem sourceOutput_second (A : Matrix n n ℂ) (D : Matrix m (FourSpin n) ℂ)
    (k : ℕ) (hk : 1 ≤ k) (S U : selfAdjoint (Matrix (FourSpin n) (FourSpin n) ℂ))
    (hS : (S : Matrix (FourSpin n) (FourSpin n) ℂ).PosDef) :
    fderiv ℝ (fderiv ℝ (sourceOutput A D ((1 : ℝ) / 2 ^ k))) S U U =
      krausMap (outputKraus A D) (CarrierMetric.second ((1 : ℝ) / 2 ^ k)
        (compressedCarrierCLM A S) (compressedCarrierCLM A U) (compressedCarrierCLM A U)) := by
  rw [((sourceOutput_eventuallyEq A D k hk S hS).fderiv (𝕜 := ℝ)).fderiv_eq]
  apply LinearDerivative.second
  exact (CarrierMetric.smooth (dyadic_mem_Ioo k hk) _
    (by simpa only [compressedCarrierCLM_coe] using compressedCarrier_posDef A hS)).of_le
      (WithTop.coe_le_coe.mpr le_top)

theorem sourceOutput_smooth (A : Matrix n n ℂ) (D : Matrix m (FourSpin n) ℂ)
    (k : ℕ) (hk : 1 ≤ k) (S : selfAdjoint (Matrix (FourSpin n) (FourSpin n) ℂ))
    (hS : (S : Matrix (FourSpin n) (FourSpin n) ℂ).PosDef) :
    ContDiffAt ℝ ∞ (sourceOutput A D ((1 : ℝ) / 2 ^ k)) S :=
  (sandwich D).contDiff.contDiffAt.comp S (contDiffAt_sourceTerm A k hk S hS)

/-- Balancing also commutes with the physical source derivative. -/
theorem sourceOutput_first_physical (A : Matrix n n ℂ) (D : Matrix m (FourSpin n) ℂ)
    (k : ℕ) (hk : 1 ≤ k) (S U : selfAdjoint (Matrix (FourSpin n) (FourSpin n) ℂ))
    (hS : (S : Matrix (FourSpin n) (FourSpin n) ℂ).PosDef) :
    fderiv ℝ (sourceOutput A D ((1 : ℝ) / 2 ^ k)) S U =
      D * fderiv ℝ (SourceDerivatives.term ((1 : ℝ) / 2 ^ k) A) S U * Dᴴ := by
  exact LinearDerivative.first (ContinuousLinearMap.id ℝ _) (sandwich D)
    (SourceDerivatives.term ((1 : ℝ) / 2 ^ k) A) S U
    ((contDiffAt_sourceTerm A k hk S hS).differentiableAt (by simp))

/-- Balancing commutes with the physical source Hessian. -/
theorem sourceOutput_second_physical (A : Matrix n n ℂ) (D : Matrix m (FourSpin n) ℂ)
    (k : ℕ) (hk : 1 ≤ k) (S U : selfAdjoint (Matrix (FourSpin n) (FourSpin n) ℂ))
    (hS : (S : Matrix (FourSpin n) (FourSpin n) ℂ).PosDef) :
    fderiv ℝ (fderiv ℝ (sourceOutput A D ((1 : ℝ) / 2 ^ k))) S U U =
      D * fderiv ℝ (fderiv ℝ (SourceDerivatives.term ((1 : ℝ) / 2 ^ k) A)) S U U * Dᴴ := by
  exact LinearDerivative.second (ContinuousLinearMap.id ℝ _) (sandwich D)
    (SourceDerivatives.term ((1 : ℝ) / 2 ^ k) A) S U
    ((contDiffAt_sourceTerm A k hk S hS).of_le (WithTop.coe_le_coe.mpr le_top))

omit [Fintype m] [DecidableEq m] in
/-- The carrier mass identity holds in every Hermitian direction. -/
theorem realTrace_compressedCarrier_direction (A : Matrix n n ℂ) (hA : A.PosSemidef)
    (S U : selfAdjoint (Matrix (FourSpin n) (FourSpin n) ℂ))
    (hS : (S : Matrix (FourSpin n) (FourSpin n) ℂ).PosDef) :
    realTrace (compressedCarrierCLM A U :
      Matrix (AtomCarrierIndex A) (AtomCarrierIndex A) ℂ) =
      realTrace (spinAtom A * (U : Matrix (FourSpin n) (FourSpin n) ℂ)) := by
  let L := (realTraceCLM (n := AtomCarrierIndex A)).comp
    ((hermitianInclusion (n := AtomCarrierIndex A)).comp (compressedCarrierCLM A))
  let R := (SourceDerivative.traceProbeCLM (spinAtom A)).comp
    (hermitianInclusion (n := FourSpin n))
  have he : (fun T => L T) =ᶠ[𝓝 S] (fun T => R T) := by
    filter_upwards [eventually_posDef_of_posDef S hS] with T hT
    simpa only [L, R, ContinuousLinearMap.comp_apply, realTraceCLM_apply,
      hermitianInclusion_apply, SourceDerivative.traceProbeCLM_apply, compressedCarrierCLM_coe] using
      SourceDerivative.realTrace_compressedCarrier A hA hT.posSemidef
  have hd := he.fderiv_eq (𝕜 := ℝ)
  rw [L.hasFDerivAt.fderiv, R.hasFDerivAt.fderiv] at hd
  exact DFunLike.congr_fun hd U

omit [Fintype m] [DecidableEq m] in
theorem atomCarrier_nonempty {A : Matrix n n ℂ} (hA : A.PosSemidef) (hne : A ≠ 0) :
    Nonempty (AtomCarrierIndex A) := by
  by_contra hn
  haveI : IsEmpty (AtomCarrierIndex A) := not_nonempty_iff.mp hn
  have hz : atomEmbedding A * compressedAtom A * (atomEmbedding A)ᴴ = 0 := by
    ext i j
    simp [Matrix.mul_apply]
  exact hne ((atom_reconstruct hA).symm.trans hz)

end AugmentedHigherRankKS.SupportedSourceCalculus
