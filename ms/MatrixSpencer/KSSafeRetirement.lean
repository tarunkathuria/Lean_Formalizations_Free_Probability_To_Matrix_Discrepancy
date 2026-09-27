import MatrixSpencer.KSRankOne
import MatrixSpencer.OwnerBounds
import MatrixSpencer.OptimizerResponseUnrestricted

/-!
# Frozen-transport comparisons for singular physical sources

All transports below live on the old physical source support. Their linear
majorants act on the full physical density, so a frozen center may mix the
source support with its complement.
-/

open Matrix Filter Topology
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator ContDiff

noncomputable section
namespace MatrixSpencer.KSSafeRetirement

variable {ι κ n m : Type*} [Fintype ι] [Fintype κ] [Fintype n] [Fintype m]
  [DecidableEq n] [DecidableEq m]

local instance retirementCStar {s : Type*} [Fintype s] [DecidableEq s] :
    CStarAlgebra (Matrix s s ℂ) := {}
local instance retirementNormedSpace : NormedSpace ℝ (selfAdjoint (Matrix n n ℂ)) :=
  inferInstance

def zeroKraus : Empty → Matrix n n ℂ := fun _ => 0

def baseHermitianPotential (θ : ℝ) (H : selfAdjoint (Matrix n n ℂ)) : ℝ :=
  baseDensityPotential (H : Matrix n n ℂ) θ

theorem baseHermitianPotential_eq (θ : ℝ) :
    baseHermitianPotential (n := n) θ = hermitianDensityPotential zeroKraus θ := rfl

def sourceAdjoint (B : ι → Matrix n n ℂ) (Q : Matrix n n ℂ) : Matrix n n ℂ :=
  ∑ i, (B i)ᴴ * Q * B i

theorem realTrace_sourceAdjoint (B : ι → Matrix n n ℂ) (Q X : Matrix n n ℂ) :
    realTrace (sourceAdjoint B Q * X) = realTrace (Q * krausChannel B X) := by
  simp only [sourceAdjoint, krausChannel, Matrix.sum_mul, Matrix.mul_sum,
    realTrace_sum]
  apply Finset.sum_congr rfl
  intro i _
  calc
    realTrace ((B i)ᴴ * Q * B i * X) =
        realTrace ((B i)ᴴ * (Q * B i * X)) := by simp only [Matrix.mul_assoc]
    _ = realTrace ((Q * B i * X) * (B i)ᴴ) := realTrace_mul_comm _ _
    _ = realTrace (Q * (B i * X * (B i)ᴴ)) := by simp only [Matrix.mul_assoc]

theorem realTrace_embedded_mul (V : Matrix n m ℂ) (Z : Matrix m m ℂ)
    (X : Matrix n n ℂ) :
    realTrace (V * Z * Vᴴ * X) = realTrace (Z * (Vᴴ * X * V)) := by
  calc
    _ = realTrace ((V * Z) * (Vᴴ * X)) := by simp only [Matrix.mul_assoc]
    _ = realTrace ((Vᴴ * X) * (V * Z)) := realTrace_rectangular_mul_comm _ _
    _ = realTrace ((Vᴴ * X * V) * Z) := by simp only [Matrix.mul_assoc]
    _ = _ := realTrace_mul_comm _ _

/-- Full-density linear majorant from one transport on a fixed support. -/
def supportedGradient (B : ι → Matrix n n ℂ) (V : Matrix n m ℂ)
    (Z : Matrix m m ℂ) : Matrix n n ℂ :=
  V * Z⁻¹ * Vᴴ + sourceAdjoint B (V * Z * Vᴴ)

theorem supportedGradient_pairing (B : ι → Matrix n n ℂ) (V : Matrix n m ℂ)
    (Z : Matrix m m ℂ) (X : Matrix n n ℂ) :
    realTrace (supportedGradient B V Z * X) =
      realTrace (Z⁻¹ * (Vᴴ * X * V)) +
        realTrace (Z * (Vᴴ * krausChannel B X * V)) := by
  rw [supportedGradient, Matrix.add_mul, realTrace_add,
    realTrace_sourceAdjoint, realTrace_embedded_mul]
  congr 1
  rw [← realTrace_embedded_mul, realTrace_mul_comm]

theorem supportedGradient_isHermitian (B : ι → Matrix n n ℂ) (V : Matrix n m ℂ)
    {Z : Matrix m m ℂ} (hZ : Z.IsHermitian) :
    (supportedGradient B V Z).IsHermitian := by
  apply Matrix.IsHermitian.add
  · exact Matrix.isHermitian_mul_mul_conjTranspose V hZ.inv
  · change (sourceAdjoint B (V * Z * Vᴴ))ᴴ = sourceAdjoint B (V * Z * Vᴴ)
    simp only [sourceAdjoint, Matrix.conjTranspose_sum]
    apply Finset.sum_congr rfl
    intro i _
    simpa only [Matrix.conjTranspose_conjTranspose] using
      (Matrix.isHermitian_mul_mul_conjTranspose (B i)ᴴ
        (Matrix.isHermitian_mul_mul_conjTranspose V hZ)).eq

/-- Any new source supported in the old support obeys the old transport's
full-density majorant, even when the source or test density is singular. -/
theorem fidelity_le_supportedGradient (B : ι → Matrix n n ℂ)
    (V : Matrix n m ℂ) (hV : Vᴴ * V = 1) {Z : Matrix m m ℂ} (hZ : Z.PosDef)
    {X : Matrix n n ℂ} (hX : X.PosSemidef)
    (hsupport : V * (Vᴴ * krausChannel B X * V) * Vᴴ = krausChannel B X) :
    2 * fidelity X (krausChannel B X) ≤ realTrace (supportedGradient B V Z * X) := by
  have hM : (Vᴴ * krausChannel B X * V).PosSemidef := by
    simpa only [Matrix.conjTranspose_conjTranspose] using
      (krausChannel_posSemidef B hX).mul_mul_conjTranspose_same Vᴴ
  have hS : (Vᴴ * X * V).PosSemidef := by
    simpa only [Matrix.conjTranspose_conjTranspose] using
      hX.mul_mul_conjTranspose_same Vᴴ
  have hf : fidelity X (krausChannel B X) =
      fidelity (Vᴴ * X * V) (Vᴴ * krausChannel B X * V) := by
    conv_lhs => rw [← hsupport]
    exact fidelity_isometry_compression V hV hX hM
  rw [hf, supportedGradient_pairing]
  have hb := fidelity_le_transportCost hS hM hZ
  simpa only [transportCost, realTrace_mul_comm] using hb

def actualSupportTransport (B : ι → Matrix n n ℂ) (S : Matrix n n ℂ) :=
  transportOptimizer (krausCompressedDensity B S) (krausCompressedSource B S)

def actualSupportedGradient (B : ι → Matrix n n ℂ) (S : Matrix n n ℂ) :=
  supportedGradient B (krausSupportEmbedding B) (actualSupportTransport B S)

theorem actualSupportTransport_posDef (B : ι → Matrix n n ℂ)
    {S : Matrix n n ℂ} (hS : S.PosDef) : (actualSupportTransport B S).PosDef :=
  transportOptimizer_posDef (krausCompressedDensity_posDef B hS)
    (krausCompressedSource_posDef B hS)

theorem actualSupportedGradient_pairing (B : ι → Matrix n n ℂ)
    (S : Matrix n n ℂ) (X : selfAdjoint (Matrix n n ℂ)) :
    realTrace (actualSupportedGradient B S * (X : Matrix n n ℂ)) =
      jointTransportFunctional (actualSupportTransport B S) (krausReducedPairCLM B X) := by
  rw [actualSupportedGradient, supportedGradient_pairing, jointTransportFunctional_apply]
  simp only [krausReducedPairCLM, ContinuousLinearMap.prod_apply,
    krausReducedDensityCLM_coe, krausReducedSourceCLM_coe,
    krausCompressedSource_eq_compression, krausCompressedDensity]

theorem actualSupportedGradient_contact (B : ι → Matrix n n ℂ)
    {S : Matrix n n ℂ} (hS : S.PosDef) :
    realTrace (actualSupportedGradient B S * S) = 2 * fidelity S (krausChannel B S) := by
  let S' : selfAdjoint (Matrix n n ℂ) := ⟨S, hS.isHermitian⟩
  rw [actualSupportedGradient_pairing B S S', jointTransportFunctional_eq_cost]
  simp only [krausReducedPairCLM, ContinuousLinearMap.prod_apply,
    krausReducedDensityCLM_coe, krausReducedSourceCLM_coe]
  have hd := krausCompressedDensity_posDef B hS
  have hm := krausCompressedSource_posDef B hS
  change transportCost (krausCompressedDensity B S) (krausCompressedSource B S)
    (transportOptimizer (krausCompressedDensity B S) (krausCompressedSource B S)) = _
  rw [transportCost_at_transport (transportOptimizer_posDef hd hm)
    (transportOptimizer_solve hd hm), trace_transportOptimizer_eq_fidelity hd hm,
    ← fidelity_kraus_support_compression B hS.posSemidef]

set_option maxHeartbeats 1000000 in
theorem fderiv_krausSourceFidelity_eq_supportedGradient (B : ι → Matrix n n ℂ)
    (S : selfAdjoint (Matrix n n ℂ)) (hS : (S : Matrix n n ℂ).PosDef) :
    fderiv ℝ (krausSourceFidelity B) S = tracePairing (actualSupportedGradient B S) := by
  rw [(hasFDerivAt_krausSourceFidelity_source_unrestricted B S hS).fderiv]
  have hd := krausCompressedDensity_posDef B hS
  have hm := krausCompressedSource_posDef B hS
  rw [show krausReducedPairCLM B S = (krausReducedDensityCLM B S,
    krausReducedSourceCLM B S) from rfl]
  rw [(hasFDerivAt_doubleFidelity (krausReducedDensityCLM B S)
    (krausReducedSourceCLM B S) (by simpa using hd) (by simpa using hm)).fderiv]
  simp only [krausReducedDensityCLM_coe, krausReducedSourceCLM_coe]
  ext X
  exact (actualSupportedGradient_pairing B S X).symm

theorem fderiv_base_eq_actual (H : Matrix n n ℂ) (B : ι → Matrix n n ℂ)
    (θ : ℝ) (S : selfAdjoint (Matrix n n ℂ)) (hS : (S : Matrix n n ℂ).PosDef) :
    fderiv ℝ (hermitianDensityObjective (H + actualSupportedGradient B S)
      (fun _ : Empty => (0 : Matrix n n ℂ)) θ) S =
    fderiv ℝ (hermitianDensityObjective H B θ) S := by
  have hz : krausSourceFidelity (fun _ : Empty => (0 : Matrix n n ℂ)) =
      (fun _ : selfAdjoint (Matrix n n ℂ) => (0 : ℝ)) := by
    funext X
    change 2 * fidelity (X : Matrix n n ℂ)
      (krausChannel (fun _ : Empty => (0 : Matrix n n ℂ)) (X : Matrix n n ℂ)) = 0
    simp [krausChannel, fidelity, fidelityCore]
  rw [fderiv_hermitianDensityObjective_eq_source_unrestricted _ _ _ S hS,
    fderiv_hermitianDensityObjective_eq_source_unrestricted H B θ S hS,
    fderiv_krausSourceFidelity_eq_supportedGradient B S hS, hz]
  simp only [fderiv_const_apply, map_add, add_zero]

/-- The actual optimizer also maximizes its supported-transport majorant. -/
theorem base_isMaxOn_of_actual (H : Matrix n n ℂ) (B : ι → Matrix n n ℂ)
    {θ : ℝ} (hθ : 0 < θ) (S : selfAdjoint (Matrix n n ℂ))
    (hS : (S : Matrix n n ℂ).PosDef) (ht : realTrace (S : Matrix n n ℂ) = 1)
    (hmax : ∀ T ∈ densitySet, densityObjective H B θ T ≤ densityObjective H B θ S) :
    ∀ T ∈ densitySet,
      densityObjective (H + actualSupportedGradient B S)
        (fun _ : Empty => (0 : Matrix n n ℂ)) θ T ≤
      densityObjective (H + actualSupportedGradient B S)
        (fun _ : Empty => (0 : Matrix n n ℂ)) θ S := by
  apply density_stationary_isMaxOn_source_unrestricted _ _ hθ S hS ht
  rw [fderiv_base_eq_actual H B θ S hS]
  exact density_maximizer_stationary_source_unrestricted H B θ S hS ht hmax

/-- Exact primal contact, retaining the full physical density and arbitrary
frozen center; no physical-source faithfulness hypothesis is imposed. -/
theorem basePotential_contact (H : Matrix n n ℂ) (B : ι → Matrix n n ℂ)
    {θ : ℝ} (hθ : 0 < θ) (S : selfAdjoint (Matrix n n ℂ))
    (hS : (S : Matrix n n ℂ).PosDef) (ht : realTrace (S : Matrix n n ℂ) = 1)
    (hmax : ∀ T ∈ densitySet, densityObjective H B θ T ≤ densityObjective H B θ S) :
    baseDensityPotential (H + actualSupportedGradient B S) θ = densityPotential H B θ := by
  rw [baseDensityPotential,
    densityPotential_eq_of_maximizer _ _ _ ⟨hS.posSemidef, ht⟩
      (base_isMaxOn_of_actual H B hθ S hS ht hmax),
    densityPotential_eq_of_maximizer H B θ ⟨hS.posSemidef, ht⟩ hmax,
    densityObjective_empty]
  simp only [Matrix.add_mul, realTrace_add, densityObjective]
  rw [actualSupportedGradient_contact B hS]

theorem baseOptimizer_eq_actual [Nonempty n] (H : Matrix n n ℂ)
    (B : ι → Matrix n n ℂ) {θ : ℝ} (hθ : 0 < θ)
    (S : selfAdjoint (Matrix n n ℂ)) (hS : (S : Matrix n n ℂ).PosDef)
    (ht : realTrace (S : Matrix n n ℂ) = 1)
    (hmax : ∀ T ∈ densitySet, densityObjective H B θ T ≤ densityObjective H B θ S) :
    hermitianDensityOptimizer (H + actualSupportedGradient B S)
      (fun _ : Empty => (0 : Matrix n n ℂ)) θ = S := by
  apply density_stationary_eq_optimizer_source_unrestricted _ _ hθ S hS ht
  rw [fderiv_base_eq_actual H B θ S hS]
  exact density_maximizer_stationary_source_unrestricted H B θ S hS ht hmax

/-- A supported transport upper-bounds the actual potential at every center. -/
theorem densityPotential_le_supported [Nonempty n] (H : Matrix n n ℂ)
    (B : ι → Matrix n n ℂ) (V : Matrix n m ℂ) (hV : Vᴴ * V = 1)
    {Z : Matrix m m ℂ} (hZ : Z.PosDef) (θ : ℝ)
    (hsupport : ∀ X ∈ densitySet,
      V * (Vᴴ * krausChannel B X * V) * Vᴴ = krausChannel B X) :
    densityPotential H B θ ≤ baseDensityPotential (H + supportedGradient B V Z) θ := by
  obtain ⟨S, hS, hmax⟩ := exists_densityOptimizer H B θ
  rw [densityPotential_eq_of_maximizer H B θ hS hmax]
  have hf := fidelity_le_supportedGradient B V hV hZ hS.1 (hsupport S hS)
  have hb := baseDensityObjective_le_potential (H + supportedGradient B V Z) θ hS
  simp only [Matrix.add_mul, realTrace_add] at hb
  unfold densityObjective
  linarith

theorem baseDensityPotential_mono [Nonempty n] {H K : Matrix n n ℂ}
    (hHK : H ≤ K) (θ : ℝ) : baseDensityPotential H θ ≤ baseDensityPotential K θ := by
  obtain ⟨S, hS, hmax⟩ := exists_densityOptimizer H (fun _ : Empty => (0 : Matrix n n ℂ)) θ
  rw [baseDensityPotential, densityPotential_eq_of_maximizer _ _ _ hS hmax,
    densityObjective_empty]
  have ht := realTrace_mul_mono hS.1 hHK
  rw [realTrace_mul_comm S H, realTrace_mul_comm S K] at ht
  exact (add_le_add_right ht _).trans (baseDensityObjective_le_potential K θ hS)

/-- General endpoint comparison using the old actual transport. New atoms
need only stay in the old physical support. The matrix inequality is the
explicit safe-retirement test after its rank-one simplification. -/
theorem retire_of_supported_matrix_le [Nonempty n]
    (H Hnew : Matrix n n ℂ) (B : ι → Matrix n n ℂ) (Bnew : κ → Matrix n n ℂ)
    {θ : ℝ} (hθ : 0 < θ) (S : selfAdjoint (Matrix n n ℂ))
    (hS : (S : Matrix n n ℂ).PosDef) (ht : realTrace (S : Matrix n n ℂ) = 1)
    (hmax : ∀ T ∈ densitySet, densityObjective H B θ T ≤ densityObjective H B θ S)
    (hsupport : ∀ X ∈ densitySet,
      krausSupportEmbedding B *
        ((krausSupportEmbedding B)ᴴ * krausChannel Bnew X * krausSupportEmbedding B) *
        (krausSupportEmbedding B)ᴴ = krausChannel Bnew X)
    (hle : Hnew + supportedGradient Bnew (krausSupportEmbedding B) (actualSupportTransport B S) ≤
      H + actualSupportedGradient B S) :
    densityPotential Hnew Bnew θ ≤ densityPotential H B θ := by
  have hu := densityPotential_le_supported Hnew Bnew (krausSupportEmbedding B)
    (krausSupportEmbedding_isometry B) (actualSupportTransport_posDef B hS) θ hsupport
  exact hu.trans ((baseDensityPotential_mono hle θ).trans
    (basePotential_contact H B hθ S hS ht hmax).le)

end MatrixSpencer.KSSafeRetirement
