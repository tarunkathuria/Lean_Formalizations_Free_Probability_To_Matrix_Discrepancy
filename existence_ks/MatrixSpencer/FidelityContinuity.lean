import MatrixSpencer.TransportVariational
import MatrixSpencer.DensityDomain
import MatrixSpencer.SqrtContinuity

/-!
# Fidelity at the semidefinite boundary

Continuity uses the actual matrix square root on the entire positive cone.
Regularization adds a positive scalar multiple of the identity.
-/

open scoped Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
open Matrix Filter Topology

noncomputable section

namespace MatrixSpencer

variable {n X : Type*} [Fintype n] [DecidableEq n]

theorem continuous_fidelity_of_psd [TopologicalSpace X]
    {S M : X → Matrix n n ℂ} (hS : Continuous S) (hM : Continuous M)
    (hSpos : ∀ x, (S x).PosSemidef) (hMpos : ∀ x, (M x).PosSemidef) :
    Continuous (fun x => fidelity (S x) (M x)) := by
  have hroot := continuous_matrix_sqrt_of_psd hS hSpos
  have hinner := (hroot.mul hM).mul hroot
  have hinnerpos : ∀ x, (CFC.sqrt (S x) * M x * CFC.sqrt (S x)).PosSemidef := by
    intro x
    simpa only [(CFC.sqrt_nonneg (S x)).posSemidef.isHermitian.eq] using
      (hMpos x).conjTranspose_mul_mul_same (CFC.sqrt (S x))
  exact continuous_realTrace.comp (continuous_matrix_sqrt_of_psd hinner hinnerpos)

theorem tendsto_fidelity_of_psd {f : Filter X} {S M : X → Matrix n n ℂ}
    {S₀ M₀ : Matrix n n ℂ} (hS : Tendsto S f (𝓝 S₀)) (hM : Tendsto M f (𝓝 M₀))
    (hSpos : ∀ᶠ x in f, (S x).PosSemidef) (hMpos : ∀ᶠ x in f, (M x).PosSemidef)
    (hS₀ : S₀.PosSemidef) (hM₀ : M₀.PosSemidef) :
    Tendsto (fun x => fidelity (S x) (M x)) f (𝓝 (fidelity S₀ M₀)) := by
  have hroot := tendsto_matrix_sqrt_of_psd hS hSpos hS₀
  have hinner := (hroot.mul hM).mul hroot
  have hinnerpos : ∀ᶠ x in f, (CFC.sqrt (S x) * M x * CFC.sqrt (S x)).PosSemidef := by
    filter_upwards [hMpos] with x hx
    simpa only [(CFC.sqrt_nonneg (S x)).posSemidef.isHermitian.eq] using
      hx.conjTranspose_mul_mul_same (CFC.sqrt (S x))
  have hinner₀ : (CFC.sqrt S₀ * M₀ * CFC.sqrt S₀).PosSemidef := by
    simpa only [(CFC.sqrt_nonneg S₀).posSemidef.isHermitian.eq] using
      hM₀.conjTranspose_mul_mul_same (CFC.sqrt S₀)
  exact continuous_realTrace.continuousAt.tendsto.comp
    (tendsto_matrix_sqrt_of_psd hinner hinnerpos hinner₀)

def regularize (S : Matrix n n ℂ) (r : ℝ) : Matrix n n ℂ := S + r • 1

theorem regularize_posDef {S : Matrix n n ℂ} (hS : S.PosSemidef) {r : ℝ} (hr : 0 < r) :
    (regularize S r).PosDef :=
  Matrix.PosDef.posSemidef_add hS (Matrix.PosDef.one.smul hr)

theorem le_regularize (S : Matrix n n ℂ) {r : ℝ} (hr : 0 ≤ r) : S ≤ regularize S r := by
  exact le_add_of_nonneg_right (smul_nonneg hr zero_le_one)

omit [Fintype n] in
theorem regularize_tendsto (S : Matrix n n ℂ) :
    Tendsto (regularize S) (𝓝[Set.Ioi 0] 0) (𝓝 S) := by
  have h : Continuous (regularize S) := continuous_const.add (continuous_id.smul continuous_const)
  simpa only [regularize, zero_smul, add_zero] using (h.tendsto 0).mono_left inf_le_left

theorem fidelity_regularize_tendsto {S M : Matrix n n ℂ}
    (hS : S.PosSemidef) (hM : M.PosSemidef) :
    Tendsto (fun r => fidelity (regularize S r) (regularize M r))
      (𝓝[Set.Ioi 0] 0) (𝓝 (fidelity S M)) := by
  apply tendsto_fidelity_of_psd (regularize_tendsto S) (regularize_tendsto M) _ _ hS hM
  · exact Filter.Eventually.mono
      (self_mem_nhdsWithin : ∀ᶠ r : ℝ in 𝓝[Set.Ioi 0] 0, r ∈ Set.Ioi 0)
      (fun _ hr => (regularize_posDef hS hr).posSemidef)
  · exact Filter.Eventually.mono
      (self_mem_nhdsWithin : ∀ᶠ r : ℝ in 𝓝[Set.Ioi 0] 0, r ∈ Set.Ioi 0)
      (fun _ hr => (regularize_posDef hM hr).posSemidef)

/-- Fidelity symmetry extends to arbitrary singular positive inputs. -/
theorem fidelity_symm {S M : Matrix n n ℂ} (hS : S.PosSemidef) (hM : M.PosSemidef) :
    fidelity S M = fidelity M S := by
  apply tendsto_nhds_unique (fidelity_regularize_tendsto hS hM)
  apply (fidelity_regularize_tendsto hM hS).congr'
  filter_upwards [self_mem_nhdsWithin] with r hr
  exact fidelity_symm_posDef (regularize_posDef hM hr) (regularize_posDef hS hr)

/-- Fidelity is jointly monotone on the full positive cone. -/
theorem fidelity_mono {S₁ S₂ M₁ M₂ : Matrix n n ℂ}
    (hS₁ : S₁.PosSemidef) (hS₂ : S₂.PosSemidef)
    (hM₁ : M₁.PosSemidef) (hM₂ : M₂.PosSemidef)
    (hS : S₁ ≤ S₂) (hM : M₁ ≤ M₂) : fidelity S₁ M₁ ≤ fidelity S₂ M₂ := by
  apply le_of_tendsto_of_tendsto (fidelity_regularize_tendsto hS₁ hM₁)
    (fidelity_regularize_tendsto hS₂ hM₂)
  filter_upwards [self_mem_nhdsWithin] with r hr
  exact fidelity_mono_posDef (regularize_posDef hS₁ hr) (regularize_posDef hS₂ hr)
    (regularize_posDef hM₁ hr) (regularize_posDef hM₂ hr)
    (add_le_add_right hS _) (add_le_add_right hM _)

omit [DecidableEq n] in
theorem posSemidef_weighted_add {S T : Matrix n n ℂ}
    (hS : S.PosSemidef) (hT : T.PosSemidef) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (a • S + b • T).PosSemidef :=
  (add_nonneg (smul_nonneg ha hS.nonneg) (smul_nonneg hb hT.nonneg)).posSemidef

/-- Joint concavity holds on the full positive cone, including singular endpoints. -/
theorem fidelity_concave {S₁ S₂ M₁ M₂ : Matrix n n ℂ}
    (hS₁ : S₁.PosSemidef) (hS₂ : S₂.PosSemidef)
    (hM₁ : M₁.PosSemidef) (hM₂ : M₂.PosSemidef)
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    a * fidelity S₁ M₁ + b * fidelity S₂ M₂ ≤
      fidelity (a • S₁ + b • S₂) (a • M₁ + b • M₂) := by
  have hleft := ((fidelity_regularize_tendsto hS₁ hM₁).const_mul a).add
    ((fidelity_regularize_tendsto hS₂ hM₂).const_mul b)
  have hSmix := ((regularize_tendsto S₁).const_smul a).add
    ((regularize_tendsto S₂).const_smul b)
  have hMmix := ((regularize_tendsto M₁).const_smul a).add
    ((regularize_tendsto M₂).const_smul b)
  have hright := tendsto_fidelity_of_psd hSmix hMmix
    (show ∀ᶠ r : ℝ in 𝓝[Set.Ioi 0] 0,
      (a • regularize S₁ r + b • regularize S₂ r).PosSemidef from by
      filter_upwards [self_mem_nhdsWithin] with r hr
      exact posSemidef_weighted_add (regularize_posDef hS₁ hr).posSemidef
        (regularize_posDef hS₂ hr).posSemidef ha hb)
    (show ∀ᶠ r : ℝ in 𝓝[Set.Ioi 0] 0,
      (a • regularize M₁ r + b • regularize M₂ r).PosSemidef from by
      filter_upwards [self_mem_nhdsWithin] with r hr
      exact posSemidef_weighted_add (regularize_posDef hM₁ hr).posSemidef
        (regularize_posDef hM₂ hr).posSemidef ha hb)
    (posSemidef_weighted_add hS₁ hS₂ ha hb) (posSemidef_weighted_add hM₁ hM₂ ha hb)
  apply le_of_tendsto_of_tendsto hleft hright
  filter_upwards [self_mem_nhdsWithin] with r hr
  exact fidelity_concave_posDef (regularize_posDef hS₁ hr) (regularize_posDef hS₂ hr)
    (regularize_posDef hM₁ hr) (regularize_posDef hM₂ hr) ha hb hab

end MatrixSpencer
