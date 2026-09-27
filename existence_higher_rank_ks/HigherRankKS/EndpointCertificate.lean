import HigherRankKS.SourceDerivative
import HigherRankKS.SupportedSpin
import HigherRankKS.EndpointMajorant
import HigherRankKS.PotentialSmoothness
import MatrixSpencer.KSArbitraryTransportContact

/-! A fixed supported transport majorizes the nonlinear source objective even
when an owner is deleted and the source support becomes smaller. -/

open Matrix MatrixSpencer Filter Topology Set
open scoped NNReal BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator ContDiff

noncomputable section
namespace HigherRankKS.EndpointCertificate

variable {ι n : Type*} [Fintype ι] [Fintype n] [DecidableEq n]
local instance endpointCertificateCStar {m : Type*} [Fintype m] [DecidableEq m] :
    CStarAlgebra (Matrix m m ℂ) := {}

private theorem dyadic_mem_Ioo (k : ℕ) (hk : 1 ≤ k) :
    (1 : ℝ) / (2 : ℝ) ^ k ∈ Ioo (0 : ℝ) 1 := by
  constructor
  · positivity
  · apply (div_lt_one (by positivity : 0 < (2 : ℝ) ^ k)).mpr
    exact one_lt_pow₀ (by norm_num) (Nat.ne_of_gt hk)

/-- Fixed support reconstruction extends to singular comparison densities. -/
theorem term_reconstruct_psd (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).PosSemidef)
    {S : Matrix (n ⊕ n) (n ⊕ n) ℂ} (hS : S.PosSemidef)
    (k : ℕ) (hk : 1 ≤ k) (i : ι) :
    sourceEmbedding A * SupportedSpin.term A ((1 : ℝ) / 2 ^ k) S i * (sourceEmbedding A)ᴴ =
      sourceTerm ((1 : ℝ) / 2 ^ k) (A i) S := by
  let f : ℝ≥0 → Matrix (n ⊕ n) (n ⊕ n) ℂ := fun t =>
    sourceTerm ((1 : ℝ) / 2 ^ k) (A i) (S + (t : ℝ) • 1)
  have hf : Continuous f := continuous_sourceTerm_of_psd (A i)
    (continuous_const.add (NNReal.continuous_coe.smul continuous_const))
    (fun t => hS.add (Matrix.PosSemidef.one.smul t.coe_nonneg))
    (dyadic_mem_Ioo k hk).1.le (dyadic_mem_Ioo k hk).2.le
  have heq : EqOn
      (fun t : ℝ≥0 => sourceEmbedding A *
        ((sourceEmbedding A)ᴴ * f t * sourceEmbedding A) * (sourceEmbedding A)ᴴ)
      f (Ioi 0) := by
    intro t ht
    exact SupportedSpin.term_reconstruct A hA (regularize_posDef hS ht) k hk i
  have hc : Continuous (fun t : ℝ≥0 => sourceEmbedding A *
      ((sourceEmbedding A)ᴴ * f t * sourceEmbedding A) * (sourceEmbedding A)ᴴ) := by
    simpa only [Function.comp_def, matrixExtensionCLM_apply, Matrix.conjTranspose_conjTranspose] using
      (matrixExtensionCLM (sourceEmbedding A)).continuous.comp
        ((matrixExtensionCLM (sourceEmbedding A)ᴴ).continuous.comp hf)
  have hh := heq.closure hc hf
  have hzero : (0 : ℝ≥0) ∈ closure (Ioi (0 : ℝ≥0)) := by
    simpa only [closure_Ioi, mem_Ici] using (show (0 : ℝ≥0) ≤ 0 from le_rfl)
  simpa only [f, NNReal.coe_zero, zero_smul, add_zero] using hh hzero

/-- Arbitrary new weights remain in the original fixed support. -/
theorem source_reconstruct_psd (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).PosSemidef)
    {S : Matrix (n ⊕ n) (n ⊕ n) ℂ} (hS : S.PosSemidef)
    (k : ℕ) (hk : 1 ≤ k) (c : ι → ℝ) :
    sourceEmbedding A * compressedSource A ((1 : ℝ) / 2 ^ k) c S * (sourceEmbedding A)ᴴ =
      source A ((1 : ℝ) / 2 ^ k) c S := by
  rw [SupportedSpin.compressedSource_eq_sum]
  simp only [Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_smul, Matrix.smul_mul,
    term_reconstruct_psd A hA hS k hk, source]

/-- A fixed supported transport, extended by zero in the full density space. -/
def extended (A : ι → Matrix n n ℂ)
    (Z : Matrix (SourceCarrierIndex A) (SourceCarrierIndex A) ℂ) :
    Matrix (n ⊕ n) (n ⊕ n) ℂ := sourceEmbedding A * Z * (sourceEmbedding A)ᴴ

/-- The old transport objective for any new nonnegative owner weights. -/
def fixedObjective (H : Matrix (n ⊕ n) (n ⊕ n) ℂ) (A : ι → Matrix n n ℂ)
    (β : ℝ) (c : ι → ℝ) (θ : ℝ)
    (Z : Matrix (SourceCarrierIndex A) (SourceCarrierIndex A) ℂ)
    (S : selfAdjoint (Matrix (n ⊕ n) (n ⊕ n) ℂ)) : ℝ :=
  realTrace (H * (S : Matrix (n ⊕ n) (n ⊕ n) ℂ)) + realTrace (extended A Z⁻¹ * (S : Matrix (n ⊕ n) (n ⊕ n) ℂ)) +
    ∑ i, c i * SourceDerivative.probe β (A i) (extended A Z) S +
    2 * θ * realTrace (CFC.sqrt (S : Matrix (n ⊕ n) (n ⊕ n) ℂ))

theorem fixedObjective_eq_cost (H : Matrix (n ⊕ n) (n ⊕ n) ℂ)
    (A : ι → Matrix n n ℂ) (β : ℝ) (c : ι → ℝ) (θ : ℝ)
    (Z : Matrix (SourceCarrierIndex A) (SourceCarrierIndex A) ℂ)
    (S : selfAdjoint (Matrix (n ⊕ n) (n ⊕ n) ℂ)) :
    fixedObjective H A β c θ Z S = realTrace (H * (S : Matrix (n ⊕ n) (n ⊕ n) ℂ)) +
      transportCost (SupportedSpin.density A (S : Matrix (n ⊕ n) (n ⊕ n) ℂ))
        (compressedSource A β c (S : Matrix (n ⊕ n) (n ⊕ n) ℂ)) Z +
      2 * θ * realTrace (CFC.sqrt (S : Matrix (n ⊕ n) (n ⊕ n) ℂ)) := by
  have hs : (∑ i, c i * SourceDerivative.probe β (A i) (extended A Z) S) =
      realTrace (Z * compressedSource A β c (S : Matrix (n ⊕ n) (n ⊕ n) ℂ)) := by
    rw [compressedSource, ← KSSafeRetirement.realTrace_embedded_mul]
    simp only [source, Matrix.mul_sum, Matrix.mul_smul, realTrace_sum, realTrace_smul,
      SourceDerivative.probe, extended]
  rw [fixedObjective, hs]
  simp only [extended, KSSafeRetirement.realTrace_embedded_mul, transportCost,
    SupportedSpin.density, KSSupportSymmetry.compress]
  rw [realTrace_mul_comm Z⁻¹, realTrace_mul_comm Z]
  ring

/-- The fixed transport is valid for singular test densities and after deletion. -/
theorem objective_le_fixed (H : Matrix (n ⊕ n) (n ⊕ n) ℂ)
    (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).PosSemidef)
    (k : ℕ) (hk : 1 ≤ k) {c : ι → ℝ} (hc : ∀ i, 0 ≤ c i) (θ : ℝ)
    (Z : Matrix (SourceCarrierIndex A) (SourceCarrierIndex A) ℂ) (hZ : Z.PosDef)
    (S : selfAdjoint (Matrix (n ⊕ n) (n ⊕ n) ℂ))
    (hS : (S : Matrix (n ⊕ n) (n ⊕ n) ℂ).PosSemidef) :
    objective H A ((1 : ℝ) / 2 ^ k) c θ (S : Matrix (n ⊕ n) (n ⊕ n) ℂ) ≤
      fixedObjective H A ((1 : ℝ) / 2 ^ k) c θ Z S := by
  have hm := (source_posSemidef A ((1 : ℝ) / 2 ^ k) hc hS).conjTranspose_mul_mul_same
    (sourceEmbedding A)
  have hd := hS.conjTranspose_mul_mul_same (sourceEmbedding A)
  have hf : fidelity (S : Matrix (n ⊕ n) (n ⊕ n) ℂ) (source A ((1 : ℝ) / 2 ^ k) c (S : Matrix (n ⊕ n) (n ⊕ n) ℂ)) =
      fidelity (SupportedSpin.density A (S : Matrix (n ⊕ n) (n ⊕ n) ℂ))
        (compressedSource A ((1 : ℝ) / 2 ^ k) c (S : Matrix (n ⊕ n) (n ⊕ n) ℂ)) := by
    conv_lhs => rhs; rw [← source_reconstruct_psd A hA hS k hk c]
    exact fidelity_isometry_compression (sourceEmbedding A) (SupportedSpin.embedding_isometry A) hS hm
  have hb : 2 * fidelity (SupportedSpin.density A (S : Matrix (n ⊕ n) (n ⊕ n) ℂ))
      (compressedSource A ((1 : ℝ) / 2 ^ k) c (S : Matrix (n ⊕ n) (n ⊕ n) ℂ)) ≤
      transportCost (SupportedSpin.density A (S : Matrix (n ⊕ n) (n ⊕ n) ℂ))
        (compressedSource A ((1 : ℝ) / 2 ^ k) c (S : Matrix (n ⊕ n) (n ⊕ n) ℂ)) Z :=
    fidelity_le_transportCost hd hm hZ
  rw [fixedObjective_eq_cost, objective, hf]
  linarith

/-- The fixed transport objective is smooth at every faithful density. -/
theorem contDiffAt_fixedObjective (H : Matrix (n ⊕ n) (n ⊕ n) ℂ)
    (A : ι → Matrix n n ℂ) (k : ℕ) (hk : 1 ≤ k) (c : ι → ℝ) (θ : ℝ)
    (Z : Matrix (SourceCarrierIndex A) (SourceCarrierIndex A) ℂ)
    (S : selfAdjoint (Matrix (n ⊕ n) (n ⊕ n) ℂ))
    (hS : (S : Matrix (n ⊕ n) (n ⊕ n) ℂ).PosDef) :
    ContDiffAt ℝ ∞ (fixedObjective H A ((1 : ℝ) / 2 ^ k) c θ Z) S := by
  exact ((((tracePairing H).contDiff.contDiffAt).add
    ((tracePairing (extended A Z⁻¹)).contDiff.contDiffAt)).add
      (ContDiffAt.sum (fun i _ => contDiffAt_const.mul
        (SourceDerivative.contDiffAt_probe (A i) (extended A Z) k hk S hS)))).add
    (contDiffAt_tsallisPotential θ S hS)

/-- A fixed positive probe preserves the actual source's concavity. -/
theorem probe_concave (A : Matrix n n ℂ) {β : ℝ} (hβ : β ∈ Ioo 0 1)
    (Z : Matrix (n ⊕ n) (n ⊕ n) ℂ) (hZ : Z.PosSemidef) :
    ConcaveOn ℝ (OptimizerResponse.densityDomain (n := n ⊕ n)) (SourceDerivative.probe β A Z) := by
  refine ⟨densitySet_convex.linear_preimage (hermitianInclusion (n := n ⊕ n)).toLinearMap, ?_⟩
  intro S hS T hT a b ha hb hab
  have h := realTrace_mul_mono hZ (sourceTerm_weighted_add_le A hβ.1 hβ.2 hS.1 hT.1 ha hb)
  simpa only [SourceDerivative.probe, Matrix.mul_add, Matrix.mul_smul, realTrace_add,
    realTrace_smul, smul_eq_mul] using h

/-- Deleting an owner preserves concavity of the entire fixed-transport objective. -/
theorem fixedObjective_concave (H : Matrix (n ⊕ n) (n ⊕ n) ℂ)
    (A : ι → Matrix n n ℂ) {β : ℝ} (hβ : β ∈ Ioo 0 1)
    {c : ι → ℝ} (hc : ∀ i, 0 ≤ c i) {θ : ℝ} (hθ : 0 ≤ θ)
    (Z : Matrix (SourceCarrierIndex A) (SourceCarrierIndex A) ℂ) (hZ : Z.PosDef) :
    ConcaveOn ℝ (OptimizerResponse.densityDomain (n := n ⊕ n)) (fixedObjective H A β c θ Z) := by
  have hd : Convex ℝ (OptimizerResponse.densityDomain (n := n ⊕ n)) :=
    densitySet_convex.linear_preimage (hermitianInclusion (n := n ⊕ n)).toLinearMap
  have hz : (extended A Z).PosSemidef := hZ.posSemidef.mul_mul_conjTranspose_same (sourceEmbedding A)
  refine ⟨hd, ?_⟩
  intro S hS T hT a b ha hb hab
  have hp : a * (∑ i, c i * SourceDerivative.probe β (A i) (extended A Z) S) +
      b * (∑ i, c i * SourceDerivative.probe β (A i) (extended A Z) T) ≤
      ∑ i, c i * SourceDerivative.probe β (A i) (extended A Z) (a • S + b • T) := by
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro i _
    have hh := mul_le_mul_of_nonneg_left
      ((probe_concave (A i) hβ (extended A Z) hz).2 hS hT ha hb hab) (hc i)
    simp only [smul_eq_mul] at hh
    nlinarith
  have hr := mul_le_mul_of_nonneg_left (trace_sqrt_concave hS.1 hT.1 ha hb hab)
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hθ)
  simp only [fixedObjective, (selfAdjoint (Matrix (n ⊕ n) (n ⊕ n) ℂ)).coe_add,
    selfAdjoint.val_smul, Matrix.mul_add, Matrix.mul_smul, realTrace_add, realTrace_smul,
    smul_eq_mul]
  nlinarith

/-- The chosen old transport touches the actual objective at its base density. -/
theorem fixedObjective_contact (H : Matrix (n ⊕ n) (n ⊕ n) ℂ)
    (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).PosSemidef)
    (k : ℕ) (hk : 1 ≤ k) {c : ι → ℝ} (hc : ∀ i, 0 < c i) (θ : ℝ)
    (S : selfAdjoint (Matrix (n ⊕ n) (n ⊕ n) ℂ))
    (hS : (S : Matrix (n ⊕ n) (n ⊕ n) ℂ).PosDef) :
    fixedObjective H A ((1 : ℝ) / 2 ^ k) c θ
      (SupportedSpin.transport A ((1 : ℝ) / 2 ^ k) c (S : Matrix (n ⊕ n) (n ⊕ n) ℂ)) S =
        hermitianObjective H A ((1 : ℝ) / 2 ^ k) c θ S := by
  rw [fixedObjective_eq_cost]
  rw [transportCost_at_transport (SupportedSpin.transport_posDef A hA hc hS k hk)
    (SupportedSpin.transport_equation A hA hc hS k hk)]
  rw [SupportedSpin.transport, trace_transportOptimizer_eq_fidelity
    (SupportedSpin.density_posDef A hS) (compressedSource_posDef A hA hc hS k hk)]
  rw [hermitianObjective, objective, fidelity_source_compression A hA hc hS k hk]
  rfl

/-- Smooth contact transfers the actual maximizing objective's derivative
onto the fixed old transport objective. -/
theorem fixedObjective_fderiv (H : Matrix (n ⊕ n) (n ⊕ n) ℂ)
    (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).PosSemidef)
    (k : ℕ) (hk : 1 ≤ k) {c : ι → ℝ} (hc : ∀ i, 0 < c i) (θ : ℝ)
    (S : selfAdjoint (Matrix (n ⊕ n) (n ⊕ n) ℂ))
    (hS : (S : Matrix (n ⊕ n) (n ⊕ n) ℂ).PosDef) :
    fderiv ℝ (fixedObjective H A ((1 : ℝ) / 2 ^ k) c θ
      (SupportedSpin.transport A ((1 : ℝ) / 2 ^ k) c (S : Matrix (n ⊕ n) (n ⊕ n) ℂ))) S =
      fderiv ℝ (hermitianObjective H A ((1 : ℝ) / 2 ^ k) c θ) S := by
  apply KSArbitraryTransportContact.fderiv_eq_of_touching_majorant
    ((contDiffAt_hermitianObjective H A hA k hk c hc θ S hS).differentiableAt (by simp))
    ((contDiffAt_fixedObjective H A k hk c θ _ S hS).differentiableAt (by simp))
    (fixedObjective_contact H A hA k hk hc θ S hS)
  filter_upwards [eventually_posDef_of_posDef S hS] with T hT
  exact objective_le_fixed H A hA k hk (fun i => (hc i).le) θ _
    (SupportedSpin.transport_posDef A hA hc hS k hk) T hT.posSemidef

section Deletion
variable [DecidableEq ι]

theorem fixedObjective_delete_add (H : Matrix (n ⊕ n) (n ⊕ n) ℂ)
    (A : ι → Matrix n n ℂ) (β : ℝ) (c : ι → ℝ) (θ : ℝ)
    (Z : Matrix (SourceCarrierIndex A) (SourceCarrierIndex A) ℂ)
    (i : ι) (S : selfAdjoint (Matrix (n ⊕ n) (n ⊕ n) ℂ)) :
    fixedObjective H A β c θ Z S = fixedObjective H A β (Function.update c i 0) θ Z S +
      c i * SourceDerivative.probe β (A i) (extended A Z) S := by
  have hs : (∑ j, c j * SourceDerivative.probe β (A j) (extended A Z) S) =
      (∑ j, Function.update c i 0 j * SourceDerivative.probe β (A j) (extended A Z) S) +
        c i * SourceDerivative.probe β (A i) (extended A Z) S := by
    calc
      _ = ∑ j, (Function.update c i 0 j * SourceDerivative.probe β (A j) (extended A Z) S +
          if j = i then c i * SourceDerivative.probe β (A i) (extended A Z) S else 0) := by
        apply Finset.sum_congr rfl
        intro j _
        by_cases hj : j = i
        · subst j
          simp
        · simp [hj]
      _ = _ := by simp [Finset.sum_add_distrib]
  simp only [fixedObjective]
  linarith

/-- The concrete fixed-transport certificate permits deletion of one owner
and the corresponding bounded change of the full center. -/
theorem potential_delete_le (H C : Matrix (n ⊕ n) (n ⊕ n) ℂ)
    (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).PosSemidef)
    (k : ℕ) (hk : 1 ≤ k) (c : ι → ℝ) (hc : ∀ i, 0 < c i)
    (θ : ℝ) (hθ : 0 ≤ θ)
    (S : selfAdjoint (Matrix (n ⊕ n) (n ⊕ n) ℂ))
    (hS : (S : Matrix (n ⊕ n) (n ⊕ n) ℂ).PosDef)
    (ht : realTrace (S : Matrix (n ⊕ n) (n ⊕ n) ℂ) = 1)
    (hmax : ∀ T ∈ densitySet,
      objective H A ((1 : ℝ) / 2 ^ k) c θ T ≤ objective H A ((1 : ℝ) / 2 ^ k) c θ (S : Matrix (n ⊕ n) (n ⊕ n) ℂ))
    (i : ι) (hi : A i ≠ 0) (a : ℝ) (hC : C ≤ a • spinAtom (A i))
    (hcert : a ≤ ((1 : ℝ) / 2 ^ k) * c i *
      (SourceDerivative.probe ((1 : ℝ) / 2 ^ k) (A i)
        (extended A (SupportedSpin.transport A ((1 : ℝ) / 2 ^ k) c (S : Matrix (n ⊕ n) (n ⊕ n) ℂ))) S /
        realTrace (spinAtom (A i) * (S : Matrix (n ⊕ n) (n ⊕ n) ℂ)))) :
    potential (H + C) A ((1 : ℝ) / 2 ^ k) (Function.update c i 0) θ ≤
      potential H A ((1 : ℝ) / 2 ^ k) c θ := by
  let β : ℝ := (1 : ℝ) / 2 ^ k
  let Z := SupportedSpin.transport A β c (S : Matrix (n ⊕ n) (n ⊕ n) ℂ)
  let g := fixedObjective H A β (Function.update c i 0) θ Z
  let τ := SourceDerivative.probe β (A i) (extended A Z)
  have hZ : Z.PosDef := SupportedSpin.transport_posDef A hA hc hS k hk
  have hZfull : (extended A Z).PosSemidef := hZ.posSemidef.mul_mul_conjTranspose_same (sourceEmbedding A)
  have hc' : ∀ j, 0 ≤ Function.update c i 0 j := by
    intro j
    by_cases hj : j = i
    · subst j
      simp
    · simpa only [Function.update_of_ne hj] using (hc j).le
  have hSd : S ∈ OptimizerResponse.densityDomain (n := n ⊕ n) := ⟨hS.posSemidef, ht⟩
  have dg : DifferentiableAt ℝ g S :=
    (contDiffAt_fixedObjective H A k hk (Function.update c i 0) θ Z S hS).differentiableAt (by simp)
  have dt : DifferentiableAt ℝ τ S :=
    (SourceDerivative.contDiffAt_probe (A i) (extended A Z) k hk S hS).differentiableAt (by simp)
  have hsplit : fixedObjective H A β c θ Z = fun T => g T + c i * τ T := by
    funext T
    exact fixedObjective_delete_add H A β c θ Z i T
  have hderiv : fderiv ℝ g S + c i • fderiv ℝ τ S =
      fderiv ℝ (fixedObjective H A β c θ Z) S := by
    rw [hsplit]
    exact (dg.hasFDerivAt.add (dt.hasFDerivAt.const_mul (c i))).fderiv.symm
  have hstat := OptimizerResponse.faithful_maximizer_stationary
    (hermitianObjective H A β c θ) S hS ht
    ((contDiffAt_hermitianObjective H A hA k hk c hc θ S hS).differentiableAt (by simp))
    (fun T hT => hmax T hT)
  have hstationary : ∀ T ∈ OptimizerResponse.densityDomain (n := n ⊕ n),
      (fderiv ℝ g S + c i • fderiv ℝ τ S) (T - S) = 0 := by
    intro T hT
    rw [hderiv, fixedObjective_fderiv H A hA k hk hc θ S hS]
    have hzero : realTrace ((T - S : selfAdjoint (Matrix (n ⊕ n) (n ⊕ n) ℂ)) : Matrix (n ⊕ n) (n ⊕ n) ℂ) = 0 := by
      change realTrace ((T : Matrix (n ⊕ n) (n ⊕ n) ℂ) - (S : Matrix (n ⊕ n) (n ⊕ n) ℂ)) = 0
      rw [realTrace_sub, hT.2, ht, sub_self]
    let X : densityTangent (n := n ⊕ n) := ⟨T - S, (mem_densityTangent_iff _).mpr hzero⟩
    exact DFunLike.congr_fun hstat X
  have heuler : fderiv ℝ τ S S = τ S := SourceDerivative.probe_euler (A i) (extended A Z) k hk S hS
  have hcertificate : ∀ T ∈ OptimizerResponse.densityDomain (n := n ⊕ n),
      tracePairing C T ≤ c i * fderiv ℝ τ S T := by
    intro T hT
    have htrace := realTrace_mul_mono hT.1 hC
    rw [realTrace_mul_comm (T : Matrix (n ⊕ n) (n ⊕ n) ℂ) C, Matrix.mul_smul, realTrace_smul,
      realTrace_mul_comm (T : Matrix (n ⊕ n) (n ⊕ n) ℂ)] at htrace
    have hp := SourceDerivative.atom_mass_pos (hA i) hi hS
    have hd := SourceDerivative.probe_derivative_lower (A i) (hA i) (extended A Z) hZfull
      k hk S T hS hT.1 hp
    have hm := realTrace_mul_nonneg (spinAtom_posSemidef (hA i)) hT.1
    have hscale := mul_le_mul_of_nonneg_right hcert hm
    have hderivscale := mul_le_mul_of_nonneg_left hd (hc i).le
    change realTrace (C * (T : Matrix (n ⊕ n) (n ⊕ n) ℂ)) ≤ _
    change realTrace (C * (T : Matrix (n ⊕ n) (n ⊕ n) ℂ)) ≤ c i *
      fderiv ℝ (SourceDerivative.probe ((1 : ℝ) / 2 ^ k) (A i) (extended A Z)) S T
    nlinarith
  have hmajorant : ∀ T ∈ OptimizerResponse.densityDomain (n := n ⊕ n),
      hermitianObjective (H + C) A β (Function.update c i 0) θ T ≤ g T + tracePairing C T := by
    intro T hT
    have h := objective_le_fixed (H + C) A hA k hk hc' θ Z hZ T hT.1
    simp only [fixedObjective, Matrix.add_mul, realTrace_add] at h
    unfold g fixedObjective
    change objective (H + C) A β (Function.update c i 0) θ (T : Matrix (n ⊕ n) (n ⊕ n) ℂ) ≤ _
    simp only [tracePairing_apply]
    linarith
  have hb : ∀ T : selfAdjoint (Matrix (n ⊕ n) (n ⊕ n) ℂ),
      T ∈ OptimizerResponse.densityDomain (n := n ⊕ n) →
      hermitianObjective (H + C) A β (Function.update c i 0) θ T ≤ g S + c i * τ S :=
    EndpointMajorant.deletion_bound
    (fixedObjective_concave H A (dyadic_mem_Ioo k hk) hc' hθ Z hZ) hSd
    dg.hasFDerivAt (c i) hstationary heuler hcertificate hmajorant
  have hsbound : potential (H + C) A β (Function.update c i 0) θ ≤ g S + c i * τ S := by
    have hne : (objective (H + C) A β (Function.update c i 0) θ '' densitySet).Nonempty :=
      ⟨_, Set.mem_image_of_mem _ hSd⟩
    apply csSup_le hne
    rintro _ ⟨T, hT, rfl⟩
    exact hb ⟨T, hT.1.isHermitian⟩ hT
  calc
    potential (H + C) A β (Function.update c i 0) θ ≤ g S + c i * τ S := hsbound
    _ = fixedObjective H A β c θ Z S := (fixedObjective_delete_add H A β c θ Z i S).symm
    _ = objective H A β c θ (S : Matrix (n ⊕ n) (n ⊕ n) ℂ) := fixedObjective_contact H A hA k hk hc θ S hS
    _ = potential H A β c θ := (potential_eq_of_optimizer H A β c θ hSd hmax).symm

end Deletion

end HigherRankKS.EndpointCertificate
