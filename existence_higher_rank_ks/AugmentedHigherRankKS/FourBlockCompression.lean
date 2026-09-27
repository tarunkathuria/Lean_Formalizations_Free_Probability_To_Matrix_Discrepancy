import AugmentedHigherRankKS.FourBlockSource

/-! Fixed support compression of the four-block original-power source. -/
noncomputable section
open Matrix MatrixSpencer Filter Topology
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator ContDiff
namespace AugmentedHigherRankKS
variable {n : Type*} [Fintype n] [DecidableEq n]
local instance compressionCStar {j : Type*} [Fintype j] [DecidableEq j] :
    CStarAlgebra (Matrix j j ℂ) := {}

def spinAtom (A : Matrix n n ℂ) : Matrix (FourSpin n) (FourSpin n) ℂ :=
  HigherRankKS.spinAtom (HigherRankKS.spinAtom A)

theorem spinAtom_posSemidef {A : Matrix n n ℂ} (hA : A.PosSemidef) :
    (spinAtom A).PosSemidef :=
  HigherRankKS.spinAtom_posSemidef (HigherRankKS.spinAtom_posSemidef hA)

theorem sourceTerm_mulVec_eq_zero_iff {A : Matrix n n ℂ} (hA : A.PosSemidef)
    {S : Matrix (FourSpin n) (FourSpin n) ℂ} (hS : S.PosDef) (k : ℕ) (hk : 1 ≤ k)
    (x : FourSpin n → ℂ) :
    sourceTerm ((1 : ℝ) / (2 : ℝ) ^ k) A S *ᵥ x = 0 ↔ spinAtom A *ᵥ x = 0 := by
  change HigherRankKS.spinAtom (HigherRankKS.sourceTerm ((1 : ℝ) / (2 : ℝ) ^ k) A
    (HigherRankKS.marginal S)) *ᵥ x = 0 ↔
    HigherRankKS.spinAtom (HigherRankKS.spinAtom A) *ᵥ x = 0
  rw [HigherRankKS.spinAtom_mulVec_eq_zero_iff,
    HigherRankKS.spinAtom_mulVec_eq_zero_iff,
    HigherRankKS.sourceTerm_mulVec_eq_zero_iff hA (HigherRankKS.marginal_posDef hS) k hk,
    HigherRankKS.sourceTerm_mulVec_eq_zero_iff hA (HigherRankKS.marginal_posDef hS) k hk]

variable {ι : Type*} [Fintype ι]

/-- Positive live coefficients preserve precisely the common original-atom kernel. -/
theorem source_mulVec_eq_zero_iff (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).PosSemidef)
    {c : ι → ℝ} (hc : ∀ i, 0 < c i)
    {S : Matrix (FourSpin n) (FourSpin n) ℂ} (hS : S.PosDef) (k : ℕ) (hk : 1 ≤ k)
    (x : FourSpin n → ℂ) :
    source A ((1 : ℝ) / (2 : ℝ) ^ k) c S *ᵥ x = 0 ↔ ∀ i, spinAtom (A i) *ᵥ x = 0 := by
  constructor
  · intro hx i
    have hs : (∑ j, c j * (star x ⬝ᵥ
        (sourceTerm ((1 : ℝ) / (2 : ℝ) ^ k) (A j) S *ᵥ x)).re) = 0 := by
      have h := congrArg (fun y => (star x ⬝ᵥ y).re) hx
      simpa only [source, Matrix.sum_mulVec, Matrix.smul_mulVec, dotProduct_sum,
        dotProduct_smul, Complex.re_sum, Complex.smul_re, smul_eq_mul, dotProduct_zero,
        Complex.zero_re] using h
    have hi := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => mul_nonneg (hc j).le
      ((sourceTerm_posSemidef _ (A j) hS.posSemidef).re_dotProduct_nonneg x))).mp hs i
        (Finset.mem_univ i)
    have hreal : (star x ⬝ᵥ
        (sourceTerm ((1 : ℝ) / (2 : ℝ) ^ k) (A i) S *ᵥ x)).re = 0 :=
      (mul_eq_zero.mp hi).resolve_left (hc i).ne'
    have hterm := sourceTerm_posSemidef ((1 : ℝ) / (2 : ℝ) ^ k) (A i) hS.posSemidef
    have hcomplex : star x ⬝ᵥ (sourceTerm ((1 : ℝ) / (2 : ℝ) ^ k) (A i) S *ᵥ x) = 0 := by
      apply Complex.ext
      · exact hreal
      · exact (Complex.nonneg_iff.mp (hterm.2 x)).2.symm
    exact (sourceTerm_mulVec_eq_zero_iff (hA i) hS k hk x).mp
      ((hterm.dotProduct_mulVec_zero_iff x).mp hcomplex)
  · intro hx
    have ht : ∀ i, sourceTerm ((1 : ℝ) / (2 : ℝ) ^ k) (A i) S *ᵥ x = 0 :=
      fun i => (sourceTerm_mulVec_eq_zero_iff (hA i) hS k hk x).mpr (hx i)
    simp only [source, Matrix.sum_mulVec, Matrix.smul_mulVec, ht, smul_zero, Finset.sum_const_zero]

abbrev SourceCarrierIndex (A : ι → Matrix n n ℂ) :=
  Fin (Module.finrank ℂ (krausSupport (fun i => spinAtom (A i))))

def sourceEmbedding (A : ι → Matrix n n ℂ) : Matrix (FourSpin n) (SourceCarrierIndex A) ℂ :=
  krausSupportEmbedding (fun i => spinAtom (A i))

def compressedSource (A : ι → Matrix n n ℂ) (β : ℝ) (c : ι → ℝ)
    (S : Matrix (FourSpin n) (FourSpin n) ℂ) : Matrix (SourceCarrierIndex A) (SourceCarrierIndex A) ℂ :=
  (sourceEmbedding A)ᴴ * source A β c S * sourceEmbedding A

/-- The actual total source is faithful on the fixed span of the live atom ranges. -/
theorem compressedSource_posDef (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).PosSemidef)
    {c : ι → ℝ} (hc : ∀ i, 0 < c i)
    {S : Matrix (FourSpin n) (FourSpin n) ℂ} (hS : S.PosDef) (k : ℕ) (hk : 1 ≤ k) :
    (compressedSource A ((1 : ℝ) / (2 : ℝ) ^ k) c S).PosDef := by
  have hpsd := source_posSemidef A ((1 : ℝ) / (2 : ℝ) ^ k) (fun i => (hc i).le) hS.posSemidef
  apply (hpsd.conjTranspose_mul_mul_same (sourceEmbedding A)).posDef_iff_isUnit.mpr
  apply Matrix.mulVec_injective_iff_isUnit.mp
  change Function.Injective (compressedSource A ((1 : ℝ) / (2 : ℝ) ^ k) c S).mulVecLin
  apply LinearMap.ker_eq_bot.mp
  apply Matrix.ker_mulVecLin_eq_bot_iff.mpr
  intro x hx
  have hform : star (sourceEmbedding A *ᵥ x) ⬝ᵥ
      (source A ((1 : ℝ) / (2 : ℝ) ^ k) c S *ᵥ (sourceEmbedding A *ᵥ x)) = 0 := by
    calc
      _ = star x ⬝ᵥ (compressedSource A ((1 : ℝ) / (2 : ℝ) ^ k) c S *ᵥ x) := by
        simp only [compressedSource, star_mulVec, dotProduct_mulVec, vecMul_vecMul]
      _ = 0 := by rw [hx, dotProduct_zero]
  have hz := (hpsd.dotProduct_mulVec_zero_iff (sourceEmbedding A *ᵥ x)).mp hform
  have hAz := (source_mulVec_eq_zero_iff A hA hc hS k hk _).mp hz
  have hIz : krausChannel (fun i => spinAtom (A i)) (1 : Matrix (FourSpin n) (FourSpin n) ℂ) *ᵥ
      (sourceEmbedding A *ᵥ x) = 0 := by
    apply (krausChannel_mulVec_eq_zero_iff _ Matrix.PosDef.one _).mpr
    simpa only [fun i => (spinAtom_posSemidef (hA i)).isHermitian.eq] using hAz
  have hcompressed : krausCompressedSource (fun i => spinAtom (A i)) 1 *ᵥ x = 0 := by
    rw [krausCompressedSource_eq_compression, ← Matrix.mulVec_mulVec,
      ← Matrix.mulVec_mulVec]
    change (sourceEmbedding A)ᴴ *ᵥ
      (krausChannel (fun i => spinAtom (A i)) 1 *ᵥ (sourceEmbedding A *ᵥ x)) = 0
    rw [hIz, Matrix.mulVec_zero]
  apply Matrix.mulVec_injective_of_isUnit
    (krausCompressedSource_posDef (fun i => spinAtom (A i)) Matrix.PosDef.one).isUnit
  simpa only [Matrix.mulVec_zero] using hcompressed

theorem source_euclidean_ker_eq_identity (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).PosSemidef)
    {c : ι → ℝ} (hc : ∀ i, 0 < c i)
    {S : Matrix (FourSpin n) (FourSpin n) ℂ} (hS : S.PosDef) (k : ℕ) (hk : 1 ≤ k) :
    LinearMap.ker (Matrix.toEuclideanCLM (n := FourSpin n) (𝕜 := ℂ)
      (source A ((1 : ℝ) / (2 : ℝ) ^ k) c S)).toLinearMap =
      LinearMap.ker (Matrix.toEuclideanCLM (n := FourSpin n) (𝕜 := ℂ)
        (krausChannel (fun i => spinAtom (A i)) 1)).toLinearMap := by
  ext x
  have he (M : Matrix (FourSpin n) (FourSpin n) ℂ) :
      Matrix.toEuclideanCLM (n := FourSpin n) (𝕜 := ℂ) M x = 0 ↔ M *ᵥ WithLp.ofLp x = 0 := by
    constructor
    · intro h
      simpa only [Matrix.ofLp_toEuclideanCLM, WithLp.ofLp_zero] using congrArg WithLp.ofLp h
    · intro h
      apply WithLp.ofLp_injective
      simpa only [Matrix.ofLp_toEuclideanCLM, WithLp.ofLp_zero] using h
  change Matrix.toEuclideanCLM (n := FourSpin n) (𝕜 := ℂ)
    (source A ((1 : ℝ) / (2 : ℝ) ^ k) c S) x = 0 ↔
      Matrix.toEuclideanCLM (n := FourSpin n) (𝕜 := ℂ)
        (krausChannel (fun i => spinAtom (A i)) 1) x = 0
  simp only [he, source_mulVec_eq_zero_iff A hA hc hS k hk,
    krausChannel_mulVec_eq_zero_iff _ Matrix.PosDef.one,
    fun i => (spinAtom_posSemidef (hA i)).isHermitian.eq]

theorem source_range_eq_support (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).PosSemidef)
    {c : ι → ℝ} (hc : ∀ i, 0 < c i)
    {S : Matrix (FourSpin n) (FourSpin n) ℂ} (hS : S.PosDef) (k : ℕ) (hk : 1 ≤ k) :
    LinearMap.range (Matrix.toEuclideanCLM (n := FourSpin n) (𝕜 := ℂ)
      (source A ((1 : ℝ) / (2 : ℝ) ^ k) c S)).toLinearMap =
      krausSupport (fun i => spinAtom (A i)) := by
  have hs := isHermitian_toEuclideanCLM_symmetric
    (source_posSemidef A ((1 : ℝ) / (2 : ℝ) ^ k) (fun i => (hc i).le) hS.posSemidef).isHermitian
  have hI := isHermitian_toEuclideanCLM_symmetric
    (krausChannel_posSemidef (fun i => spinAtom (A i)) Matrix.PosSemidef.one).isHermitian
  have hh := source_euclidean_ker_eq_identity A hA hc hS k hk
  exact le_antisymm
    ((ContinuousLinearMap.ker_le_ker_iff_range_le_range hs hI).mp hh.ge)
    ((ContinuousLinearMap.ker_le_ker_iff_range_le_range hI hs).mp hh.le)

theorem source_projection_left (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).PosSemidef)
    {c : ι → ℝ} (hc : ∀ i, 0 < c i)
    {S : Matrix (FourSpin n) (FourSpin n) ℂ} (hS : S.PosDef) (k : ℕ) (hk : 1 ≤ k) :
    (sourceEmbedding A * (sourceEmbedding A)ᴴ) * source A ((1 : ℝ) / (2 : ℝ) ^ k) c S =
      source A ((1 : ℝ) / (2 : ℝ) ^ k) c S := by
  apply (Matrix.toEuclideanCLM (n := FourSpin n) (𝕜 := ℂ)).injective
  rw [map_mul]
  change Matrix.toEuclideanCLM (n := FourSpin n) (𝕜 := ℂ)
      (krausSupportEmbedding (fun i => spinAtom (A i)) *
        (krausSupportEmbedding (fun i => spinAtom (A i)))ᴴ) * _ = _
  rw [krausSupportEmbedding_projection]
  apply ContinuousLinearMap.ext
  intro x
  apply Submodule.starProjection_eq_self_iff.mpr
  rw [← source_range_eq_support A hA hc hS k hk]
  exact LinearMap.mem_range_self _ x

theorem source_projection_right (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).PosSemidef)
    {c : ι → ℝ} (hc : ∀ i, 0 < c i)
    {S : Matrix (FourSpin n) (FourSpin n) ℂ} (hS : S.PosDef) (k : ℕ) (hk : 1 ≤ k) :
    source A ((1 : ℝ) / (2 : ℝ) ^ k) c S * (sourceEmbedding A * (sourceEmbedding A)ᴴ) =
      source A ((1 : ℝ) / (2 : ℝ) ^ k) c S := by
  have h := congrArg Matrix.conjTranspose (source_projection_left A hA hc hS k hk)
  simpa only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
    (source_posSemidef A ((1 : ℝ) / (2 : ℝ) ^ k) (fun i => (hc i).le) hS.posSemidef).isHermitian.eq] using h

theorem compressedSource_reconstruct (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).PosSemidef)
    {c : ι → ℝ} (hc : ∀ i, 0 < c i)
    {S : Matrix (FourSpin n) (FourSpin n) ℂ} (hS : S.PosDef) (k : ℕ) (hk : 1 ≤ k) :
    sourceEmbedding A * compressedSource A ((1 : ℝ) / (2 : ℝ) ^ k) c S *
      (sourceEmbedding A)ᴴ = source A ((1 : ℝ) / (2 : ℝ) ^ k) c S := by
  calc
    _ = (sourceEmbedding A * (sourceEmbedding A)ᴴ) *
        source A ((1 : ℝ) / (2 : ℝ) ^ k) c S *
        (sourceEmbedding A * (sourceEmbedding A)ᴴ) := by simp only [compressedSource, Matrix.mul_assoc]
    _ = _ := by rw [source_projection_left A hA hc hS k hk, source_projection_right A hA hc hS k hk]

theorem fidelity_source_compression (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).PosSemidef)
    {c : ι → ℝ} (hc : ∀ i, 0 < c i)
    {S : Matrix (FourSpin n) (FourSpin n) ℂ} (hS : S.PosDef) (k : ℕ) (hk : 1 ≤ k) :
    fidelity S (source A ((1 : ℝ) / (2 : ℝ) ^ k) c S) =
      fidelity ((sourceEmbedding A)ᴴ * S * sourceEmbedding A)
        (compressedSource A ((1 : ℝ) / (2 : ℝ) ^ k) c S) := by
  conv_lhs => rhs; rw [← compressedSource_reconstruct A hA hc hS k hk]
  exact fidelity_isometry_compression (sourceEmbedding A)
    (krausSupportEmbedding_isometry _) hS.posSemidef
    (compressedSource_posDef A hA hc hS k hk).posSemidef

/-- Frozen zero-weight labels can be removed exactly; the density and center stay in the full space. -/
theorem source_eq_live [DecidableEq ι] (A : ι → Matrix n n ℂ) (β : ℝ)
    (L : Finset ι) (c : ι → ℝ) (hc : ∀ i, i ∉ L → c i = 0)
    (S : Matrix (FourSpin n) (FourSpin n) ℂ) :
    source A β c S = source (fun i : {i // i ∈ L} => A i) β (fun i => c i) S := by
  classical
  have h := Fintype.sum_subtype_add_sum_subtype (fun i => i ∈ L)
    (fun i => c i • sourceTerm β (A i) S)
  have hz : (∑ i : {i // i ∉ L}, c i • sourceTerm β (A i) S) = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    rw [hc i i.property, zero_smul]
  rw [hz, add_zero] at h
  unfold source
  exact h.symm.trans (Finset.sum_congr (by ext i; simp) (fun _ _ => rfl))

end AugmentedHigherRankKS
