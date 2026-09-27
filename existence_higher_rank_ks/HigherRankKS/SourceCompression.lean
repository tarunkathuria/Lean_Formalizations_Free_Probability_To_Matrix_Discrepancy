import HigherRankKS.Source
import HigherRankKS.CarrierSmoothness
import MatrixSpencer.KrausCompressionBridge
import MatrixSpencer.CovarianceSupport

/-! Fixed carrier compression for the actual nonlinear source, including singular atoms. -/

noncomputable section
open Matrix MatrixSpencer
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator ContDiff

namespace HigherRankKS

variable {n : Type*} [Fintype n] [DecidableEq n]
local instance sourceCompressionCStar {k : Type*} [Fintype k] [DecidableEq k] :
    CStarAlgebra (Matrix k k ℂ) := {}

omit [DecidableEq n] in
theorem marginal_posDef {S : Matrix (n ⊕ n) (n ⊕ n) ℂ} (hS : S.PosDef) :
    (marginal S).PosDef := by
  have hl : S.toBlocks₁₁.PosDef := by
    refine ⟨hS.isHermitian.submatrix Sum.inl, ?_⟩
    intro x hx
    have hv : Sum.elim x (0 : n → ℂ) ≠ 0 := by
      intro hz
      apply hx
      funext i
      simpa using congrFun hz (Sum.inl i)
    simpa [Matrix.toBlocks₁₁, Matrix.mulVec, dotProduct, Fintype.sum_sum_type] using
      hS.2 (Sum.elim x (0 : n → ℂ)) hv
  exact hl.add_posSemidef (hS.posSemidef.submatrix Sum.inr)

def atomKraus (A : Matrix n n ℂ) : Unit → Matrix n n ℂ := fun _ => CFC.sqrt A

abbrev AtomCarrierIndex (A : Matrix n n ℂ) :=
  Fin (Module.finrank ℂ (krausSupport (atomKraus A)))

def atomEmbedding (A : Matrix n n ℂ) : Matrix n (AtomCarrierIndex A) ℂ :=
  krausSupportEmbedding (atomKraus A)

theorem atomEmbedding_isometry (A : Matrix n n ℂ) :
    (atomEmbedding A)ᴴ * atomEmbedding A = 1 := krausSupportEmbedding_isometry _

theorem atomKraus_channel (A : Matrix n n ℂ) (T : Matrix n n ℂ) :
    krausChannel (atomKraus A) T = CFC.sqrt A * T * CFC.sqrt A := by
  simp [krausChannel, atomKraus, (CFC.sqrt_nonneg A).posSemidef.isHermitian.eq]

/-- The fixed compressed space is exactly the atom's range, not an invented larger carrier. -/
theorem atom_support_eq_range {A : Matrix n n ℂ} (hA : A.PosSemidef) :
    krausSupport (atomKraus A) =
      LinearMap.range (Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ) A).toLinearMap := by
  unfold krausSupport
  rw [atomKraus_channel, Matrix.mul_one, CFC.sqrt_mul_sqrt_self A hA.nonneg]

def compressedCarrier (A : Matrix n n ℂ) (S : Matrix (n ⊕ n) (n ⊕ n) ℂ) :
    Matrix (AtomCarrierIndex A) (AtomCarrierIndex A) ℂ :=
  krausCompressedSource (atomKraus A) (marginal S)

theorem compressedCarrier_eq_compression (A : Matrix n n ℂ)
    (S : Matrix (n ⊕ n) (n ⊕ n) ℂ) :
    compressedCarrier A S = (atomEmbedding A)ᴴ * carrier A S * atomEmbedding A := by
  rw [compressedCarrier, krausCompressedSource_eq_compression, atomKraus_channel]
  rfl

theorem compressedCarrier_posDef (A : Matrix n n ℂ)
    {S : Matrix (n ⊕ n) (n ⊕ n) ℂ} (hS : S.PosDef) :
    (compressedCarrier A S).PosDef :=
  krausCompressedSource_posDef _ (marginal_posDef hS)

theorem compressedCarrier_posSemidef (A : Matrix n n ℂ)
    {S : Matrix (n ⊕ n) (n ⊕ n) ℂ} (hS : S.PosSemidef) :
    (compressedCarrier A S).PosSemidef :=
  krausCompressedSource_posSemidef _ (marginal_posSemidef hS)

theorem carrier_reconstruct (A : Matrix n n ℂ)
    {S : Matrix (n ⊕ n) (n ⊕ n) ℂ} (hS : S.PosSemidef) :
    atomEmbedding A * compressedCarrier A S * (atomEmbedding A)ᴴ = carrier A S := by
  simpa only [atomEmbedding, compressedCarrier, atomKraus_channel, carrier] using
    krausCompressedSource_reconstruct (atomKraus A) (marginal_posSemidef hS)

variable {m : Type*} [Fintype m] [DecidableEq m]

theorem dyadicRoot_isometry_embedding (V : Matrix n m ℂ) (hV : Vᴴ * V = 1)
    {M : Matrix m m ℂ} (hM : M.PosSemidef) (k : ℕ) :
    dyadicRoot k (V * M * Vᴴ) = V * dyadicRoot k M * Vᴴ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [dyadicRoot_succ, ih, sqrt_isometry_embedding V hV (dyadicRoot_posSemidef k hM)]
    rfl

theorem pow_succ_isometry_embedding (V : Matrix n m ℂ) (hV : Vᴴ * V = 1)
    (M : Matrix m m ℂ) (j : ℕ) :
    (V * M * Vᴴ) ^ (j + 1) = V * M ^ (j + 1) * Vᴴ := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [pow_succ _ (j + 1), ih]
    calc
      V * M ^ (j + 1) * Vᴴ * (V * M * Vᴴ) =
          V * M ^ (j + 1) * (Vᴴ * V) * M * Vᴴ := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [hV, Matrix.mul_one, Matrix.mul_assoc V, ← pow_succ]

/-- Positive dyadic powers commute exactly with isometric extension by zero. -/
theorem rpow_dyadic_isometry_embedding (V : Matrix n m ℂ) (hV : Vᴴ * V = 1)
    {M : Matrix m m ℂ} (hM : M.PosSemidef) (k ℓ : ℕ) (hℓ : 0 < ℓ) :
    CFC.rpow (V * M * Vᴴ) ((ℓ : ℝ) / (2 : ℝ) ^ k) =
      V * CFC.rpow M ((ℓ : ℝ) / (2 : ℝ) ^ k) * Vᴴ := by
  rw [rpow_dyadic_eq_root_pow k ℓ (hM.mul_mul_conjTranspose_same V),
    rpow_dyadic_eq_root_pow k ℓ hM, dyadicRoot_isometry_embedding V hV hM k]
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hℓ)
  exact pow_succ_isometry_embedding V hV _ j

theorem carrierPower_dyadic_isometry_embedding (V : Matrix n m ℂ) (hV : Vᴴ * V = 1)
    {M : Matrix m m ℂ} (hM : M.PosSemidef) (k : ℕ) (hk : 1 ≤ k) :
    carrierPower ((1 : ℝ) / (2 : ℝ) ^ k) (V * M * Vᴴ) =
      V * carrierPower ((1 : ℝ) / (2 : ℝ) ^ k) M * Vᴴ := by
  have hpow : 1 < (2 : ℕ) ^ k := one_lt_pow₀ (by decide) (Nat.ne_of_gt hk)
  unfold carrierPower
  rw [realTrace_isometry_embedding V hV, dyadic_complement_eq,
    rpow_dyadic_isometry_embedding V hV hM k (2 ^ k - 1) (Nat.sub_pos_of_lt hpow)]
  simp only [Matrix.mul_smul, Matrix.smul_mul]

theorem carrierPower_reconstruct (A : Matrix n n ℂ)
    {S : Matrix (n ⊕ n) (n ⊕ n) ℂ} (hS : S.PosSemidef)
    (k : ℕ) (hk : 1 ≤ k) :
    carrierPower ((1 : ℝ) / (2 : ℝ) ^ k) (carrier A S) =
      atomEmbedding A * carrierPower ((1 : ℝ) / (2 : ℝ) ^ k) (compressedCarrier A S) *
        (atomEmbedding A)ᴴ := by
  rw [← carrier_reconstruct A hS]
  exact carrierPower_dyadic_isometry_embedding _ (atomEmbedding_isometry A)
    (compressedCarrier_posSemidef A hS) k hk

/-- The nonlinear carrier is faithful whenever its carrier input is faithful. -/
theorem carrierPower_posDef (β : ℝ) {M : Matrix m m ℂ} (hM : M.PosDef) :
    (carrierPower β M).PosDef := by
  rcases isEmpty_or_nonempty m with he | hn
  · letI := he
    convert (Matrix.PosDef.one : (1 : Matrix m m ℂ).PosDef) using 1
    exact Subsingleton.elim _ _
  · letI := hn
    have hp : (CFC.rpow M (1 - β)).PosDef := by
      apply (CFC.rpow_nonneg.posSemidef).posDef_iff_isUnit.mpr
      exact hM.isUnit.cfcRpow (1 - β) hM.posSemidef.nonneg
    exact hp.smul (Real.rpow_pos_of_pos (Complex.pos_iff.mp hM.trace_pos).1 β)

def compressedAtom (A : Matrix n n ℂ) :
    Matrix (AtomCarrierIndex A) (AtomCarrierIndex A) ℂ :=
  krausCompressedSource (atomKraus A) 1

theorem compressedAtom_posDef (A : Matrix n n ℂ) : (compressedAtom A).PosDef :=
  krausCompressedSource_posDef _ Matrix.PosDef.one

theorem atom_reconstruct {A : Matrix n n ℂ} (hA : A.PosSemidef) :
    atomEmbedding A * compressedAtom A * (atomEmbedding A)ᴴ = A := by
  have h := krausCompressedSource_reconstruct (atomKraus A) Matrix.PosSemidef.one
  simpa only [atomEmbedding, compressedAtom, atomKraus_channel, Matrix.mul_one,
    CFC.sqrt_mul_sqrt_self A hA.nonneg] using h

theorem sqrt_atom_reconstruct {A : Matrix n n ℂ} (hA : A.PosSemidef) :
    CFC.sqrt A = atomEmbedding A * CFC.sqrt (compressedAtom A) * (atomEmbedding A)ᴴ := by
  have h := sqrt_isometry_embedding (atomEmbedding A) (atomEmbedding_isometry A)
    (compressedAtom_posDef A).posSemidef
  rwa [atom_reconstruct hA] at h

def compressedSourceBlock (β : ℝ) (A : Matrix n n ℂ)
    (S : Matrix (n ⊕ n) (n ⊕ n) ℂ) : Matrix (AtomCarrierIndex A) (AtomCarrierIndex A) ℂ :=
  CFC.sqrt (compressedAtom A) * carrierPower β (compressedCarrier A S) *
    CFC.sqrt (compressedAtom A)

theorem compressedSourceBlock_posDef (β : ℝ) (A : Matrix n n ℂ)
    {S : Matrix (n ⊕ n) (n ⊕ n) ℂ} (hS : S.PosDef) :
    (compressedSourceBlock β A S).PosDef := by
  have hR := (compressedAtom_posDef A).posDef_sqrt
  simpa only [compressedSourceBlock, hR.isHermitian.eq] using
    (carrierPower_posDef β (compressedCarrier_posDef A hS)).conjTranspose_mul_mul_same
      (B := CFC.sqrt (compressedAtom A)) (Matrix.mulVec_injective_iff_isUnit.mpr hR.isUnit)

/-- The physical output is the extension by zero of an actual positive-definite carrier output. -/
theorem sourceBlock_reconstruct {A : Matrix n n ℂ} (hA : A.PosSemidef)
    {S : Matrix (n ⊕ n) (n ⊕ n) ℂ} (hS : S.PosSemidef) (k : ℕ) (hk : 1 ≤ k) :
    sourceBlock ((1 : ℝ) / (2 : ℝ) ^ k) A S =
      atomEmbedding A * compressedSourceBlock ((1 : ℝ) / (2 : ℝ) ^ k) A S *
        (atomEmbedding A)ᴴ := by
  unfold sourceBlock compressedSourceBlock
  rw [sqrt_atom_reconstruct hA, carrierPower_reconstruct A hS k hk]
  calc
    _ = atomEmbedding A * CFC.sqrt (compressedAtom A) *
        ((atomEmbedding A)ᴴ * atomEmbedding A) *
        carrierPower ((1 : ℝ) / (2 : ℝ) ^ k) (compressedCarrier A S) *
        ((atomEmbedding A)ᴴ * atomEmbedding A) * CFC.sqrt (compressedAtom A) *
        (atomEmbedding A)ᴴ := by simp only [Matrix.mul_assoc]
    _ = _ := by simp only [atomEmbedding_isometry, Matrix.mul_one, Matrix.mul_assoc]

omit [DecidableEq n] in
theorem isometry_embedding_mulVec_eq_zero_iff (V : Matrix n m ℂ) (hV : Vᴴ * V = 1)
    {M : Matrix m m ℂ} (hM : M.PosDef) (x : n → ℂ) :
    (V * M * Vᴴ) *ᵥ x = 0 ↔ Vᴴ *ᵥ x = 0 := by
  constructor
  · intro hx
    have h := congrArg (fun y => Vᴴ *ᵥ y) hx
    have hm : M *ᵥ (Vᴴ *ᵥ x) = 0 := by
      simpa only [Matrix.mulVec_mulVec, ← Matrix.mul_assoc, hV, Matrix.one_mul,
        Matrix.mulVec_zero] using h
    exact Matrix.mulVec_injective_of_isUnit hM.isUnit (by simpa using hm)
  · intro hx
    simp only [← Matrix.mulVec_mulVec, hx, Matrix.mulVec_zero]

/-- At a faithful density the nonlinear output has exactly the original atom's kernel. -/
theorem sourceBlock_mulVec_eq_zero_iff {A : Matrix n n ℂ} (hA : A.PosSemidef)
    {S : Matrix (n ⊕ n) (n ⊕ n) ℂ} (hS : S.PosDef) (k : ℕ) (hk : 1 ≤ k)
    (x : n → ℂ) :
    sourceBlock ((1 : ℝ) / (2 : ℝ) ^ k) A S *ᵥ x = 0 ↔ A *ᵥ x = 0 := by
  rw [sourceBlock_reconstruct hA hS.posSemidef k hk,
    isometry_embedding_mulVec_eq_zero_iff _ (atomEmbedding_isometry A)
      (compressedSourceBlock_posDef _ A hS)]
  have h := isometry_embedding_mulVec_eq_zero_iff (atomEmbedding A) (atomEmbedding_isometry A)
    (compressedAtom_posDef A) x
  rw [atom_reconstruct hA] at h
  exact h.symm

def spinAtom (A : Matrix n n ℂ) : Matrix (n ⊕ n) (n ⊕ n) ℂ :=
  Matrix.fromBlocks A 0 0 A

theorem spinAtom_posSemidef {A : Matrix n n ℂ} (hA : A.PosSemidef) :
    (spinAtom A).PosSemidef := posSemidef_fromBlocks_diagonal hA hA

omit [DecidableEq n] in
lemma spinAtom_mulVec_eq_zero_iff (A : Matrix n n ℂ) (x : n ⊕ n → ℂ) :
    spinAtom A *ᵥ x = 0 ↔ A *ᵥ (x ∘ Sum.inl) = 0 ∧ A *ᵥ (x ∘ Sum.inr) = 0 := by
  rw [spinAtom, Matrix.fromBlocks_mulVec]
  simp only [Matrix.zero_mulVec, add_zero, zero_add]
  constructor
  · intro h
    constructor
    · funext i; exact congrFun h (Sum.inl i)
    · funext i; exact congrFun h (Sum.inr i)
  · rintro ⟨hl, hr⟩
    simp [hl, hr]

theorem sourceTerm_mulVec_eq_zero_iff {A : Matrix n n ℂ} (hA : A.PosSemidef)
    {S : Matrix (n ⊕ n) (n ⊕ n) ℂ} (hS : S.PosDef) (k : ℕ) (hk : 1 ≤ k)
    (x : n ⊕ n → ℂ) :
    sourceTerm ((1 : ℝ) / (2 : ℝ) ^ k) A S *ᵥ x = 0 ↔ spinAtom A *ᵥ x = 0 := by
  change spinAtom (sourceBlock ((1 : ℝ) / (2 : ℝ) ^ k) A S) *ᵥ x = 0 ↔ _
  rw [spinAtom_mulVec_eq_zero_iff, spinAtom_mulVec_eq_zero_iff,
    sourceBlock_mulVec_eq_zero_iff hA hS k hk, sourceBlock_mulVec_eq_zero_iff hA hS k hk]

variable {ι : Type*} [Fintype ι]

/-- Positive live coefficients preserve precisely the common original-atom kernel. -/
theorem source_mulVec_eq_zero_iff (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).PosSemidef)
    {c : ι → ℝ} (hc : ∀ i, 0 < c i)
    {S : Matrix (n ⊕ n) (n ⊕ n) ℂ} (hS : S.PosDef) (k : ℕ) (hk : 1 ≤ k)
    (x : n ⊕ n → ℂ) :
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

def sourceEmbedding (A : ι → Matrix n n ℂ) : Matrix (n ⊕ n) (SourceCarrierIndex A) ℂ :=
  krausSupportEmbedding (fun i => spinAtom (A i))

def compressedSource (A : ι → Matrix n n ℂ) (β : ℝ) (c : ι → ℝ)
    (S : Matrix (n ⊕ n) (n ⊕ n) ℂ) : Matrix (SourceCarrierIndex A) (SourceCarrierIndex A) ℂ :=
  (sourceEmbedding A)ᴴ * source A β c S * sourceEmbedding A

/-- The actual total source is faithful on the fixed span of the live atom ranges. -/
theorem compressedSource_posDef (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).PosSemidef)
    {c : ι → ℝ} (hc : ∀ i, 0 < c i)
    {S : Matrix (n ⊕ n) (n ⊕ n) ℂ} (hS : S.PosDef) (k : ℕ) (hk : 1 ≤ k) :
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
  have hIz : krausChannel (fun i => spinAtom (A i)) (1 : Matrix (n ⊕ n) (n ⊕ n) ℂ) *ᵥ
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
    {S : Matrix (n ⊕ n) (n ⊕ n) ℂ} (hS : S.PosDef) (k : ℕ) (hk : 1 ≤ k) :
    LinearMap.ker (Matrix.toEuclideanCLM (n := n ⊕ n) (𝕜 := ℂ)
      (source A ((1 : ℝ) / (2 : ℝ) ^ k) c S)).toLinearMap =
      LinearMap.ker (Matrix.toEuclideanCLM (n := n ⊕ n) (𝕜 := ℂ)
        (krausChannel (fun i => spinAtom (A i)) 1)).toLinearMap := by
  ext x
  have he (M : Matrix (n ⊕ n) (n ⊕ n) ℂ) :
      Matrix.toEuclideanCLM (n := n ⊕ n) (𝕜 := ℂ) M x = 0 ↔ M *ᵥ WithLp.ofLp x = 0 := by
    constructor
    · intro h
      simpa only [Matrix.ofLp_toEuclideanCLM, WithLp.ofLp_zero] using congrArg WithLp.ofLp h
    · intro h
      apply WithLp.ofLp_injective
      simpa only [Matrix.ofLp_toEuclideanCLM, WithLp.ofLp_zero] using h
  change Matrix.toEuclideanCLM (n := n ⊕ n) (𝕜 := ℂ)
    (source A ((1 : ℝ) / (2 : ℝ) ^ k) c S) x = 0 ↔
      Matrix.toEuclideanCLM (n := n ⊕ n) (𝕜 := ℂ)
        (krausChannel (fun i => spinAtom (A i)) 1) x = 0
  simp only [he, source_mulVec_eq_zero_iff A hA hc hS k hk,
    krausChannel_mulVec_eq_zero_iff _ Matrix.PosDef.one,
    fun i => (spinAtom_posSemidef (hA i)).isHermitian.eq]

theorem source_range_eq_support (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).PosSemidef)
    {c : ι → ℝ} (hc : ∀ i, 0 < c i)
    {S : Matrix (n ⊕ n) (n ⊕ n) ℂ} (hS : S.PosDef) (k : ℕ) (hk : 1 ≤ k) :
    LinearMap.range (Matrix.toEuclideanCLM (n := n ⊕ n) (𝕜 := ℂ)
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
    {S : Matrix (n ⊕ n) (n ⊕ n) ℂ} (hS : S.PosDef) (k : ℕ) (hk : 1 ≤ k) :
    (sourceEmbedding A * (sourceEmbedding A)ᴴ) * source A ((1 : ℝ) / (2 : ℝ) ^ k) c S =
      source A ((1 : ℝ) / (2 : ℝ) ^ k) c S := by
  apply (Matrix.toEuclideanCLM (n := n ⊕ n) (𝕜 := ℂ)).injective
  rw [map_mul]
  change Matrix.toEuclideanCLM (n := n ⊕ n) (𝕜 := ℂ)
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
    {S : Matrix (n ⊕ n) (n ⊕ n) ℂ} (hS : S.PosDef) (k : ℕ) (hk : 1 ≤ k) :
    source A ((1 : ℝ) / (2 : ℝ) ^ k) c S * (sourceEmbedding A * (sourceEmbedding A)ᴴ) =
      source A ((1 : ℝ) / (2 : ℝ) ^ k) c S := by
  have h := congrArg Matrix.conjTranspose (source_projection_left A hA hc hS k hk)
  simpa only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
    (source_posSemidef A ((1 : ℝ) / (2 : ℝ) ^ k) (fun i => (hc i).le) hS.posSemidef).isHermitian.eq] using h

theorem compressedSource_reconstruct (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).PosSemidef)
    {c : ι → ℝ} (hc : ∀ i, 0 < c i)
    {S : Matrix (n ⊕ n) (n ⊕ n) ℂ} (hS : S.PosDef) (k : ℕ) (hk : 1 ≤ k) :
    sourceEmbedding A * compressedSource A ((1 : ℝ) / (2 : ℝ) ^ k) c S *
      (sourceEmbedding A)ᴴ = source A ((1 : ℝ) / (2 : ℝ) ^ k) c S := by
  calc
    _ = (sourceEmbedding A * (sourceEmbedding A)ᴴ) *
        source A ((1 : ℝ) / (2 : ℝ) ^ k) c S *
        (sourceEmbedding A * (sourceEmbedding A)ᴴ) := by simp only [compressedSource, Matrix.mul_assoc]
    _ = _ := by rw [source_projection_left A hA hc hS k hk, source_projection_right A hA hc hS k hk]

theorem fidelity_source_compression (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).PosSemidef)
    {c : ι → ℝ} (hc : ∀ i, 0 < c i)
    {S : Matrix (n ⊕ n) (n ⊕ n) ℂ} (hS : S.PosDef) (k : ℕ) (hk : 1 ≤ k) :
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
    (S : Matrix (n ⊕ n) (n ⊕ n) ℂ) :
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

end HigherRankKS
