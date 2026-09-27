import MatrixSpencer.DyadicSDPCoordinates
import MatrixSpencer.DyadicOwnerSDPIdentity
import MatrixSpencer.KSFullManuscriptWeakOptimization
import MatrixSpencer.OwnerSDPProgramSize

/-! The rectangular dyadic owner SDP as explicit affine real symmetric
matrix inequalities. Each of its 2m+1 complex blocks has order 2d and is
realified to order 4d. The coefficients use the original covariance entries;
constructing them requires no matrix powers, eigenvectors, or matrix roots. -/
open Matrix
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section
namespace MatrixSpencer.DyadicSDPAffineData
open DyadicSDPCoordinates DyadicSDPTracePower
open KSFullManuscriptSDPBlockPencil KSComplexTraceSqrt KSComplexProjectionGeometry
variable {n ι : Type*} [Fintype n] [LinearOrder n] [Fintype ι] [DecidableEq ι]
set_option maxHeartbeats 800000
abbrev Constraint (m : ℕ) := Unit ⊕ (Fin m ⊕ Fin m)
abbrev RealIndex (n : Type*) := (n ⊕ n) ⊕ (n ⊕ n)
abbrev matrixSize (n : Type*) [Fintype n] := Fintype.card (RealIndex n)

def block (A : ι → Matrix n n ℂ) (C : Matrix ι ι ℝ) (m : ℕ)
    (S : Matrix n n ℂ) (X : Fin (m+1) → Matrix n n ℂ) (Z : Matrix n n ℂ) :
    Constraint m → Matrix (n ⊕ n) (n ⊕ n) ℂ :=
  Sum.elim (fun _ => Matrix.fromBlocks S Z Zᴴ (covarianceSource A C S))
    (Sum.elim (fun j => Matrix.fromBlocks S (X j.succ) (X j.succ) (X j.castSucc))
      (fun j => Matrix.fromBlocks (X j.succ) 0 0 0))

theorem source_add (A : ι → Matrix n n ℂ) (C : Matrix ι ι ℝ) (S T : Matrix n n ℂ) :
    covarianceSource A C (S+T)=covarianceSource A C S+covarianceSource A C T := by
  simp only [covarianceSource, Matrix.mul_add, Matrix.add_mul, smul_add, Finset.sum_add_distrib]

theorem source_smul (A : ι → Matrix n n ℂ) (C : Matrix ι ι ℝ) (r : ℝ) (S : Matrix n n ℂ) :
    covarianceSource A C (r • S)=r • covarianceSource A C S := by
  simp only [covarianceSource, Matrix.mul_smul, Matrix.smul_mul, Finset.smul_sum]
  congr 1
  funext i
  congr 1
  funext j
  exact smul_comm _ _ _

theorem source_hermitian (A : ι → Matrix n n ℂ) (hA : ∀i,(A i).IsHermitian)
    {C : Matrix ι ι ℝ} (hC : C.PosSemidef) {S : Matrix n n ℂ} (hS : S.IsHermitian) :
    (covarianceSource A C S).IsHermitian := by
  rw [covarianceSource_eq_kraus A hA hC]
  exact channel_hermitian _ hS

theorem block_add (A : ι → Matrix n n ℂ) (C : Matrix ι ι ℝ) (m : ℕ)
    (S T : Matrix n n ℂ) (X Y : Fin (m+1) → Matrix n n ℂ) (Z W : Matrix n n ℂ)
    (b : Constraint m) :
    block A C m (S+T) (X+Y) (Z+W) b=block A C m S X Z b+block A C m T Y W b := by
  rcases b with u | (j|j) <;>
    simp only [block, Sum.elim_inl, Sum.elim_inr, Pi.add_apply,
      Matrix.conjTranspose_add, source_add, Matrix.fromBlocks_add, add_zero]

theorem block_smul (A : ι → Matrix n n ℂ) (C : Matrix ι ι ℝ) (m : ℕ) (r : ℝ)
    (S : Matrix n n ℂ) (X : Fin (m+1) → Matrix n n ℂ) (Z : Matrix n n ℂ)
    (b : Constraint m) :
    block A C m (r • S) (r • X) (r • Z) b=r • block A C m S X Z b := by
  rcases b with u | (j|j) <;>
    simp only [block, Sum.elim_inl, Sum.elim_inr, Pi.smul_apply,
      Matrix.conjTranspose_smul, star_trivial, source_smul, Matrix.fromBlocks_smul, smul_zero]

theorem block_hermitian (A : ι → Matrix n n ℂ) (hA : ∀i,(A i).IsHermitian)
    {C : Matrix ι ι ℝ} (hC : C.PosSemidef) (m : ℕ)
    {S : Matrix n n ℂ} (hS : S.IsHermitian) {X : Fin (m+1) → Matrix n n ℂ}
    (hX : ∀j,(X j).IsHermitian) (Z : Matrix n n ℂ) (b : Constraint m) :
    (block A C m S X Z b).IsHermitian := by
  rcases b with u | (j|j)
  · exact Matrix.IsHermitian.fromBlocks hS rfl (source_hermitian A hA hC hS)
  · exact Matrix.IsHermitian.fromBlocks hS (hX j.succ).eq (hX j.castSucc)
  · exact Matrix.IsHermitian.fromBlocks (hX j.succ) (by simp) Matrix.isHermitian_zero

def complexLinear (m : ℕ) (a : n) (A : ι → Matrix n n ℂ) (C : Matrix ι ι ℝ)
    (b : Constraint m) : (Index m a → ℝ) →ₗ[ℝ] Matrix (n ⊕ n) (n ⊕ n) ℂ where
  toFun x := block A C m (densityLinear m a x) (fun j => chainLinear m a j x) (fidelityLinear m a x) b
  map_add' x y := by
    change block A C m (densityLinear m a (x+y)) (fun j => chainLinear m a j (x+y))
      (fidelityLinear m a (x+y)) b = _
    simp only [map_add]
    exact block_add A C m _ _ _ _ _ _ b
  map_smul' r x := by
    change block A C m (densityLinear m a (r • x)) (fun j => chainLinear m a j (r • x))
      (fidelityLinear m a (r • x)) b = _
    simp only [map_smul, RingHom.id_apply]
    exact block_smul A C m r _ _ _ b

def realLinear (m : ℕ) (a : n) (A : ι → Matrix n n ℂ) (C : Matrix ι ι ℝ)
    (b : Constraint m) : (Index m a → ℝ) →ₗ[ℝ] Matrix (RealIndex n) (RealIndex n) ℝ where
  toFun x := realification (complexLinear m a A C b x)
  map_add' x y := by rw [map_add, realification_add]
  map_smul' r x := by rw [map_smul, realification_smul]; rfl

def finiteLinear (m : ℕ) (a : n) (A : ι → Matrix n n ℂ) (C : Matrix ι ι ℝ)
    (b : Constraint m) : Space m a →ₗ[ℝ] Matrix (Fin (matrixSize n)) (Fin (matrixSize n)) ℝ where
  toFun x := (realLinear m a A C b (entries m a x)).submatrix
    (Fintype.equivFin (RealIndex n)).symm (Fintype.equivFin (RealIndex n)).symm
  map_add' x y := by
    change (realLinear m a A C b (entries m a x+entries m a y)).submatrix _ _ = _
    rw [map_add, Matrix.submatrix_add]
    rfl
  map_smul' r x := by
    change (realLinear m a A C b (r • entries m a x)).submatrix _ _ = _
    rw [map_smul, Matrix.submatrix_smul]
    rfl

def constant (m : ℕ) (a : n) (A : ι → Matrix n n ℂ) (C : Matrix ι ι ℝ)
    (S₀ : selfAdjoint (Matrix n n ℂ)) (b : Constraint m) :=
  (realification (block A C m S₀ (chain m a 0) 0 b)).submatrix
    (Fintype.equivFin (RealIndex n)).symm (Fintype.equivFin (RealIndex n)).symm

/-- Actual finite real affine data for each matrix inequality. -/
def data (m : ℕ) (a : n) (A : ι → Matrix n n ℂ) (hA : ∀i,(A i).IsHermitian)
    (C : Matrix ι ι ℝ) (hC : C.PosSemidef) (S₀ : selfAdjoint (Matrix n n ℂ))
    (b : Constraint m) : KSFullManuscriptAffinePSD.Data (dimension m a) (matrixSize n) where
  constant := constant m a A C S₀ b
  coefficient i := finiteLinear m a A C b (unit m a i)
  constant_symmetric := (realification_symmetric _
    (block_hermitian A hA hC m S₀.property (chain_hermitian m a 0) 0 b)).submatrix _
  coefficient_symmetric i := (realification_symmetric _
    (block_hermitian A hA hC m (densityLinear m a _).property
      (chainLinear_hermitian m a _) _ b)).submatrix _

theorem matrixAt_eq (m : ℕ) (a : n) (A : ι → Matrix n n ℂ) (hA : ∀i,(A i).IsHermitian)
    (C : Matrix ι ι ℝ) (hC : C.PosSemidef) (S₀ : selfAdjoint (Matrix n n ℂ))
    (b : Constraint m) (x : Space m a) :
    KSFullManuscriptAffinePSD.matrixAt (data m a A hA C hC S₀ b) x =
      constant m a A C S₀ b+finiteLinear m a A C b x := by
  change constant m a A C S₀ b + ∑i,x i • finiteLinear m a A C b (unit m a i) = _
  have hh := congrArg (finiteLinear m a A C b) (sum_units m a x)
  simpa only [map_sum, map_smul] using congrArg (fun M => constant m a A C S₀ b+M) hh

theorem matrixAt_physical (m : ℕ) (a : n) (A : ι → Matrix n n ℂ) (hA : ∀i,(A i).IsHermitian)
    (C : Matrix ι ι ℝ) (hC : C.PosSemidef) (S₀ : selfAdjoint (Matrix n n ℂ))
    (b : Constraint m) (x : Space m a) :
    KSFullManuscriptAffinePSD.matrixAt (data m a A hA C hC S₀ b) x =
      (realification (block A C m (density m a S₀ (entries m a x))
        (chain m a (entries m a x)) (fidelityLinear m a (entries m a x)) b)).submatrix
        (Fintype.equivFin (RealIndex n)).symm (Fintype.equivFin (RealIndex n)).symm := by
  rw [matrixAt_eq]
  change (realification (block A C m S₀ (chain m a 0) 0 b)).submatrix _ _ +
    (realification (block A C m (densityLinear m a (entries m a x))
      (fun j => chainLinear m a j (entries m a x)) (fidelityLinear m a (entries m a x)) b)).submatrix _ _ = _
  change (realification (block A C m S₀ (chain m a 0) 0 b) +
    realification (block A C m (densityLinear m a (entries m a x))
      (fun j => chainLinear m a j (entries m a x)) (fidelityLinear m a (entries m a x)) b)).submatrix _ _ = _
  rw [← realification_add, ← block_add]
  have hc : chain m a 0+(fun j => chainLinear m a j (entries m a x))=chain m a (entries m a x) := by
    funext j
    simpa only [zero_add] using (chain_affine m a 0 (entries m a x) j).symm
  rw [hc,zero_add]
  rfl

def target (m : ℕ) (a : n) (A : ι → Matrix n n ℂ) (hA : ∀i,(A i).IsHermitian)
    (C : Matrix ι ι ℝ) (hC : C.PosSemidef) (S₀ : selfAdjoint (Matrix n n ℂ)) : Set (Space m a) :=
  {x | ∀b, x ∈ KSFullManuscriptAffinePSD.target (data m a A hA C hC S₀ b)}

theorem convex_target (m : ℕ) (a : n) (A : ι → Matrix n n ℂ) (hA : ∀i,(A i).IsHermitian)
    (C : Matrix ι ι ℝ) (hC : C.PosSemidef) (S₀ : selfAdjoint (Matrix n n ℂ)) :
    Convex ℝ (target m a A hA C hC S₀) := by
  intro x hx y hy r s hr hs hrs b
  exact KSFullManuscriptWeakOptimization.base_convex _ (hx b) (hy b) hr hs hrs

theorem target_iff (m : ℕ) (a : n) (A : ι → Matrix n n ℂ) (hA : ∀i,(A i).IsHermitian)
    (C : Matrix ι ι ℝ) (hC : C.PosSemidef) (S₀ : selfAdjoint (Matrix n n ℂ))
    (htr : realTrace (S₀ : Matrix n n ℂ)=1) (x : Space m a) :
    x ∈ target m a A hA C hC S₀ ↔ DyadicOwnerSDPIdentity.Feasible (covarianceSource A C) m
      (density m a S₀ (entries m a x)) (chain m a (entries m a x)) (fidelityLinear m a (entries m a x)) := by
  have he (b : Constraint m) : x ∈ KSFullManuscriptAffinePSD.target (data m a A hA C hC S₀ b) ↔
      (block A C m (density m a S₀ (entries m a x)) (chain m a (entries m a x))
        (fidelityLinear m a (entries m a x)) b).PosSemidef := by
    change (KSFullManuscriptAffinePSD.matrixAt _ x).PosSemidef ↔ _
    rw [matrixAt_physical, Matrix.posSemidef_submatrix_equiv]
    exact ⟨realification_reflects_posSemidef _, realification_posSemidef _⟩
  constructor
  · intro hx
    have hf := (he (.inl ())).mp (hx (.inl ()))
    refine ⟨⟨?_, (density_trace m a S₀ _).trans htr⟩, ⟨chain_zero m a _, ?_⟩, hf⟩
    · simpa only [block, Sum.elim_inl, Matrix.submatrix, Matrix.fromBlocks_apply₁₁] using hf.submatrix Sum.inl
    · intro j
      exact ⟨(diagonal_psd_iff.mp ((he (.inr (.inr j))).mp (hx (.inr (.inr j))))).1,
        (he (.inr (.inl j))).mp (hx (.inr (.inl j)))⟩
  · intro hx b
    apply (he b).mpr
    rcases b with u | (j|j)
    · exact hx.2.2
    · exact (hx.2.1.2 j).2
    · exact diagonal_psd_iff.mpr ⟨(hx.2.1.2 j).1, Matrix.PosSemidef.zero⟩

theorem constraint_count (m : ℕ) : Fintype.card (Constraint m)=2*m+1 := by
  simp only [Constraint,Fintype.card_sum,Fintype.card_unit,Fintype.card_fin]
  omega

theorem matrixSize_eq : matrixSize n=4*Fintype.card n := by
  simp only [matrixSize,RealIndex,Fintype.card_sum]
  omega
end MatrixSpencer.DyadicSDPAffineData
