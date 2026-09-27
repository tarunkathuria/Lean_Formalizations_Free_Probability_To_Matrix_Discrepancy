import MatrixSpencer.KSFullManuscriptProgramSize
import MatrixSpencer.OwnerPotential

/-!
# Direct covariance SDP data and its exact size

This is the SDP for the actual owner value, with source
`sum i,j, C i j • (A i * S * A j)`. Its data definitions use finite matrix
arithmetic only. The equality to the Kraus pencil is a proof and does not
require constructing a covariance square root to form the coefficients.

The existing chart eliminates the density trace equality and covers every
physical feasible triple. There is one real PSD constraint; an objective
threshold query adds one affine scalar inequality. These are program-size
and representation results, not a complexity theorem for the current finite
projected-gradient value-report implementation.
-/

open Matrix
open scoped BigOperators InnerProductSpace MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section
namespace MatrixSpencer.OwnerSDPProgramSize

open KSFullManuscriptSDPCoordinates KSFullManuscriptAffineData
open KSFullManuscriptSDPBlockPencil KSFullManuscriptAffineObjective
open KSFullManuscriptSDPIdentity KSComplexTraceSqrt
variable {n ι : Type*} [Fintype n] [LinearOrder n] [Fintype ι] [DecidableEq ι]

def block (A : ι → Matrix n n ℂ) (C : Matrix ι ι ℝ) (lam : ℝ)
    (S Y Z : Matrix n n ℂ) : Matrix (ComplexIndex n) (ComplexIndex n) ℂ :=
  Matrix.fromBlocks Y 0 0 (Matrix.fromBlocks
    (Matrix.fromBlocks S Z Zᴴ (covarianceSource A C S + lam • 1)) 0 0
    (Matrix.fromBlocks S Y Y 1))

def delta (A : ι → Matrix n n ℂ) (C : Matrix ι ι ℝ)
    (S Y Z : Matrix n n ℂ) : Matrix (ComplexIndex n) (ComplexIndex n) ℂ :=
  Matrix.fromBlocks Y 0 0 (Matrix.fromBlocks
    (Matrix.fromBlocks S Z Zᴴ (covarianceSource A C S)) 0 0
    (Matrix.fromBlocks S Y Y 0))

theorem block_eq (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).IsHermitian)
    {C : Matrix ι ι ℝ} (hC : C.PosSemidef) (lam : ℝ) (S Y Z : Matrix n n ℂ) :
    block A C lam S Y Z = KSFullManuscriptSDPBlockPencil.block (covarianceKraus A C) lam S Y Z := by
  simp only [block, KSFullManuscriptSDPBlockPencil.block, covarianceSource_eq_kraus A hA hC]

omit [LinearOrder n] in
theorem delta_eq (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).IsHermitian)
    {C : Matrix ι ι ℝ} (hC : C.PosSemidef) (S Y Z : Matrix n n ℂ) :
    delta A C S Y Z = deltaBlock (covarianceKraus A C) S Y Z := by
  simp only [delta, deltaBlock, covarianceSource_eq_kraus A hA hC]

def constant (_a : n) (A : ι → Matrix n n ℂ) (C : Matrix ι ι ℝ)
    (S₀ Y₀ : selfAdjoint (Matrix n n ℂ)) (lam : ℝ) :=
  (realification (block A C lam S₀ Y₀ 0)).submatrix
    (Fintype.equivFin (RealIndex n)).symm (Fintype.equivFin (RealIndex n)).symm

def coefficient (a : n) (A : ι → Matrix n n ℂ) (C : Matrix ι ι ℝ)
    (i : Fin (dimension a)) :=
  (realification (delta A C
    (densityLinear a (entries a (unit a i))) (regularizerLinear a (entries a (unit a i)))
    (fidelityLinear a (entries a (unit a i))))).submatrix
    (Fintype.equivFin (RealIndex n)).symm (Fintype.equivFin (RealIndex n)).symm

theorem constant_eq (a : n) (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).IsHermitian)
    {C : Matrix ι ι ℝ} (hC : C.PosSemidef) (S₀ Y₀ : selfAdjoint (Matrix n n ℂ)) (lam : ℝ) :
    constant a A C S₀ Y₀ lam = KSFullManuscriptAffineData.constant a (covarianceKraus A C) S₀ Y₀ lam := by
  simp only [constant, KSFullManuscriptAffineData.constant, block_eq A hA hC]

theorem coefficient_eq (a : n) (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).IsHermitian)
    {C : Matrix ι ι ℝ} (hC : C.PosSemidef) (i : Fin (dimension a)) :
    coefficient a A C i = finiteLinear a (covarianceKraus A C) (unit a i) := by
  simp only [coefficient, delta_eq A hA hC]
  rfl

/-- Explicit affine matrix coefficients in the original covariance inputs. -/
def data (a : n) (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).IsHermitian)
    (C : Matrix ι ι ℝ) (hC : C.PosSemidef) (S₀ Y₀ : selfAdjoint (Matrix n n ℂ)) (lam : ℝ) :
    KSFullManuscriptAffinePSD.Data (dimension a) (matrixSize n) where
  constant := constant a A C S₀ Y₀ lam
  coefficient := coefficient a A C
  constant_symmetric := by
    rw [constant_eq a A hA hC]
    exact constant_symmetric a _ S₀ Y₀ lam
  coefficient_symmetric i := by
    rw [coefficient_eq a A hA hC]
    exact finiteLinear_symmetric a _ _

theorem data_eq (a : n) (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).IsHermitian)
    (C : Matrix ι ι ℝ) (hC : C.PosSemidef) (S₀ Y₀ : selfAdjoint (Matrix n n ℂ)) (lam : ℝ) :
    data a A hA C hC S₀ Y₀ lam = KSFullManuscriptAffineData.data a (covarianceKraus A C) S₀ Y₀ lam := by
  have hc := constant_eq a A hA hC S₀ Y₀ lam
  have hi : coefficient a A C = fun i => finiteLinear a (covarianceKraus A C) (unit a i) :=
    funext (coefficient_eq a A hA hC)
  simp only [data, KSFullManuscriptAffineData.data, hc, hi]

theorem convex_target (a : n) (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).IsHermitian)
    (C : Matrix ι ι ℝ) (hC : C.PosSemidef) (S₀ Y₀ : selfAdjoint (Matrix n n ℂ)) (lam : ℝ) :
    Convex ℝ (KSFullManuscriptAffinePSD.target (data a A hA C hC S₀ Y₀ lam)) :=
  KSFullManuscriptWeakOptimization.base_convex _

theorem target_iff (a : n) (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).IsHermitian)
    (C : Matrix ι ι ℝ) (hC : C.PosSemidef) (S₀ Y₀ : selfAdjoint (Matrix n n ℂ))
    (htr : realTrace (S₀ : Matrix n n ℂ) = 1) (lam : ℝ) (x : Space a) :
    x ∈ KSFullManuscriptAffinePSD.target (data a A hA C hC S₀ Y₀ lam) ↔
      Feasible (covarianceSource A C) lam (density a S₀ (entries a x))
        (regularizer a Y₀ (entries a x)) (fidelityLinear a (entries a x)) := by
  rw [data_eq, KSFullManuscriptAffineData.target_iff a _ S₀ Y₀ htr]
  simp only [Feasible, covarianceSource_eq_kraus A hA hC]

/-- The unregularized direct-input SDP has a true maximum equal to the owner
potential used by the numerical MS and eighth-cube KS reports. -/
theorem exists_maximizer (a : n) (H : Matrix n n ℂ) (A : ι → Matrix n n ℂ)
    (hA : ∀ i, (A i).IsHermitian) (C : Matrix ι ι ℝ) (hC : C.PosSemidef)
    (S₀ Y₀ : selfAdjoint (Matrix n n ℂ)) (htr : realTrace (S₀ : Matrix n n ℂ) = 1)
    {θ : ℝ} (hθ : 0 < θ) :
    ∃ x : Space a, x ∈ KSFullManuscriptAffinePSD.target (data a A hA C hC S₀ Y₀ 0) ∧
      offset H θ S₀ Y₀ + ⟪KSFullManuscriptAffineObjective.coefficient a H θ, x⟫_ℝ =
        ownerPotential H A C θ ∧
      ∀ y ∈ KSFullManuscriptAffinePSD.target (data a A hA C hC S₀ Y₀ 0),
        offset H θ S₀ Y₀ + ⟪KSFullManuscriptAffineObjective.coefficient a H θ, y⟫_ℝ ≤
        offset H θ S₀ Y₀ + ⟪KSFullManuscriptAffineObjective.coefficient a H θ, x⟫_ℝ := by
  letI : Nonempty n := ⟨a⟩
  rw [data_eq, ownerPotential_eq_densityPotential H A hA hC]
  obtain ⟨S,Y,Z,hF,hval,hmax⟩ := original_SDP_exact H (covarianceKraus A C) hθ
  let hs : selfAdjoint (Matrix n n ℂ) := ⟨S, (feasible_density hF).1.isHermitian⟩
  let hy : selfAdjoint (Matrix n n ℂ) := ⟨Y, hF.2.1.isHermitian⟩
  let x := coordinates a (encode a S₀ Y₀ hs hy Z)
  have hS : density a S₀ (entries a x) = hs := by
    rw [entries_coordinates]
    exact density_encode a S₀ Y₀ hs hy Z (hF.1.trans htr.symm)
  have hY : regularizer a Y₀ (entries a x) = hy := by
    rw [entries_coordinates]
    exact regularizer_encode a S₀ Y₀ hs hy Z
  have hZ : fidelityLinear a (entries a x) = Z := by
    rw [entries_coordinates]
    exact fidelity_encode a S₀ Y₀ hs hy Z
  have hx : x ∈ KSFullManuscriptAffinePSD.target
      (KSFullManuscriptAffineData.data a (covarianceKraus A C) S₀ Y₀ 0) := by
    rw [KSFullManuscriptAffineData.target_iff a _ S₀ Y₀ htr, hS, hY, hZ]
    exact hF
  have hv : value H θ S Y Z = offset H θ S₀ Y₀ +
      ⟪KSFullManuscriptAffineObjective.coefficient a H θ, x⟫_ℝ := by
    have hh := value_eq_affine a H θ S₀ Y₀ x
    simpa only [hS, hY, hZ, hs, hy] using hh
  refine ⟨x, hx, hv.symm.trans hval, ?_⟩
  intro y hy'
  rw [← value_eq_affine, ← hv]
  exact hmax _ _ _ ((KSFullManuscriptAffineData.target_iff a _ S₀ Y₀ htr 0 y).mp hy')

/-- Original real input entries for `H`, all atoms, and the covariance. -/
theorem inputEntries (N d : ℕ) :
    2 * Fintype.card (Fin d × Fin d) +
      2 * Fintype.card (Fin N × (Fin d × Fin d)) +
      Fintype.card (Fin N × Fin N) = 2 * d^2 + 2 * N * d^2 + N^2 := by
  simp only [Fintype.card_prod, Fintype.card_fin]
  ring

end MatrixSpencer.OwnerSDPProgramSize
