import FaithfulMS.DirectSDPDecode
import MatrixSpencer.RealRAMOwnerSDPPolynomialCost
import MatrixSpencer.RectangularRidgeSDPSetup

/-! Counted exact primal-density queries. Affine coefficient construction,
primal optimization, trace-one density decoding, and objective evaluation
are charged separately. No covariance response is supplied by the solver. -/
open Matrix Set
open scoped BigOperators InnerProductSpace MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section
namespace FaithfulMS.DirectSDPArithmetic
open MatrixSpencer RealRAM
open RealRAM.JacobiIteration (Counted)
open DirectSDP

structure PrimalOutput (d : ℕ) where
  density : Matrix (Fin d) (Fin d) ℂ
  value : ℝ

variable {ι : Type} [Fintype ι] [DecidableEq ι] {d : ℕ}

def square (P : PolynomialService) (H : Matrix (Fin d) (Fin d) ℂ)
    (A : ι → Matrix (Fin d) (Fin d) ℂ) (hA : ∀ i, (A i).IsHermitian)
    (C : Matrix ι ι ℝ) (hC : C.PosSemidef) (hd : 0 < d) (θ : ℝ) :
    Counted (PrimalOutput d) :=
  let a : Fin d := ⟨0,hd⟩
  let q := OwnerSDPSetup.setup a H A hA C hC hd θ
  let x := P.run (fun _ : Unit => q.value.data) q.value.coefficient q.value.offset
  let s := DirectSDPDecode.density a
    (fun p => KSFullManuscriptAffineData.entries a x.value (.inl (.inl p)))
  let v := DirectSDPDecode.affine q.value.coefficient x.value q.value.offset
  ⟨⟨s.value,v.value⟩,q.cost+x.cost+s.cost+v.cost⟩

theorem square_density (P : PolynomialService) (H : Matrix (Fin d) (Fin d) ℂ)
    (A : ι → Matrix (Fin d) (Fin d) ℂ) (hA : ∀ i, (A i).IsHermitian)
    (C : Matrix ι ι ℝ) (hC : C.PosSemidef) (hd : 0 < d) (θ : ℝ) (hθ : 0 < θ) :
    (square P H A hA C hC hd θ).value.density =
      (P.service.squareSolution H A hA C hC hd θ hθ).density := by
  dsimp only [square]
  rw [DirectSDPDecode.density_value _ _ hd]
  rfl

theorem square_value (P : PolynomialService) (H : Matrix (Fin d) (Fin d) ℂ)
    (A : ι → Matrix (Fin d) (Fin d) ℂ) (hA : ∀ i, (A i).IsHermitian)
    (C : Matrix ι ι ℝ) (hC : C.PosSemidef) (hd : 0 < d) (θ : ℝ) (hθ : 0 < θ) :
    (square P H A hA C hC hd θ).value.value = ownerPotential H A C θ := by
  let a : Fin d := ⟨0,hd⟩
  let D := squareData a A hA C hC hd
  let c := KSFullManuscriptAffineObjective.coefficient a H θ
  let z := KSFullManuscriptAffineObjective.offset H θ (KSFullManuscriptCenterData.densityCenter hd) 0
  let x := P.service.solve D c z
  have hf (y : KSFullManuscriptAffineData.Space a) :
      y ∈ DirectSDP.feasible D ↔ y ∈ KSFullManuscriptAffinePSD.target
        (OwnerSDPProgramSize.data a A hA C hC (KSFullManuscriptCenterData.densityCenter hd) 0 0) := by
    simp only [DirectSDP.feasible, Set.mem_setOf_eq, D, squareData, KSConvexValueOracle.ownerData,
      forall_const]
  obtain ⟨y,hy,hval,hmax⟩ := OwnerSDPProgramSize.exists_maximizer a H A hA C hC
    (KSFullManuscriptCenterData.densityCenter hd) 0
    (KSFullManuscriptStrictFeasible.density_trace hd) hθ
  have ho := P.service.optimal D c z
    ⟨y,(hf y).mpr hy,fun u hu => hmax u ((hf u).mp hu)⟩
  change z+⟪c,y⟫_ℝ = ownerPotential H A C θ at hval
  have he : z+⟪c,x⟫_ℝ = ownerPotential H A C θ := by
    apply le_antisymm
    · have hu := hmax x ((hf x).mp ho.1)
      change z+⟪c,x⟫_ℝ ≤ z+⟪c,y⟫_ℝ at hu
      rwa [hval] at hu
    · simpa only [hval] using ho.2 y ((hf y).mpr hy)
  dsimp only [square]
  rw [DirectSDPDecode.affine_value]
  exact he

def squareSize (d : ℕ) := (4*d^2+1)*(10*d)^2+4*d^2+2

def squareCost (P : PolynomialService) (r d : ℕ) :=
  1000000*(r+d+1)^9+P.coefficient*(squareSize d+1)^P.degree+
    d*d*(4*d+16)+16*d^2+4

theorem square_cost_le (P : PolynomialService) (H : Matrix (Fin d) (Fin d) ℂ)
    (A : ι → Matrix (Fin d) (Fin d) ℂ) (hA : ∀ i, (A i).IsHermitian)
    (C : Matrix ι ι ℝ) (hC : C.PosSemidef) (hd : 0 < d) (θ : ℝ) :
    (square P H A hA C hC hd θ).cost ≤ squareCost P (Fintype.card ι) d := by
  let a : Fin d := ⟨0,hd⟩
  let q := OwnerSDPSetup.setup a H A hA C hC hd θ
  let x := P.run (fun _ : Unit => q.value.data) q.value.coefficient q.value.offset
  have hq := (OwnerSDPSetup.setup_cost_le a H A hA C hC hd θ).trans
    (OwnerSDPSetup.setupCost_polynomial (Fintype.card ι) d)
  have hdim : KSFullManuscriptAffineData.dimension a ≤ 4*d^2 := by
    rw [KSFullManuscriptProgramSize.variableCount];omega
  have hs : DirectSDP.dataSize (Fintype.card Unit) (KSFullManuscriptAffineData.dimension a)
      (KSFullManuscriptAffineData.matrixSize (Fin d)) ≤ squareSize d := by
    simp only [DirectSDP.dataSize,Fintype.card_unit,Nat.one_mul,squareSize,
      KSFullManuscriptProgramSize.pencilOrder]
    gcongr
  have hx := P.run_cost_le (fun _ : Unit => q.value.data) q.value.coefficient q.value.offset hs
  have hdens := DirectSDPDecode.density_cost_le a
    (fun p => KSFullManuscriptAffineData.entries a x.value (.inl (.inl p)))
  have hv := DirectSDPDecode.affine_cost q.value.coefficient x.value q.value.offset
  change q.cost+x.cost+(DirectSDPDecode.density a
    (fun p => KSFullManuscriptAffineData.entries a x.value (.inl (.inl p)))).cost+
      (DirectSDPDecode.affine q.value.coefficient x.value q.value.offset).cost ≤ _
  change q.cost ≤ _ at hq
  change x.cost ≤ _ at hx
  rw [hv]
  unfold squareCost
  omega


def rectangular (P : PolynomialService) (m : ℕ) (hm : 1 ≤ m)
    (H : Matrix (Fin d) (Fin d) ℂ) (A : ι → Matrix (Fin d) (Fin d) ℂ)
    (hA : ∀ i, (A i).IsHermitian) (C : Matrix ι ι ℝ) (hC : C.PosSemidef)
    (hd : 0 < d) (θ : ℝ) : Counted (PrimalOutput d) :=
  let a : Fin d := ⟨0,hd⟩
  let Cs : selfAdjoint (Matrix ι ι ℝ) := ⟨C,hC.isHermitian⟩
  let q := RectangularRidgeSDPEntries.materialize m hm a (OwnerSDPBlocks.input H A C θ)
  let D := RectangularRidgeSDPEntries.materializedData m hm a H A hA Cs θ
  let c := RectangularRidgeSDPEntries.materializedCoefficient m hm a H A C θ
  let x := P.run D c (q.value.2 none)
  let s := DirectSDPDecode.density a
    (fun p => DyadicSDPCoordinates.entries m a x.value (.inl (.inl p)))
  let v := DirectSDPDecode.affine c x.value (q.value.2 none)
  ⟨⟨s.value,v.value⟩,q.cost+x.cost+s.cost+v.cost⟩

theorem materialized_data (m : ℕ) (hm : 1 ≤ m) (a : Fin d)
    (H : Matrix (Fin d) (Fin d) ℂ) (A : ι → Matrix (Fin d) (Fin d) ℂ)
    (hA : ∀ i, (A i).IsHermitian) (C : Matrix ι ι ℝ) (hC : C.PosSemidef) (θ : ℝ) :
    RectangularRidgeSDPEntries.materializedData m hm a H A hA ⟨C,hC.isHermitian⟩ θ =
      RectangularRidgeConvexValue.ownerData m a A hA C hC :=
  (RectangularRidgeSDPEntries.materializedData_eq m hm a H A hA ⟨C,hC.isHermitian⟩ θ).trans
    (RectangularRidgeSymmetricQueries.data_eq m a A hA ⟨C,hC.isHermitian⟩ hC)

theorem materialized_offset (m : ℕ) (hm : 1 ≤ m) (a : Fin d)
    (H : Matrix (Fin d) (Fin d) ℂ) (A : ι → Matrix (Fin d) (Fin d) ℂ)
    (C : Matrix ι ι ℝ) (θ : ℝ) :
    (RectangularRidgeSDPEntries.materialize m hm a (OwnerSDPBlocks.input H A C θ)).value.2 none =
      RectangularRidgeAffineSDP.offset m hm a H θ (1/d) :=
  RectangularRidgeSDPEntries.objectiveExpr_eval m hm a H A C θ none

theorem center_eq (hd : 0 < d) (a : Fin d) :
    DyadicOwnerSDP.center a = KSFullManuscriptCenterData.densityCenter hd := by
  apply Subtype.ext
  simp [DyadicOwnerSDP.center, KSFullManuscriptCenterData.densityCenter,
    KSFullManuscriptStrictFeasible.density, maximallyMixed, one_div]

theorem rectangular_density (P : PolynomialService) (m : ℕ) (hm : 1 ≤ m)
    (H : Matrix (Fin d) (Fin d) ℂ) (A : ι → Matrix (Fin d) (Fin d) ℂ)
    (hA : ∀ i, (A i).IsHermitian) (C : Matrix ι ι ℝ) (hC : C.PosSemidef)
    (hd : 0 < d) (θ : ℝ) (hθ : 0 < θ) :
    (rectangular P m hm H A hA C hC hd θ).value.density =
      (P.service.rectangularSolution m hm H A hA C hC hd θ (1/d) hθ (by positivity)).density := by
  dsimp only [rectangular]
  rw [DirectSDPDecode.density_value _ _ hd]
  rw [materialized_data m hm ⟨0,hd⟩ H A hA C hC θ]
  simp only [RectangularRidgeSDPEntries.materializedCoefficient_eq, materialized_offset]
  change _ = (DyadicOwnerSDP.center (⟨0,hd⟩ : Fin d) : Matrix (Fin d) (Fin d) ℂ) + _
  rw [center_eq hd]
  rfl

theorem rectangular_value (P : PolynomialService) (m : ℕ) (hm : 1 ≤ m)
    (H : Matrix (Fin d) (Fin d) ℂ) (A : ι → Matrix (Fin d) (Fin d) ℂ)
    (hA : ∀ i, (A i).IsHermitian) (C : Matrix ι ι ℝ) (hC : C.PosSemidef)
    (hd : 0 < d) (θ : ℝ) (hθ : 0 < θ) :
    (rectangular P m hm H A hA C hC hd θ).value.value =
      RectangularRidgePotential.potential H (covarianceKraus A C) m θ (1/d) := by
  let a : Fin d := ⟨0,hd⟩
  let D := RectangularRidgeConvexValue.ownerData m a A hA C hC
  let c := RectangularRidgeAffineSDP.coefficient m hm a H θ (1/d)
  let z := RectangularRidgeAffineSDP.offset m hm a H θ (1/d)
  let x := P.service.solve D c z
  obtain ⟨y,hy,hval,hmax⟩ := RectangularRidgeAffineSDP.exists_maximizer m hm a H A hA C hC hθ
    (show (0 : ℝ) ≤ 1/d by positivity)
  have ho := P.service.optimal D c z ⟨y,hy,hmax⟩
  change z+⟪c,y⟫_ℝ = _ at hval
  have he : z+⟪c,x⟫_ℝ = RectangularRidgePotential.potential H (covarianceKraus A C) m θ (1/d) := by
    apply le_antisymm
    · have hu := hmax x ho.1
      change z+⟪c,x⟫_ℝ ≤ z+⟪c,y⟫_ℝ at hu
      rwa [hval] at hu
    · simpa only [hval] using ho.2 y hy
  dsimp only [rectangular]
  rw [DirectSDPDecode.affine_value]
  rw [materialized_data m hm ⟨0,hd⟩ H A hA C hC θ]
  simpa only [RectangularRidgeSDPEntries.materializedCoefficient_eq, materialized_offset] using he

def rectangularSize (m d : ℕ) := (2*m+1)*((m+3)*d^2+1)*(4*d)^2+(m+3)*d^2+2

def rectangularCost (P : PolynomialService) (r m d : ℕ) :=
  1000000*(r+m+d+1)^11+P.coefficient*(rectangularSize m d+1)^P.degree+
    d*d*(4*d+16)+4*(m+3)*d^2+4

theorem rectangular_cost_le (P : PolynomialService) (m : ℕ) (hm : 1 ≤ m)
    (H : Matrix (Fin d) (Fin d) ℂ) (A : ι → Matrix (Fin d) (Fin d) ℂ)
    (hA : ∀ i, (A i).IsHermitian) (C : Matrix ι ι ℝ) (hC : C.PosSemidef)
    (hd : 0 < d) (θ : ℝ) :
    (rectangular P m hm H A hA C hC hd θ).cost ≤ rectangularCost P (Fintype.card ι) m d := by
  let a : Fin d := ⟨0,hd⟩
  let Cs : selfAdjoint (Matrix ι ι ℝ) := ⟨C,hC.isHermitian⟩
  let q := RectangularRidgeSDPEntries.materialize m hm a (OwnerSDPBlocks.input H A C θ)
  let D := RectangularRidgeSDPEntries.materializedData m hm a H A hA Cs θ
  let c := RectangularRidgeSDPEntries.materializedCoefficient m hm a H A C θ
  let x := P.run D c (q.value.2 none)
  have hq := (RectangularRidgeSDPEntries.materialize_cost_le m hm a (OwnerSDPBlocks.input H A C θ)).trans
    (RectangularRidgeSDPEntries.setupCost_polynomial (Fintype.card ι) m d)
  have hdim : DyadicSDPCoordinates.dimension m a ≤ (m+3)*d^2 := by
    rw [DyadicSDPCoordinates.dimension_eq];simp only [Fintype.card_fin];omega
  have hs : DirectSDP.dataSize (Fintype.card (DyadicSDPAffineData.Constraint m))
      (DyadicSDPCoordinates.dimension m a) (DyadicSDPAffineData.matrixSize (Fin d)) ≤ rectangularSize m d := by
    have hc : Fintype.card (DyadicSDPAffineData.Constraint m) = 2*m+1 := by
      simp [DyadicSDPAffineData.Constraint];omega
    simp only [DirectSDP.dataSize,hc,DyadicSDPAffineData.matrixSize_eq,Fintype.card_fin,rectangularSize]
    gcongr
  have hx := P.run_cost_le D c (q.value.2 none) hs
  have hdens := DirectSDPDecode.density_cost_le a
    (fun p => DyadicSDPCoordinates.entries m a x.value (.inl (.inl p)))
  have hv := DirectSDPDecode.affine_cost c x.value (q.value.2 none)
  change q.cost+x.cost+(DirectSDPDecode.density a
    (fun p => DyadicSDPCoordinates.entries m a x.value (.inl (.inl p)))).cost+
      (DirectSDPDecode.affine c x.value (q.value.2 none)).cost ≤ _
  change q.cost ≤ _ at hq
  change x.cost ≤ _ at hx
  rw [hv]
  unfold rectangularCost
  have hfour : 4 * DyadicSDPCoordinates.dimension m a ≤ 4*(m+3)*d^2 := by
    simpa only [Nat.mul_assoc] using Nat.mul_le_mul_left 4 hdim
  omega

end FaithfulMS.DirectSDPArithmetic
