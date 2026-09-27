import FaithfulMS.DirectAffineArithmetic
import FaithfulMS.SpectralSupport
import FaithfulMS.DirectDensityAmbient

/-! Computing the covariance response from the returned density.

This program forms the covariance source, computes its range projection by
EVD, completes the source and density by the identity on the kernel, solves
the ordinary positive transport equation, and evaluates the Gram entries.
No abstract source basis, derivative, or favorable report is a primitive.
-/
open Matrix
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section
namespace FaithfulMS.DirectGammaArithmetic
open MatrixSpencer
open MatrixSpencer.RealRAM.JacobiIteration (Counted)
open DirectMatrixArithmetic SpectralArithmetic DirectDensityAmbient
local instance {d : ℕ} : CStarAlgebra (Matrix (Fin d) (Fin d) ℂ) := {}
variable {d k : ℕ}
abbrev CMat (d : ℕ) := Matrix (Fin d) (Fin d) ℂ

def transport (S M : CMat d) (hS : S.PosDef) (hM : M.PosDef) : Counted (CMat d) := by
  let R := spectralRoot S hS.isHermitian
  let W := product R.value M
  let N := product W.value R.value
  have hN : N.value.PosDef := by
    dsimp only [N,W,R]
    rw [product_value,product_value,spectralRoot_psd_value S hS.posSemidef]
    have hi : Function.Injective (CFC.sqrt S).mulVec :=
      Matrix.mulVec_injective_iff_isUnit.mpr hS.posDef_sqrt.isUnit
    simpa only [hS.posDef_sqrt.isHermitian.eq] using hM.conjTranspose_mul_mul_same hi
  let K := spectralInverseRoot N.value hN.isHermitian
  let U := product R.value K.value
  let T := product U.value R.value
  exact ⟨T.value,R.cost+W.cost+N.cost+K.cost+U.cost+T.cost⟩

theorem transport_value (S M : CMat d) (hS : S.PosDef) (hM : M.PosDef) :
    (transport S M hS hM).value = transportOptimizer S M := by
  have hN : (CFC.sqrt S*M*CFC.sqrt S).PosDef := by
    have hi : Function.Injective (CFC.sqrt S).mulVec :=
      Matrix.mulVec_injective_iff_isUnit.mpr hS.posDef_sqrt.isUnit
    simpa only [hS.posDef_sqrt.isHermitian.eq] using hM.conjTranspose_mul_mul_same hi
  simp only [transport,product_value,spectralRoot_psd_value S hS.posSemidef]
  rw [spectralInverseRoot_posDef_value _ hN]
  rfl

def transportBudget (d : ℕ) : ℕ := 80*(d+1)^3+4*(d*d*(16*d+4))

theorem transport_cost (S M : CMat d) (hS : S.PosDef) (hM : M.PosDef) :
    (transport S M hS hM).cost ≤ transportBudget d := by
  unfold transport
  dsimp only
  calc
    _ ≤ 40*(d+1)^3 + d*d*(16*d+4) + d*d*(16*d+4) +
        40*(d+1)^3 + d*d*(16*d+4) + d*d*(16*d+4) := by
      gcongr <;> first | exact spectralRoot_cost _ _ | exact product_cost _ _ |
        exact spectralInverseRoot_cost _ _
    _ = _ := by unfold transportBudget; ring

def sourceProjection (A : Fin k → CMat d) (hA : ∀ i, (A i).IsHermitian)
    (C : Matrix (Fin k) (Fin k) ℝ) (hC : C.PosSemidef)
    (S : CMat d) (hS : S.PosDef) : Counted (CMat d) := by
  let M := source A C S
  have hM : M.value.PosSemidef := by
    rw [source_value]
    exact covarianceSource_posSemidef A hA hC hS.posSemidef
  let P := spectralSupport M.value hM.isHermitian
  exact ⟨P.value,M.cost+P.cost⟩

theorem sourceProjection_value (A : Fin k → CMat d) (hA : ∀ i, (A i).IsHermitian)
    (C : Matrix (Fin k) (Fin k) ℝ) (hC : C.PosSemidef)
    (S : CMat d) (hS : S.PosDef) :
    (sourceProjection A hA C hC S hS).value = krausSupportProjection (covarianceKraus A C) := by
  simp only [sourceProjection,spectralSupport_value,source_value]
  rw [covarianceSource_eq_kraus A hA hC,source_support_projection _ hS]

def sourceBudget (k d : ℕ) : ℕ :=
  d*d*(RealRAM.OwnerSDPBlocks.sourceBound k d 2+2)

theorem sourceProjection_cost (A : Fin k → CMat d) (hA : ∀ i, (A i).IsHermitian)
    (C : Matrix (Fin k) (Fin k) ℝ) (hC : C.PosSemidef)
    (S : CMat d) (hS : S.PosDef) :
    (sourceProjection A hA C hC S hS).cost ≤ sourceBudget k d+40*(d+1)^3 := by
  unfold sourceProjection
  dsimp only
  apply Nat.add_le_add
  · simpa only [sourceBudget,Fintype.card_fin] using source_cost A C S
  · exact spectralSupport_cost _ _

def compute (A : Fin k → CMat d) (hA : ∀ i, (A i).IsHermitian)
    (C : Matrix (Fin k) (Fin k) ℝ) (hC : C.PosSemidef)
    (S : CMat d) (hS : S.PosDef) : Counted (Matrix (Fin k) (Fin k) ℝ) := by
  let M := source A C S
  let P := sourceProjection A hA C hC S hS
  let J := complement P.value
  let PS := product P.value S
  let PSP := product PS.value P.value
  let Sbar := addition PSP.value J.value
  let Mbar := addition M.value J.value
  have hD : Sbar.value.PosDef := by
    dsimp only [Sbar,PSP,PS,J,P]
    rw [addition_value,product_value,product_value,complement_value,sourceProjection_value]
    exact completed_density_posDef (covarianceKraus A C) hS
  have hE : Mbar.value.PosDef := by
    dsimp only [Mbar,M,J,P]
    rw [addition_value,source_value,complement_value,sourceProjection_value,
      covarianceSource_eq_kraus A hA hC]
    exact completed_source_posDef (covarianceKraus A C) hS
  let T := transport Sbar.value Mbar.value hD hE
  let PT := product P.value T.value
  let Z := product PT.value P.value
  let G := gram A S Z.value
  exact ⟨G.value,M.cost+P.cost+J.cost+PS.cost+PSP.cost+Sbar.cost+Mbar.cost+
    T.cost+PT.cost+Z.cost+G.cost⟩

theorem compute_value (A : Fin k → CMat d) (hA : ∀ i, (A i).IsHermitian)
    (C : Matrix (Fin k) (Fin k) ℝ) (hC : C.PosSemidef)
    (S : CMat d) (hS : S.PosDef) :
    (compute A hA C hC S hS).value = DirectDensity.gamma A C S := by
  simp only [compute,gram_value,product_value,transport_value,addition_value,
    complement_value,source_value,sourceProjection_value]
  exact (gamma_ambient A hA hC hS).symm

def arithmeticBudget (k d : ℕ) : ℕ :=
  2*sourceBudget k d+40*(d+1)^3+25*d*d+4*(d*d*(16*d+4))+
    transportBudget d+k*k*(gramEntryBound d+1)

theorem compute_cost (A : Fin k → CMat d) (hA : ∀ i, (A i).IsHermitian)
    (C : Matrix (Fin k) (Fin k) ℝ) (hC : C.PosSemidef)
    (S : CMat d) (hS : S.PosDef) :
    (compute A hA C hC S hS).cost ≤ arithmeticBudget k d := by
  unfold compute
  dsimp only
  calc
    _ ≤ sourceBudget k d + (sourceBudget k d+40*(d+1)^3) + 9*d*d +
        d*d*(16*d+4)+d*d*(16*d+4)+8*d*d+8*d*d+transportBudget d+
        d*d*(16*d+4)+d*d*(16*d+4)+k*k*(gramEntryBound d+1) := by
      gcongr
      · simpa only [sourceBudget,Fintype.card_fin] using source_cost A C S
      · exact sourceProjection_cost _ _ _ _ _ _
      · exact complement_cost _
      · exact product_cost _ _
      · exact product_cost _ _
      · exact addition_cost _ _
      · exact addition_cost _ _
      · exact transport_cost _ _ _ _
      · exact product_cost _ _
      · exact product_cost _ _
      · simpa only [Fintype.card_fin] using gram_cost A S _
    _ = _ := by unfold arithmeticBudget; ring

theorem arithmeticBudget_mono {k d K D : ℕ} (hk : k ≤ K) (hd : d ≤ D) :
    arithmeticBudget k d ≤ arithmeticBudget K D := by
  unfold arithmeticBudget sourceBudget transportBudget gramEntryBound
    RealRAM.OwnerSDPBlocks.sourceBound RealRAM.OwnerSDPBlocks.productBound
  gcongr

theorem arithmeticBudget_polynomial (k d : ℕ) :
    arithmeticBudget k d ≤ 20000*(k+d+1)^6 := by
  calc
    _ ≤ arithmeticBudget (k+d) (k+d) := arithmeticBudget_mono (by omega) (by omega)
    _ ≤ _ := by
      unfold arithmeticBudget sourceBudget transportBudget gramEntryBound
        RealRAM.OwnerSDPBlocks.sourceBound RealRAM.OwnerSDPBlocks.productBound
      ring_nf
      omega

end FaithfulMS.DirectGammaArithmetic
