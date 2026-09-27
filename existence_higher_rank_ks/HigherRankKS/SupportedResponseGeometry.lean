import HigherRankKS.BalancedTransportResponse
import HigherRankKS.SupportedSpin
import MatrixSpencer.KSBalancedSpin

/-! Trace identities for the actual supported and balanced density response. -/

open Matrix MatrixSpencer MatrixSpencer.KSSignSymmetry
open scoped BigOperators MatrixOrder ComplexOrder

noncomputable section
namespace HigherRankKS.BalancedTransportResponse

variable {n : Type*} [Fintype n] [DecidableEq n]

theorem weight_eq_balancedDensity {S M : Matrix n n ℂ}
    (hS : S.PosDef) (hM : M.PosDef) :
    weight S M = balancedDensity S (transportOptimizer S M) :=
  (balancedDensity_eq_source_congruence (transportOptimizer_posDef hS hM)
    (transportOptimizer_solve hS hM)).symm

end HigherRankKS.BalancedTransportResponse

namespace HigherRankKS.SupportedSpin

variable {ι n : Type*} [Fintype ι] [Fintype n] [DecidableEq n]

theorem signed_probe_reconstruct (A : ι → Matrix n n ℂ)
    (hA : ∀ i, (A i).PosSemidef) (i : ι) :
    sourceEmbedding A * (involution A * probe A i) * (sourceEmbedding A)ᴴ =
      signedLift (A i) := by
  rw [← Matrix.mul_assoc (sourceEmbedding A), involution,
    KSSupportSymmetry.intertwine (sourceEmbedding A) (embedding_isometry A)
      signMatrix (projection_commute A hA)]
  rw [Matrix.mul_assoc signMatrix, Matrix.mul_assoc signMatrix,
    probe_reconstruct A hA i]
  simp [signMatrix, spinAtom, signedLift, Matrix.fromBlocks_multiply]

theorem signed_probe_pairing (A : ι → Matrix n n ℂ)
    (hA : ∀ i, (A i).PosSemidef)
    (X : Matrix (n ⊕ n) (n ⊕ n) ℂ) (i : ι) :
    realTrace (signedLift (A i) * X) =
      realTrace ((involution A * probe A i) * density A X) := by
  have ht := KSSafeRetirement.realTrace_embedded_mul
    (sourceEmbedding A) (involution A * probe A i) X
  rw [signed_probe_reconstruct A hA i] at ht
  exact ht

theorem balanced_probe_pairing (A : ι → Matrix n n ℂ)
    (hA : ∀ i, (A i).PosSemidef)
    (X : Matrix (n ⊕ n) (n ⊕ n) ℂ)
    {Z : Matrix (SourceCarrierIndex A) (SourceCarrierIndex A) ℂ} (hZ : Z.PosDef)
    (i : ι) :
    realTrace (spinAtom (A i) * X) =
      realTrace (balancedKraus (probe A) Z i * balancedDensity (density A X) Z) := by
  rw [realTrace_mul_comm (balancedKraus (probe A) Z i), balancedKraus,
    KSBalancedSpin.trace_balanced_pair _ _ hZ]
  exact (probe_pairing A hA X i).symm

theorem balanced_signed_probe_pairing (A : ι → Matrix n n ℂ)
    (hA : ∀ i, (A i).PosSemidef)
    (X : Matrix (n ⊕ n) (n ⊕ n) ℂ)
    {Z : Matrix (SourceCarrierIndex A) (SourceCarrierIndex A) ℂ} (hZ : Z.PosDef)
    (hJZ : Commute (involution A) Z) (i : ι) :
    realTrace (signedLift (A i) * X) =
      realTrace ((involution A * balancedKraus (probe A) Z i) *
        balancedDensity (density A X) Z) := by
  have hJsqrt : involution A * CFC.sqrt Z = CFC.sqrt Z * involution A :=
    (KSSupportSymmetry.commute_sqrt (involution_isHermitian A) (involution_sq A hA)
      hZ.posSemidef hJZ).eq
  have hbal : involution A * balancedKraus (probe A) Z i =
      CFC.sqrt Z * (involution A * probe A i) * CFC.sqrt Z := by
    simp only [balancedKraus, ← Matrix.mul_assoc]
    rw [hJsqrt]
  rw [hbal, realTrace_mul_comm (CFC.sqrt Z * (involution A * probe A i) * CFC.sqrt Z),
    KSBalancedSpin.trace_balanced_pair _ _ hZ,
    realTrace_mul_comm (density A X), signed_probe_pairing A hA X i]

theorem balanced_scalar_force_pairing (A : ι → Matrix n n ℂ)
    (hA : ∀ i, (A i).PosSemidef)
    (X : Matrix (n ⊕ n) (n ⊕ n) ℂ)
    {Z : Matrix (SourceCarrierIndex A) (SourceCarrierIndex A) ℂ} (hZ : Z.PosDef)
    (hJZ : Commute (involution A) Z) (h d q : ι → ℝ) :
    realTrace ((∑ i, h i • signedLift (A i)) * X) +
        (∑ i, h i * d i * q i * realTrace (spinAtom (A i) * X)) =
      realTrace ((∑ i, h i • (involution A * balancedKraus (probe A) Z i +
        (d i * q i) • balancedKraus (probe A) Z i)) *
          balancedDensity (density A X) Z) := by
  simp only [Matrix.sum_mul, Matrix.smul_mul, Matrix.add_mul, realTrace_sum,
    realTrace_add, realTrace_smul, mul_add, Finset.sum_add_distrib]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [balanced_signed_probe_pairing A hA X hZ hJZ i, balanced_probe_pairing A hA X hZ i]
  ring

end HigherRankKS.SupportedSpin
