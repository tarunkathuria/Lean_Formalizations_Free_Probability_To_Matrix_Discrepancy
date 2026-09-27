import HigherRankKS.SupportedSpin
import HigherRankKS.SourceDiagonal
import HigherRankKS.BalancedFrames

/-! The carrier diagonal estimate on the actual live source support. -/

open Matrix MatrixSpencer MatrixSpencer.KSSupportSymmetry MatrixSpencer.KSSafeRetirement
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator

noncomputable section
namespace HigherRankKS

variable {n m : Type*} [Fintype n] [Fintype m] [DecidableEq n] [DecidableEq m]

theorem compressed_quadratic_trace (V : Matrix n m ℂ) (hV : Vᴴ * V = 1)
    (S B : Matrix n n ℂ) (B₀ Z : Matrix m m ℂ) (hB : V * B₀ * Vᴴ = B) :
    realTrace (compress V S * B₀ * Z * B₀) =
      realTrace (S * B * (V * Z * Vᴴ) * B) := by
  have hprod : B * (V * Z * Vᴴ) * B = V * (B₀ * Z * B₀) * Vᴴ := by
    rw [← hB]
    calc
      _ = V * B₀ * (Vᴴ * V) * Z * (Vᴴ * V) * B₀ * Vᴴ := by
        simp only [Matrix.mul_assoc]
      _ = _ := by simp only [hV, Matrix.mul_one, Matrix.mul_assoc]
  calc
    _ = realTrace ((B₀ * Z * B₀) * compress V S) := by
      simpa only [Matrix.mul_assoc] using realTrace_mul_comm (compress V S) (B₀ * Z * B₀)
    _ = realTrace (V * (B₀ * Z * B₀) * Vᴴ * S) := (realTrace_embedded_mul V _ S).symm
    _ = realTrace (S * (V * (B₀ * Z * B₀) * Vᴴ)) := realTrace_mul_comm _ S
    _ = _ := by rw [← hprod]; simp only [Matrix.mul_assoc]

namespace SupportedSpin

variable {ι : Type*} [Fintype ι]

theorem actual_supported_diagonal (A : ι → Matrix n n ℂ)
    (hA : ∀ i, (A i).PosSemidef)
    {S : Matrix (n ⊕ n) (n ⊕ n) ℂ} (hS : S.PosSemidef)
    (hblock : S = Matrix.fromBlocks S.toBlocks₁₁ 0 0 S.toBlocks₂₂)
    {Z : Matrix (SourceCarrierIndex A) (SourceCarrierIndex A) ℂ} (hZ : Z.PosSemidef)
    {β : ℝ} (hβ : 0 ≤ β) (hβ1 : β ≤ 1) (i : ι) :
    realTrace (density A S * probe A i * Z * probe A i) ≤
      realTrace (Z * term A β S i) := by
  rw [density, compressed_quadratic_trace (sourceEmbedding A) (embedding_isometry A)
    S (spinAtom (A i)) (probe A i) Z (probe_reconstruct A hA i)]
  have hZE : (sourceEmbedding A * Z * (sourceEmbedding A)ᴴ).PosSemidef :=
    hZ.mul_mul_conjTranspose_same _
  have hh := actual_source_diagonal_bound (hA i) hS hZE hblock hβ hβ1
  rw [realTrace_embedded_mul] at hh
  exact hh

theorem actual_balanced_diagonal (A : ι → Matrix n n ℂ)
    (hA : ∀ i, (A i).PosSemidef) (hne : ∀ i, A i ≠ 0)
    {c : ι → ℝ} (hc : ∀ i, 0 < c i)
    {S : Matrix (n ⊕ n) (n ⊕ n) ℂ} (hS : S.PosDef)
    (hblock : S = Matrix.fromBlocks S.toBlocks₁₁ 0 0 S.toBlocks₂₂)
    (k : ℕ) (hk : 1 ≤ k) (i : ι) :
    let β := (1 : ℝ) / 2 ^ k
    let Z := transport A β c S
    let B := probe A
    let O := term A β S
    let S₀ := density A S
    realTrace (balancedDensity S₀ Z * BalancedFrames.measurementFrame B c Z i *
      BalancedFrames.measurementFrame B c Z i) /
      (BalancedFrames.coefficientMass B c S₀ i / BalancedFrames.probeScale B O c S₀ Z i) ≤
      BalancedFrames.probeScale B O c S₀ Z i ^ 2 := by
  dsimp only
  have hp := BalancedFrames.carrierMass_pos (probe A) (probe_posSemidef A hA)
    (fun i => probe_ne_zero A hA i (hne i)) (density_posDef A hS)
  have hz := transport_posDef A hA hc hS k hk
  have ht := BalancedFrames.transportMass_pos (term A ((1 : ℝ) / 2 ^ k) S)
    (term_posSemidef A _ hS.posSemidef)
    (fun i => term_ne_zero A hA hS k hk i (hne i)) hz
  apply BalancedFrames.weighted_diagonal_le_probe _ _ c hc _ hz hp ht
  intro j
  apply actual_supported_diagonal A hA hS.posSemidef hblock hz.posSemidef
  · positivity
  · exact (div_le_one (by positivity)).mpr (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2))

end SupportedSpin
end HigherRankKS
