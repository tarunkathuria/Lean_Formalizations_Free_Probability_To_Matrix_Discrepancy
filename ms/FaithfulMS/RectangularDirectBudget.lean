import FaithfulMS.RectangularDirectOriginalRuntime
import FaithfulMS.RectangularDirectPolynomialMajorant
noncomputable section
namespace MatrixSpencer.RectangularDirectBudget
open RectangularDirectOriginalRuntime
private theorem doubled_bounded {f : ℕ → ℕ → ℕ → ℕ} (hf : NatPolynomialBound.Bounded f) :
    NatPolynomialBound.Bounded (fun N D k => f N (D + D) k) := by
  obtain ⟨C, e, hf⟩ := hf
  refine ⟨C * 2 ^ e, e, ?_⟩
  intro N D k
  have hh := Nat.pow_le_pow_left (show N + (D + D) + k + 2 ≤ 2 * (N + D + k + 2) by omega) e
  have hm := Nat.mul_le_mul_left C hh
  rw [mul_pow, ← mul_assoc] at hm
  exact (hf N (D + D) k).trans hm

theorem budget_polynomial (S : FaithfulMS.DirectSDP.PolynomialService) (W : RectangularDirectPrograms.Programs S) :
    NatPolynomialBound.Bounded (budget S W) := by
  have hmain := doubled_bounded (RectangularDirectPolynomialMajorant.budget_bounded S W)
  change NatPolynomialBound.Bounded (fun N D k =>
    RectangularDirectPolynomialRuntime.budget S W N (D + D) k + 1000 * (N + D + 1) ^ 3 + 5)
  apply NatPolynomialBound.add
  · apply NatPolynomialBound.add hmain
    apply NatPolynomialBound.mul (NatPolynomialBound.constant 1000)
    apply NatPolynomialBound.pow
    exact NatPolynomialBound.add (NatPolynomialBound.add NatPolynomialBound.first
      NatPolynomialBound.second) (NatPolynomialBound.constant 1)
  · exact NatPolynomialBound.constant 5

theorem exists_uniform_budget (S : FaithfulMS.DirectSDP.PolynomialService) (W : RectangularDirectPrograms.Programs S) :
    ∃ C e : ℕ, 0 < C ∧ ∀ N D k : ℕ,
      budget S W N D k ≤ C * (N + D + k + 2) ^ e ∧
      RectangularDirectPolynomialRuntime.randomDraws N (D + D) k ≤ C * (N + D + k + 2) ^ e := by
  obtain ⟨C, e, hh⟩ := NatPolynomialBound.add (budget_polynomial S W)
    (doubled_bounded RectangularDirectPolynomialMajorant.randomDraws_bounded)
  refine ⟨C + 1, e, by omega, ?_⟩
  intro N D k
  have hp := hh N D k
  dsimp only at hp
  have hm := Nat.mul_le_mul_right ((N + D + k + 2) ^ e) (show C ≤ C + 1 by omega)
  constructor <;> omega


end MatrixSpencer.RectangularDirectBudget
