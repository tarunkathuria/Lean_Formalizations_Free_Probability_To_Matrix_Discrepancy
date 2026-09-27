import AugmentedHigherRankKS.CompactExistence
import AugmentedHigherRankKS.FaceAssembly

/-! Finite composition of the proved reserve epochs. No solver, curvature,
termination, or epoch-success certificate is an assumption. -/
open Matrix MatrixSpencer Set
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section
namespace AugmentedHigherRankKS
variable {ι n : Type*} [Fintype ι] [DecidableEq ι] [Fintype n] [DecidableEq n] [Nonempty n]
local instance dyadicCStar : CStarAlgebra (Matrix n n ℂ) := {}

theorem exists_dyadic_signing
    (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).PosSemidef)
    {ε : ℝ} (hε : 0 ≤ ε) (hN : ∀ i, ‖A i‖ ≤ ε)
    {r : ℕ} (hr : ∀ i, (A i).rank ≤ r)
    (k : ℕ) (hk : 1 ≤ k) (hrr : (r : ℝ)^((1 : ℝ) / 2 ^ k) ≤ 2) :
    ∃ σ : ι → ℝ, (∀ i, σ i = 1 ∨ σ i = -1) ∧
      ‖∑ i, σ i • A i‖ ≤
        512 * Real.sqrt (ε / ((1 : ℝ) / 2 ^ k)) * Real.sqrt ‖∑ i, A i‖ := by
  let β : ℝ := 1 / 2 ^ k
  have hβ : 0 < β := by dsimp [β]; positivity
  have hfinish := signing_of_exhausted_epochs A hA (reserveScale_pos hβ).ne'
    (epochScale_nonneg β ε)
  have hepoch : ∀ x : CubePoint ι, (epochScale β ε)^2 < ‖cubeMass A x‖ →
      ∃ z : EpochState (LiveOwners x), z ∈ epochDomain (reserveScale β) 4 ∧
        (∀ i, reserve z i = 0) ∧
        epochCenterSize (fun i : LiveOwners x => A i) (fun i => x.val i) z ≤
          epochScale β ε * Real.sqrt ‖cubeMass A x‖ := by
    intro x hx
    let B : LiveOwners x → Matrix n n ℂ := fun i => A i
    have hB : ∀ i, (B i).PosSemidef := fun i => hA i
    have hsumpos : (0 : Matrix n n ℂ) ≤ ∑ i, B i :=
      Finset.sum_nonneg (fun i _ => (hB i).nonneg)
    have hsum : ∑ i, B i ≤ ‖cubeMass A x‖ • (1 : Matrix n n ℂ) := by
      have hh := IsSelfAdjoint.le_algebraMap_norm_self hsumpos.posSemidef.isHermitian
      rw [Algebra.algebraMap_eq_smul_one] at hh
      simpa only [cubeMass_eq_live_sum, B] using hh
    obtain ⟨z, hz, hc, hbound⟩ := exists_exhausted_epoch B hB hsum hε
      (fun i => hN i) (fun i => hr i) k hk (fun i => x.val i)
      (fun i => abs_le.mp (x.property i))
    refine ⟨z, hz, hc, hbound.trans ?_⟩
    exact initial_epoch_budget_le hβ hε (norm_nonneg _) hrr
  obtain ⟨σ, hσ, hn⟩ := hfinish hepoch
  refine ⟨σ, hσ, ?_⟩
  simpa only [epochScale, show (4 : ℝ) * (128 * Real.sqrt (ε / β)) =
    512 * Real.sqrt (ε / β) by ring] using hn

end AugmentedHigherRankKS
