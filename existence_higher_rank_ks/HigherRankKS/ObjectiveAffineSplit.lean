import HigherRankKS.ObjectiveResponseDefinitions

/-! Affine objective splitting via the explicit quadratic center polynomial. -/
open Matrix MatrixSpencer Filter Set
open scoped Topology BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator ContDiff
noncomputable section
namespace HigherRankKS.ObjectiveResponse

section Bilinear
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Along two affine lines, a real bilinear form is a quadratic polynomial. -/
theorem bilinear_affine_eq (B : E →L[ℝ] F →L[ℝ] ℝ) (a b : E) (c d : F) :
    (fun t : ℝ => B (a + t • b) (c + t • d)) =
      (fun t => B a c + t * (B a d + B b c) + t ^ 2 * B b d) := by
  funext t
  simp only [map_add, map_smul, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smul_apply, smul_eq_mul]
  ring

/-- Polynomial smoothness avoids expanding the operator-valued bilinear map. -/
theorem contDiff_bilinear_affine (B : E →L[ℝ] F →L[ℝ] ℝ) (a b : E) (c d : F) :
    ContDiff ℝ ∞ (fun t : ℝ => B (a + t • b) (c + t • d)) := by
  rw [bilinear_affine_eq]
  fun_prop

end Bilinear

variable {ι n : Type*} [Fintype ι] [Fintype n] [DecidableEq n]
local instance objectiveAffineSplitCStar {j : Type*} [Fintype j] [DecidableEq j] :
    CStarAlgebra (Matrix j j ℂ) := {}
local instance objectiveAffineSplitSpace :
    NormedSpace ℝ (selfAdjoint (Matrix (n ⊕ n) (n ⊕ n) ℂ)) := inferInstance

/-- Splitting the actual affine objective into its center, fidelity, and root derivatives. -/
theorem objective_second_split (A : ι → Matrix n n ℂ)
    (hA : ∀ i, (A i).PosSemidef) (k : ℕ) (hk : 1 ≤ k)
    (c : ℝ → ι → ℝ) (hcs : ContDiffAt ℝ 2 c 0) (hc : ∀ i, 0 < c 0 i)
    (H K : Matrix (n ⊕ n) (n ⊕ n) ℂ) (θ : ℝ)
    (S X : selfAdjoint (Matrix (n ⊕ n) (n ⊕ n) ℂ))
    (hS : (S : Matrix (n ⊕ n) (n ⊕ n) ℂ).PosDef) :
    iteratedDeriv 2 (fun t : ℝ => hermitianObjective (H + t • K) A ((1 : ℝ) / 2 ^ k)
      (c t) θ (S + t • X)) 0 =
      2 * tracePairing K X +
      iteratedDeriv 2 (fun t : ℝ => jointSourceFidelity A ((1 : ℝ) / 2 ^ k) (c t, S + t • X)) 0 +
      fderiv ℝ (fderiv ℝ (tsallisPotential θ)) S X X := by
  let P := fun t : ℝ => (c t, S + t • X)
  have hP : ContDiffAt ℝ 2 P 0 := hcs.prodMk (by fun_prop)
  have hP0 : P 0 = (c 0, S) := by simp [P]
  have hsmooth : ContDiffAt ℝ 2
      (fun t : ℝ => jointSourceFidelity A ((1 : ℝ) / 2 ^ k) (c t, S + t • X)) 0 := by
    have hb : ContDiffAt ℝ 2 (jointSourceFidelity A ((1 : ℝ) / 2 ^ k)) (P 0) := by
      rw [hP0]
      exact (contDiffAt_jointSourceFidelity A hA k hk (c 0) hc S hS).of_le
        (WithTop.coe_le_coe.mpr (show (2 : ℕ∞) ≤ ⊤ from le_top))
    exact hb.comp 0 hP
  have hroot : ContDiffAt ℝ 2 (tsallisPotential θ) S :=
    (contDiffAt_tsallisPotential θ S hS).of_le
      (WithTop.coe_le_coe.mpr (show (2 : ℕ∞) ≤ ⊤ from le_top))
  have hrootsmooth : ContDiffAt ℝ 2 (fun t : ℝ => tsallisPotential θ (S + t • X)) 0 := by
    have hb : ContDiffAt ℝ 2 (tsallisPotential θ) (S + (0 : ℝ) • X) := by simpa using hroot
    exact hb.comp 0 (f := fun t : ℝ => S + t • X) (by fun_prop)
  have hcenter : ContDiffAt ℝ 2 (fun t : ℝ => tracePairing (H + t • K) (S + t • X)) 0 :=
    (contDiff_bilinear_affine (tracePairing (n := n ⊕ n)) H K S X).contDiffAt.of_le
      (WithTop.coe_le_coe.mpr (show (2 : ℕ∞) ≤ ⊤ from le_top))
  have heq : (fun t : ℝ => hermitianObjective (H + t • K) A ((1 : ℝ) / 2 ^ k)
      (c t) θ (S + t • X)) =
      (fun t : ℝ => tracePairing (H + t • K) (S + t • X)) +
      (fun t : ℝ => jointSourceFidelity A ((1 : ℝ) / 2 ^ k) (c t, S + t • X)) +
      (fun t : ℝ => tsallisPotential θ (S + t • X)) := by
    funext t
    simp only [Pi.add_apply, hermitianObjective_eq, nonlinearSourceFidelity, jointSourceFidelity]
  rw [heq]
  rw [iteratedDeriv_add
      (f := (fun t : ℝ => tracePairing (H + t • K) (S + t • X)) +
        (fun t : ℝ => jointSourceFidelity A ((1 : ℝ) / 2 ^ k) (c t, S + t • X)))
      (hcenter.add hsmooth) hrootsmooth,
    iteratedDeriv_add hcenter hsmooth, center_second_affine,
    SourceScalarMetric.iteratedDeriv_two_line _ S X hroot]

end HigherRankKS.ObjectiveResponse
