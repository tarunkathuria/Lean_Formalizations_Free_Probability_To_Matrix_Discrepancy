import HigherRankKSRuntime.ActiveChart
import HigherRankKSRuntime.RuntimeCurvature
import HigherRankKSRuntime.NextEvent

/-! Identities between the controller's concrete original-owner updates and
the coefficient charts used by the derivative and response theorems. -/
noncomputable section
open Matrix MatrixSpencer
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator
namespace HigherRankKSRuntime.ActiveEnumeration
open AugmentedHigherRankKS
variable {N : ℕ} {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]

def center (A : Fin N → Matrix n n ℂ) (x₀ : Fin N → ℝ)
    (z : EpochState (Fin N)) := augmentedCenter (discrepancy A x₀ z) (budgetCenter A x₀ z)

theorem prepareOwner_eq_prepareOne (a : ℝ) (z : EpochState (Fin N)) (i : Fin N) (t : ℝ) :
    prepareOwner a z i t = prepareOne a z i t := by
  unfold prepareOwner prepareOne
  congr 1
  ext j
  simp only [Pi.single_apply]

theorem preparation_chart_eq (A : Fin N → Matrix n n ℂ) (β θ : ℝ)
    (x₀ : Fin N → ℝ) {a R : ℝ} {z : EpochState (Fin N)} (hz : z ∈ epochDomain a R)
    (i : Fin (count z)) (t : ℝ) :
    epochPotential A β θ x₀ (prepareOwner a z (activeEquiv z i) t) =
      RuntimeCurvature.prepCurve (center A x₀ z) (restrictedAtoms A z) β θ a
        (restrictedReserve z) i t := by
  rw [prepareOwner_eq_prepareOne, epochPotential_prepareOne_eq A β θ x₀ hz
    (activeEquiv z i) t, potential_reindex (activeEquiv z)]
  unfold RuntimeCurvature.prepCurve
  congr 1
  funext j
  change reserve z (activeEquiv z j) - (if activeEquiv z j = activeEquiv z i then t else 0) =
    reserve z (activeEquiv z j) - (if j = i then t else 0)
  simp only [Equiv.apply_eq_iff_eq]

theorem movement_runtime_chart_eq (A : Fin N → Matrix n n ℂ) (β θ : ℝ)
    (x₀ : Fin N → ℝ) {a R : ℝ} {z : EpochState (Fin N)} (hz : z ∈ epochDomain a R)
    (u : EuclideanSpace ℝ (Fin (count z))) :
    epochPotential A β θ x₀ (movement a z (extend z u) 1) =
      RuntimeCurvature.chart (center A x₀ z) (restrictedAtoms A z) β θ a
        (restrictedPosition z) (restrictedReserve z) u := by
  rw [movement_chart_eq A β θ x₀ hz u 1]
  simp only [one_smul, one_pow, mul_one]
  rfl

theorem movement_scale_eq (a : ℝ) (z : EpochState (Fin N))
    (v : EuclideanSpace ℝ (Fin (count z))) (t : ℝ) :
    movement a z (extend z (t • v)) 1 = movement a z (extend z v) t := by
  have he : extend z (t • v) = t • extend z v := by
    ext i
    by_cases hi : 0 < reserve z i
    · let j : ActiveOwners z := ⟨i,(mem_positiveReserves z i).mpr hi⟩
      simp only [PiLp.smul_apply,smul_eq_mul]
      rw [show extend z (t • v) i = (t • v) ((activeEquiv z).symm j) from extend_active z _ j,
        show extend z v i = v ((activeEquiv z).symm j) from extend_active z _ j]
      rfl
    · simp only [extend_inactive z _ i hi,PiLp.smul_apply,smul_zero]
  rw [he]
  apply Prod.ext
  · funext i
    simp only [movement,position,PiLp.smul_apply,smul_eq_mul,one_mul]
  · apply Prod.ext <;> funext i <;>
      simp only [movement,spent,reserve,PiLp.smul_apply,smul_eq_mul,one_pow,one_mul,mul_pow] <;>
      ring

end HigherRankKSRuntime.ActiveEnumeration
