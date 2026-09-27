import MatrixSpencer.MSManuscriptNumericalEpochSuccess
import MatrixSpencer.MSConvexNumericalEpochMoments

/-! The original square walk with convex owner-value queries substituted.
The state, invariants, tuning constants and non-query primitives remain original. -/
open Matrix Set
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section
namespace MatrixSpencer.MSConvexNumericalEpochSuccess
open MSManuscriptNumericalEpochSuccess MSManuscriptAdaptive MSManuscriptNumericalEpochLedger MSConvexNumericalEpochRun MSConvexNumericalEpochMoments MSManuscriptNumericalConfig
attribute [local instance] Classical.propDecidable
variable [MSConvexOwnerValue.Oracle]
variable {N d : ℕ} [Nonempty (Fin d)]
local instance : CStarAlgebra (Matrix (Fin d) (Fin d) ℂ) := {}
set_option maxHeartbeats 1800000
set_option maxRecDepth 4000
attribute [local irreducible] ownerPotential ownerCertificate

private theorem price_eq (cfg : EpochConfig (Fin N) (Fin d)) (hd : 0<d) :
    (ofEpochConfig cfg hd).threshold/2=2048/Real.sqrt (N:ℝ) := by
  change ((4096:ℝ)/Real.sqrt (N:ℝ))/2=_
  ring

theorem joint_moment (cfg : EpochConfig (Fin N) (Fin d)) (hd : 0<d) :
    let c:=ofEpochConfig cfg hd
    (output c).expectation (fun s=>energy c s.val+2048/Real.sqrt (N:ℝ)*s.val.paid)≤
      (151/50:ℝ)*Real.sqrt (N:ℝ) := by
  dsimp only
  have h := output_joint_moment (ofEpochConfig cfg hd)
  rw [price_eq cfg hd] at h
  exact h.trans (joint_budget cfg hd (MSManuscriptNumericalEpochLedger.initial cfg.start))

theorem dust_le (cfg : EpochConfig (Fin N) (Fin d)) (hd : 0<d) (s : Certified (ofEpochConfig cfg hd)) :
    s.val.dust≤(N:ℝ)/1024 := by
  have hdim : ((N-s.val.owner.dim:ℕ):ℝ)≤N := by exact_mod_cast Nat.sub_le N s.val.owner.dim
  have hdust := s.property.1.dust_le
  exact hdust.trans ((mul_le_mul_of_nonneg_left hdim (mul_nonneg (by norm_num) (ofEpochConfig cfg hd).floor_pos.le)).trans (dust_budget cfg hd))

theorem energy_moment (cfg : EpochConfig (Fin N) (Fin d)) (hd : 0<d) :
    let c:=ofEpochConfig cfg hd
    (output c).expectation (fun s=>energy c s.val)≤(151/50:ℝ)*Real.sqrt (N:ℝ) := by
  dsimp only
  exact MSManuscriptEpochProbability.energy_moment_le_of_joint _ _ _
    (Nat.cast_pos.mpr (count_pos cfg)) (fun s=>s.property.1.paid_nonneg) (joint_moment cfg hd)

theorem cleaning_moment (cfg : EpochConfig (Fin N) (Fin d)) (hd : 0<d) :
    let c:=ofEpochConfig cfg hd
    (output c).expectation (fun s=>if (N:ℝ)/64<s.val.paid+s.val.dust then 1 else 0)≤1/8 := by
  dsimp only
  exact MSManuscriptEpochProbability.cleaning_probability_le _ _ _ _
    (Nat.cast_pos.mpr (count_pos cfg)) (energy_nonneg _) (fun s=>s.property.1.paid_nonneg)
    (dust_le cfg hd) (joint_moment cfg hd)

theorem tangent_moment (cfg : EpochConfig (Fin N) (Fin d)) (hd : 0<d) :
    let c:=ofEpochConfig cfg hd
    (output c).expectation (fun s=>tangent c s.val^2)≤(Real.sqrt (N:ℝ))^2 := by
  dsimp only
  rw [Real.sq_sqrt (Nat.cast_nonneg N)]
  exact (output_tangent_moment (ofEpochConfig cfg hd)).trans tangent_budget

/-- All three actual numerical-acceptance moment obligations, with none
remaining as a premise. -/

theorem all_moments (cfg : EpochConfig (Fin N) (Fin d)) (hd : 0<d) :
    let c:=ofEpochConfig cfg hd
    (output c).expectation (fun s=>if (N:ℝ)/64<s.val.paid+s.val.dust then 1 else 0)≤1/8 ∧
    (output c).expectation (fun s=>energy c s.val)≤(151/50:ℝ)*Real.sqrt (N:ℝ) ∧
    (output c).expectation (fun s=>tangent c s.val^2)≤(Real.sqrt (N:ℝ))^2 :=
  ⟨cleaning_moment cfg hd,energy_moment cfg hd,tangent_moment cfg hd⟩

/-- Literal finite good-event mass of the implemented fixed-step numerical
epoch. It includes absence of excessive cleaning and both original tests. -/

theorem good_event_probability_ge (cfg : EpochConfig (Fin N) (Fin d)) (hd : 0<d) :
    let c:=ofEpochConfig cfg hd
    (31/50:ℝ)≤∑z:(output c).Draws,(output c).weight z*
      (if energy c ((output c).value z).val≤16*Real.sqrt (N:ℝ) ∧
        tangent c ((output c).value z).val≤4*Real.sqrt (N:ℝ) ∧
        ((output c).value z).val.paid+((output c).value z).val.dust≤(N:ℝ)/64 then 1 else 0) := by
  dsimp only
  have hh := MSManuscriptEpochProbability.good_probability_ge (output (ofEpochConfig cfg hd))
      (fun s=>energy (ofEpochConfig cfg hd) s.val) (fun s=>s.val.paid) (fun s=>s.val.dust)
      (fun s=>tangent (ofEpochConfig cfg hd) s.val)
      (Nat.cast_pos.mpr (count_pos cfg)) (energy_nonneg _) (fun s=>s.property.1.paid_nonneg)
      (dust_le cfg hd) (joint_moment cfg hd)
      ((output_tangent_moment (ofEpochConfig cfg hd)).trans tangent_budget)
  refine hh.trans_eq ?_
  apply Finset.sum_congr rfl
  intro z _
  congr 1
  unfold MSManuscriptEpochProbability.Good
  split_ifs <;> rfl

end MatrixSpencer.MSConvexNumericalEpochSuccess
