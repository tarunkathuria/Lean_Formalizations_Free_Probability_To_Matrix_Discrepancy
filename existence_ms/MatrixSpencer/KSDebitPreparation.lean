import MatrixSpencer.KSDebitPotential
import MatrixSpencer.KSEighthPreparedState



open Matrix Set
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section
namespace MatrixSpencer.KSDebitPreparation

open KSPotentialModels KSDebitPotential
namespace Retirement
export KSEighthRetirementLoop (Candidate endpoint update accepted select)
end Retirement

variable {N : ℕ} {n : Type*} [Fintype n] [DecidableEq n]

def statePotential (v : Fin N → n → ℂ) (δ η θ : ℝ) (x : Fin N → ℝ) : ℝ :=
  potential (KSPotentialModels.center (fun i => KSRankOne.atom (v i)) x)
    (KSDebitBudget.debit (fun i => KSRankOne.atom (v i)) δ η x)
    v (naturalOwners 64 x) θ

def queryPotential (v : Fin N → n → ℂ) (δ η θ : ℝ) (x : Fin N → ℝ)
    (c : KSEighthRetirementLoop.Candidate N) : ℝ :=
  potential (KSPotentialModels.center (fun i => KSRankOne.atom (v i))
      (Retirement.update 1 x c))
    (KSDebitBudget.debit (fun i => KSRankOne.atom (v i)) δ η x + δ • KSRankOne.atom (v c.1))
    v (naturalOwners 64 (Retirement.update 1 x c)) θ

/-- The accumulator formed from the actual retired labels pays at most `2δ`
in the final discrepancy estimate, at every cube state. -/
theorem norm_le_statePotential_add [Nonempty n] (v : Fin N → n → ℂ)
    (hparseval : (∑ i, KSRankOne.atom (v i)) = 1)
    {δ η θ : ℝ} (hδ : 0 ≤ δ) (hη : 0 ≤ η) (hηbudget : (N : ℝ) * η ≤ δ)
    (hθ : 0 < θ) {x : Fin N → ℝ} (hx : x ∈ ksCube 1) :
    ‖KSPotentialModels.center (fun i => KSRankOne.atom (v i)) x‖ ≤
      statePotential v δ η θ x + 2 * δ := by
  exact norm_le_potential_add
    (KSPotentialModels.center_isHermitian _ (fun i => KSRankOne.atom_isHermitian (v i)) x)
    (KSDebitBudget.debit_le_two_delta _ (fun i => KSRankOne.atom_posSemidef (v i))
      hparseval hδ hη hηbudget x)
    v (naturalOwners_nonneg (by norm_num) le_rfl hx) hθ

theorem endpoint_isSign (b : Bool) : IsSign (Retirement.endpoint 1 b) := by
  cases b <;> simp [Retirement.endpoint, IsSign]

/-- This identifies the actual queried optimized potential, including owner
deletion and the new matrix debit, with the determined state potential. -/
theorem queryPotential_eq_state_add [Nonempty n] (v : Fin N → n → ℂ)
    (δ η : ℝ) {θ : ℝ} (hθ : 0 < θ) {x : Fin N → ℝ} (hx : x ∈ ksCube 1)
    (c : Retirement.Candidate N) (hc : |x c.1| < 1) :
    queryPotential v δ η θ x c = statePotential v δ η θ (Retirement.update 1 x c) + η := by
  have hy := KSEighthRetirementLoop.update_mem_cube (by norm_num : (0 : ℝ) ≤ 1) hx c
  have howners : ∀ i, 0 ≤ naturalOwners 64 (Retirement.update 1 x c) i :=
    naturalOwners_nonneg (by norm_num) le_rfl hy
  have hdebit := KSDebitBudget.debit_update_endpoint
    (fun i => KSRankOne.atom (v i)) δ η c.1 hc (endpoint_isSign c.2)
  change KSDebitBudget.debit _ δ η (Retirement.update 1 x c) = _ at hdebit
  unfold statePotential
  rw [hdebit, potential_add_scalar_debit _ _ v howners hθ η]
  change queryPotential v δ η θ x c = queryPotential v δ η θ x c - η + η
  ring


theorem query_report_accuracy [Nonempty n] (v : Fin N → n → ℂ)
    (δ η : ℝ) {θ : ℝ} (hθ : 0 < θ) (report : (Fin N → ℝ) → ℝ)
    {x : Fin N → ℝ} (hx : x ∈ ksCube 1) (c : Retirement.Candidate N)
    (hc : |x c.1| < 1)
    (hreport : |report (Retirement.update 1 x c) -
      statePotential v δ η θ (Retirement.update 1 x c)| ≤ η / 8) :
    |(report (Retirement.update 1 x c) + η) - queryPotential v δ η θ x c| ≤ η / 8 := by
  rw [queryPotential_eq_state_add v δ η hθ hx c hc, add_sub_add_right_eq_sub]
  exact hreport

theorem test_equivalence (η : ℝ) (report : (Fin N → ℝ) → ℝ)
    (x : Fin N → ℝ) (c : Retirement.Candidate N) :
    Retirement.accepted 1 (-η) report x c ↔
      |x c.1| < 1 ∧ (report (Retirement.update 1 x c) + η) - report x ≤ η / 2 := by
  unfold Retirement.accepted
  constructor <;> rintro ⟨hl, hv⟩ <;> exact ⟨hl, by linarith⟩

def prepare (η : ℝ) (report : (Fin N → ℝ) → ℝ) (x : Fin N → ℝ) : Fin N → ℝ :=
  KSEighthRetirementLoop.prepare 1 (-η) report N x

theorem prepare_mem_cube (η : ℝ) (report : (Fin N → ℝ) → ℝ)
    {x : Fin N → ℝ} (hx : x ∈ ksCube 1) : prepare η report x ∈ ksCube 1 :=
  KSEighthRetirementLoop.prepare_mem_cube (by norm_num) report N hx

theorem prepare_preserves_frozen (η : ℝ) (report : (Fin N → ℝ) → ℝ)
    (x : Fin N → ℝ) (i : Fin N) (hi : |x i| = 1) : prepare η report x i = x i :=
  KSEighthRetirementLoop.prepare_preserves_frozen report N x i hi

theorem prepare_energy_progress (η : ℝ) (report : (Fin N → ℝ) → ℝ)
    {x : Fin N → ℝ} (hx : x ∈ ksCube 1) :
    KSCubePreparation.energy x ≤ KSCubePreparation.energy (prepare η report x) :=
  KSEighthRetirementLoop.prepare_energy_progress (by norm_num) report N hx

theorem prepare_exhausts_tests (η : ℝ) (report : (Fin N → ℝ) → ℝ) (x : Fin N → ℝ) :
    Retirement.select 1 (-η) report (prepare η report x) = none :=
  KSEighthRetirementLoop.prepare_exhausts_tests (by norm_num) report x

theorem accepted_state_decreases {η : ℝ} {report F : (Fin N → ℝ) → ℝ}
    {x : Fin N → ℝ} {c : Retirement.Candidate N}
    (hc : Retirement.accepted 1 (-η) report x c)
    (hold : |report x - F x| ≤ η / 8)
    (hnew : |report (Retirement.update 1 x c) - F (Retirement.update 1 x c)| ≤ η / 8) :
    F (Retirement.update 1 x c) ≤ F x - η / 4 := by
  rcases abs_le.mp hold with ⟨hol, hou⟩
  rcases abs_le.mp hnew with ⟨hnl, hnu⟩
  have ht := hc.2
  linarith

theorem prepare_nonincreasing {η : ℝ} (hη : 0 ≤ η)
    (report F : (Fin N → ℝ) → ℝ)
    (haccuracy : ∀ x ∈ ksCube 1, |report x - F x| ≤ η / 8)
    {x : Fin N → ℝ} (hx : x ∈ ksCube 1) : F (prepare η report x) ≤ F x := by
  have hall (k : ℕ) {x : Fin N → ℝ} (hx : x ∈ ksCube 1) :
      F (KSEighthRetirementLoop.prepare 1 (-η) report k x) ≤ F x := by
    induction k generalizing x with
    | zero => exact le_rfl
    | succ k ih =>
      cases hs : Retirement.select 1 (-η) report x with
      | none => simp only [KSEighthRetirementLoop.prepare, hs, le_refl]
      | some c =>
        have hy := KSEighthRetirementLoop.update_mem_cube (by norm_num : (0 : ℝ) ≤ 1) hx c
        have hd := accepted_state_decreases (KSEighthRetirementLoop.select_some hs)
          (haccuracy x hx) (haccuracy _ hy)
        simp only [KSEighthRetirementLoop.prepare, hs]
        exact (ih hy).trans (by linarith)
  exact hall N hx

/-- Failed finite numerical preparation gives strict rejection by the actual
queried potential. No potential minimizer is assumed. -/
theorem query_rejected_after_prepare [Nonempty n] (v : Fin N → n → ℂ)
    (δ : ℝ) {η θ : ℝ} (hη : 0 ≤ η) (hθ : 0 < θ)
    (report : (Fin N → ℝ) → ℝ)
    (haccuracy : ∀ x ∈ ksCube 1, |report x - statePotential v δ η θ x| ≤ η / 8)
    {x : Fin N → ℝ} (hx : x ∈ ksCube 1) (c : Retirement.Candidate N)
    (hlive : |prepare η report x c.1| < 1) :
    statePotential v δ η θ (prepare η report x) <
      queryPotential v δ η θ (prepare η report x) c := by
  let y := prepare η report x
  have hy := prepare_mem_cube η report hx
  have hu := KSEighthRetirementLoop.update_mem_cube (by norm_num : (0 : ℝ) ≤ 1) hy c
  have hn := KSEighthRetirementLoop.select_none (prepare_exhausts_tests η report x) c
  have ht : -η / 2 < report (Retirement.update 1 y c) - report y := by
    apply lt_of_not_ge
    intro ht
    exact hn ⟨hlive, ht⟩
  rcases abs_le.mp (haccuracy y hy) with ⟨hol, hou⟩
  rcases abs_le.mp (haccuracy _ hu) with ⟨hnl, hnu⟩
  rw [queryPotential_eq_state_add v δ η hθ hy c hlive]
  change statePotential v δ η θ y < statePotential v δ η θ (Retirement.update 1 y c) + η
  linarith

end MatrixSpencer.KSDebitPreparation
