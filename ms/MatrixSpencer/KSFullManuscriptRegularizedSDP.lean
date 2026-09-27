import MatrixSpencer.KSFullManuscriptSDPIdentity
import MatrixSpencer.KSFullManuscriptRegularizationBias

/-!
# The actual regularized SDP optimum and its bias

Compactness is used only to prove that a maximum exists and to identify the
specified SDP optimum. It does not choose data in the numerical ellipsoid
routine. The source regularization and error are exactly those of (O8)-(O9).
-/

open Matrix
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section
namespace MatrixSpencer.KSFullManuscriptRegularizedSDP

open KSFullManuscriptSDPIdentity KSFullManuscriptRegularizationBias
variable {n ι : Type*} [Fintype n] [DecidableEq n] [Fintype ι]

 theorem continuousOn_objective (H : Matrix n n ℂ) (B : ι → Matrix n n ℂ) (θ : ℝ)
    {lam : ℝ} (hlam : 0 ≤ lam) :
    ContinuousOn (objective H (krausChannel B) θ lam) densitySet := by
  apply continuousOn_iff_continuous_restrict.mpr
  have hs : Continuous (fun S : (densitySet : Set (Matrix n n ℂ)) => (S : Matrix n n ℂ)) :=
    continuous_subtype_val
  have hsource := ((continuous_krausChannel B).comp hs).add
    (continuous_const : Continuous (fun _ : (densitySet : Set (Matrix n n ℂ)) => lam • (1 : Matrix n n ℂ)))
  have hf := continuous_fidelity_of_psd hs hsource (fun S => S.property.1)
    (fun S => (krausChannel_posSemidef B S.property.1).add (Matrix.PosSemidef.one.smul hlam))
  have hroot := continuous_matrix_sqrt_of_psd hs (fun S => S.property.1)
  exact ((continuous_realTrace.comp (continuous_const.mul hs)).add
    (continuous_const.mul hf)).add (continuous_const.mul (continuous_realTrace.comp hroot))

def potential (H : Matrix n n ℂ) (B : ι → Matrix n n ℂ) (θ lam : ℝ) : ℝ :=
  sSup (objective H (krausChannel B) θ lam '' densitySet)

theorem exists_maximizer [Nonempty n] (H : Matrix n n ℂ) (B : ι → Matrix n n ℂ) (θ : ℝ)
    {lam : ℝ} (hlam : 0 ≤ lam) :
    ∃ S ∈ densitySet, ∀ T ∈ densitySet,
      objective H (krausChannel B) θ lam T ≤ objective H (krausChannel B) θ lam S :=
  isCompact_densitySet.exists_isMaxOn densitySet_nonempty (continuousOn_objective H B θ hlam)

theorem potential_eq_of_maximizer (H : Matrix n n ℂ) (B : ι → Matrix n n ℂ) (θ lam : ℝ)
    {S : Matrix n n ℂ} (hS : S ∈ densitySet)
    (hmax : ∀ T ∈ densitySet, objective H (krausChannel B) θ lam T ≤ objective H (krausChannel B) θ lam S) :
    potential H B θ lam = objective H (krausChannel B) θ lam S := by
  have hh : IsGreatest (objective H (krausChannel B) θ lam '' densitySet)
      (objective H (krausChannel B) θ lam S) :=
    ⟨⟨S, hS, rfl⟩, fun y ⟨T, hT, hy⟩ => hy ▸ hmax T hT⟩
  exact hh.csSup_eq

theorem regularized_SDP_exact [Nonempty n] (H : Matrix n n ℂ) (B : ι → Matrix n n ℂ)
    {θ lam : ℝ} (hθ : 0 ≤ θ) (hlam : 0 < lam) :
    ∃ S Y Z : Matrix n n ℂ, Feasible (krausChannel B) lam S Y Z ∧
      value H θ S Y Z = potential H B θ lam ∧
      ∀ S' Y' Z', Feasible (krausChannel B) lam S' Y' Z' →
        value H θ S' Y' Z' ≤ value H θ S Y Z := by
  obtain ⟨S, hS, hmax⟩ := exists_maximizer H B θ hlam.le
  have hsource : (krausChannel B S + lam • 1).PosDef :=
    regularize_posDef (krausChannel_posSemidef B hS.1) hlam
  obtain ⟨Y,Z,hF,hval⟩ := fixed_density_attainment (H := H) (θ := θ) hS hsource
  refine ⟨S,Y,Z,hF,hval.trans (potential_eq_of_maximizer H B θ lam hS hmax).symm, ?_⟩
  intro S' Y' Z' hF'
  rw [hval]
  exact (feasible_value_le hθ hF').trans (hmax S' (feasible_density hF'))

theorem objective_bias (H : Matrix n n ℂ) (B : ι → Matrix n n ℂ) (θ : ℝ)
    {lam : ℝ} (hlam : 0 ≤ lam) {S : Matrix n n ℂ} (hS : S ∈ densitySet) :
    0 ≤ objective H (krausChannel B) θ lam S - densityObjective H B θ S ∧
      objective H (krausChannel B) θ lam S - densityObjective H B θ S ≤
        2 * Real.sqrt (lam * Fintype.card n) := by
  have hh := source_regularization_error hS.1 hS.2 (krausChannel_posSemidef B hS.1) hlam
  simpa only [objective, densityObjective, add_sub_add_right_eq_sub, add_sub_add_left_eq_sub] using hh

theorem potential_bias [Nonempty n] (H : Matrix n n ℂ) (B : ι → Matrix n n ℂ) (θ : ℝ)
    {lam : ℝ} (hlam : 0 ≤ lam) :
    0 ≤ potential H B θ lam - densityPotential H B θ ∧
      potential H B θ lam - densityPotential H B θ ≤ 2 * Real.sqrt (lam * Fintype.card n) := by
  obtain ⟨S, hS, hmaxS⟩ := exists_densityOptimizer H B θ
  obtain ⟨T, hT, hmaxT⟩ := exists_maximizer H B θ hlam
  rw [densityPotential_eq_of_maximizer H B θ hS hmaxS,
    potential_eq_of_maximizer H B θ lam hT hmaxT]
  have hs := objective_bias H B θ hlam hS
  have ht := objective_bias H B θ hlam hT
  have hmS := hmaxS T hT
  have hmT := hmaxT S hS
  constructor <;> linarith


theorem potential_precision [Nonempty n] (H : Matrix n n ℂ) (B : ι → Matrix n n ℂ) (θ : ℝ)
    {ν : ℝ} (hν : 0 < ν) :
    |potential H B θ (regularization (Fintype.card n) ν) - densityPotential H B θ| ≤ ν / 2 := by
  have hn := Fintype.card_pos (α := n)
  have hb := potential_bias H B θ (regularization_pos hn hν).le
  rw [abs_of_nonneg hb.1]
  simpa only [regularization_budget hn hν.le] using hb.2

end MatrixSpencer.KSFullManuscriptRegularizedSDP
