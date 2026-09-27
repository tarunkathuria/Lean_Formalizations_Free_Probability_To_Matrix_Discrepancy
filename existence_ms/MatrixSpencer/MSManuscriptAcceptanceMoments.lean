import MatrixSpencer.MSManuscriptNumericalAcceptance



open scoped BigOperators
noncomputable section
namespace MatrixSpencer.MSManuscriptAcceptanceMoments
open MSManuscriptAdaptive MSManuscriptNumericalAcceptance
attribute [local instance] Classical.propDecidable

/-- Pointwise domination of the failed-good-event indicator. -/
theorem bad_indicator_le {s psi tangent : ℝ} (hs : 0 < s) (hp : 0 ≤ psi)
    (failed : Bool) :
    1-(if failed = false ∧ psi ≤ 16*s ∧ tangent ≤ 4*s then (1:ℝ) else 0) ≤
      (if failed then (1:ℝ) else 0) + psi/(16*s) + tangent^2/(16*s^2) := by
  have hpd : 0 ≤ psi/(16*s) := div_nonneg hp (by positivity)
  have htd : 0 ≤ tangent^2/(16*s^2) := by positivity
  cases failed with
  | true => simp; linarith
  | false =>
    simp only [Bool.false_eq_true, true_and, ↓reduceIte]
    by_cases hg : psi ≤ 16*s ∧ tangent ≤ 4*s
    · simp only [if_pos hg]; linarith
    · simp only [if_neg hg]
      by_cases hpbig : psi ≤ 16*s
      · have htbig : 4*s < tangent := lt_of_not_ge (fun ht => hg ⟨hpbig,ht⟩)
        have hsq : 16*s^2 ≤ tangent^2 := by nlinarith
        have hd : 1 ≤ tangent^2/(16*s^2) := (le_div_iff₀ (by positivity)).mpr (by simpa using hsq)
        linarith
      · have hd : 1 ≤ psi/(16*s) := (le_div_iff₀ (by positivity)).mpr (by linarith)
        linarith

/-- Exact conservative calculation: failure mass is at most `301/800`,
so the true-good event has probability at least `499/800 > 0.62`. -/
theorem good_probability_ge {α : Type*} (P : Sampler α) (failed : α → Bool)
    (psi tangent : α → ℝ) {s : ℝ} (hs : 0 < s)
    (hpsi_nonneg : ∀ z : P.Draws, 0 ≤ psi (P.value z))
    (hclean : P.expectation (fun a => if failed a then 1 else 0) ≤ 1/8)
    (hpsi : P.expectation psi ≤ (151/50:ℝ)*s)
    (htangent : P.expectation (fun a => tangent a^2) ≤ s^2) :
    (499/800:ℝ) ≤ P.expectation (fun a =>
      if failed a = false ∧ psi a ≤ 16*s ∧ tangent a ≤ 4*s then 1 else 0) := by
  have hpoint : P.expectation (fun a => 1-(if failed a = false ∧ psi a ≤ 16*s ∧
      tangent a ≤ 4*s then (1:ℝ) else 0)) ≤
      P.expectation (fun a => (if failed a then (1:ℝ) else 0) +
        psi a/(16*s)+tangent a^2/(16*s^2)) := by
    apply Finset.sum_le_sum
    intro z _
    exact mul_le_mul_of_nonneg_left (bad_indicator_le hs (hpsi_nonneg z) (failed (P.value z)))
      (P.weight_nonneg z)
  rw [P.expectation_sub, P.expectation_const] at hpoint
  have he : P.expectation (fun a => (if failed a then (1:ℝ) else 0) +
      psi a/(16*s)+tangent a^2/(16*s^2)) =
      P.expectation (fun a => if failed a then 1 else 0) +
        P.expectation psi/(16*s)+P.expectation (fun a => tangent a^2)/(16*s^2) := by
    simp only [Sampler.expectation, mul_add, mul_div_assoc, Finset.sum_add_distrib,
      Finset.sum_div]
  rw [he] at hpoint
  have hp : P.expectation psi/(16*s) ≤ (151/800:ℝ) := by
    apply (div_le_iff₀ (by positivity)).mpr
    nlinarith
  have ht : P.expectation (fun a => tangent a^2)/(16*s^2) ≤ (1/16:ℝ) := by
    apply (div_le_iff₀ (by positivity)).mpr
    nlinarith
  linarith


theorem numerical_output_event_probability_ge {N d : ℕ} (cfg : Config N d)
    (P : Sampler (Endpoint N d)) (hvalid : ∀ z : P.Draws, (P.value z).Valid cfg)
    (hclean : P.expectation (fun e => if e.cleaningFailed then 1 else 0) ≤ 1/8)
    (hpsi : P.expectation (psi cfg) ≤ (151/50:ℝ)*scale cfg)
    (htangent : P.expectation (fun e => (tangent cfg e)^2) ≤ (scale cfg)^2) (r : ℕ) :
    1-(301/800:ℝ)^r ≤ ∑ z : (output cfg P r).Draws, (output cfg P r).weight z *
      (if ((output cfg P r).value z).isSome then 1 else 0) := by
  have hnon : ∀ z : P.Draws, 0 ≤ psi cfg (P.value z) := by
    intro z
    letI : Nonempty (Fin d) := ⟨⟨0,cfg.dimension_pos⟩⟩
    exact ownerCertificate_nonneg cfg.savedCenter (P.value z).center cfg.family
      cfg.family_hermitian (hvalid z).2.1 cfg.theta
  have hp0 := good_probability_ge P Endpoint.cleaningFailed (psi cfg) (tangent cfg)
    (scale_pos cfg) hnon hclean hpsi htangent
  have hp : (499/800:ℝ) ≤ P.expectation (fun e => if Good cfg e then 1 else 0) := by
    convert hp0 using 1
    congr 1
    funext e
    simp only [Good]
    split_ifs <;> rfl
  convert MSManuscriptNumericalAcceptance.output_event_probability_ge cfg P hvalid hp r using 1 <;> norm_num

end MatrixSpencer.MSManuscriptAcceptanceMoments
