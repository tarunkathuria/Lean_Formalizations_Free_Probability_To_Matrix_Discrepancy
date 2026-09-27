import MatrixSpencer.KSEighthManuscriptParameters


open scoped BigOperators
noncomputable section
namespace MatrixSpencer.KSEighthManuscriptBudgets
open KSEighthManuscriptParameters
variable {N d : ℕ}

theorem rho_count (hN : 0 < N) (δ : ℝ) : rho N δ * N = δ/100 := by
  have hn : (N : ℝ) ≠ 0 := (Nat.cast_pos.mpr hN).ne'
  unfold rho
  field_simp

theorem kappa_count_square (hN : 0 < N) (δ : ℝ) : kappa N δ * (N : ℝ)^2 = δ/10000 := by
  have hn : (N : ℝ) ≠ 0 := (Nat.cast_pos.mpr hN).ne'
  unfold kappa
  field_simp

theorem movement_half_margin (v : Fin N → Fin d → ℂ) {δ θ : ℝ} (hN : 0 < N) :
    movementStep v δ θ * Real.sqrt (N : ℝ) ≤ rho N δ/2 := by
  have hs : 0 < Real.sqrt (N : ℝ) := Real.sqrt_pos.mpr (Nat.cast_pos.mpr hN)
  have hm : 2*movementStep v δ θ ≤ rho N δ/Real.sqrt (N : ℝ) := by
    unfold movementStep
    linarith [min_le_left (rho N δ/Real.sqrt (N : ℝ))
      (min (Real.sqrt (δ/(10000*fourthCap v θ*(N : ℝ)^3))) (1/100))]
  have hh := (le_div_iff₀ hs).mp hm
  linarith

theorem rho_le_hundredth (hN : 0 < N) {δ : ℝ} (hδ1 : δ ≤ 1) : rho N δ ≤ 1/100 := by
  have hn : (1 : ℝ) ≤ N := by exact_mod_cast hN
  unfold rho
  rw [div_le_iff₀ (by positivity : 0 < 100*(N:ℝ))]
  linarith

theorem movement_normalized_radius (v : Fin N → Fin d → ℂ) {δ θ : ℝ}
    (hN : 0 < N) (hδ1 : δ ≤ 1) :
    movementStep v δ θ * Real.sqrt (N : ℝ) ≤ 1/32 := by
  have hh := movement_half_margin (δ := δ) (θ := θ) v hN
  have hr := rho_le_hundredth hN hδ1
  linarith

theorem movement_remainder_budget (v : Fin N → Fin d → ℂ) {δ θ : ℝ}
    (hN : 0 < N) (hδ : 0 < δ) (hθ : 0 < θ) (hd : 0 < d) :
    fourthCap v θ * (N : ℝ)^3 * movementStep v δ θ ^ 2 ≤ δ/10000 := by
  have hp := movementStep_pos v hN hδ hθ hd
  have hM := fourthCap_pos v hθ hd
  have hn : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have hm : 2*movementStep v δ θ ≤ Real.sqrt (δ/(10000*fourthCap v θ*(N : ℝ)^3)) := by
    unfold movementStep
    have h := (min_le_right (rho N δ/Real.sqrt (N : ℝ))
      (min (Real.sqrt (δ/(10000*fourthCap v θ*(N : ℝ)^3))) (1/100))).trans
      (min_le_left _ _)
    linarith
  have hrad : 0 ≤ δ/(10000*fourthCap v θ*(N : ℝ)^3) := by positivity
  have hs := Real.sq_sqrt hrad
  have hh : movementStep v δ θ ^ 2 ≤ δ/(10000*fourthCap v θ*(N : ℝ)^3) := by
    nlinarith [Real.sqrt_nonneg (δ/(10000*fourthCap v θ*(N : ℝ)^3))]
  have he := (le_div_iff₀ (by positivity : 0<10000*fourthCap v θ*(N : ℝ)^3)).mp hh
  nlinarith

def cutoff (v : Fin N → Fin d → ℂ) (δ θ : ℝ) : ℕ :=
  ⌈100*(N : ℝ)/movementStep v δ θ ^ 2⌉₊

theorem cutoff_pos (v : Fin N → Fin d → ℂ) {δ θ : ℝ}
    (hN : 0 < N) (hδ : 0 < δ) (hθ : 0 < θ) (hd : 0 < d) : 0 < cutoff v δ θ := by
  have hs := movementStep_pos v hN hδ hθ hd
  unfold cutoff
  exact Nat.ceil_pos.mpr (by positivity)

theorem cutoff_lower (v : Fin N → Fin d → ℂ) {δ θ : ℝ}
    (hN : 0 < N) (hδ : 0 < δ) (hθ : 0 < θ) (hd : 0 < d) :
    100*(N : ℝ) ≤ movementStep v δ θ ^ 2 * (cutoff v δ θ : ℝ) := by
  have hs := movementStep_pos v hN hδ hθ hd
  have hc : 100*(N : ℝ)/movementStep v δ θ ^ 2 ≤ (cutoff v δ θ : ℝ) := Nat.le_ceil _
  have h := (div_le_iff₀ (sq_pos_of_pos hs)).mp hc
  simpa only [mul_comm] using h

/-- The remaining nonterminal mass at the actual chosen horizon is at most 1/100. -/
theorem cutoff_probability (v : Fin N → Fin d → ℂ) {δ θ : ℝ}
    (hN : 0 < N) (hδ : 0 < δ) (hθ : 0 < θ) (hd : 0 < d)
    (s : KSEighthManuscriptRun.State (controller v hN hδ hθ hd)) :
    KSEighthManuscriptRun.cutoffProbability (controller v hN hδ hθ hd) (cutoff v δ θ) s ≤ 1/100 := by
  have ht := cutoff_pos v hN hδ hθ hd
  have hh := cutoff_lower v hN hδ hθ hd
  have hs := movementStep_pos v hN hδ hθ hd
  have htr : (0 : ℝ) < cutoff v δ θ := Nat.cast_pos.mpr ht
  apply (KSEighthManuscriptRun.cutoffProbability_le _ _ ht s).trans
  change ((N : ℝ)/64)/(movementStep v δ θ ^ 2/2*(cutoff v δ θ : ℝ)) ≤ _
  rw [div_le_iff₀ (by positivity : 0 < movementStep v δ θ ^ 2/2*(cutoff v δ θ : ℝ))]
  nlinarith [Nat.cast_nonneg (α := ℝ) N]

end MatrixSpencer.KSEighthManuscriptBudgets
