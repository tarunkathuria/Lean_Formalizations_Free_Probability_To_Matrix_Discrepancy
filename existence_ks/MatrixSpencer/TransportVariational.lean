import MatrixSpencer.TraceGeometry

/-!
# The transport variational formula

The trace inequality is proved by completing a noncommutative square. Matrix
inverses are only canceled after positive definiteness supplies invertibility.
-/

open scoped BigOperators Matrix MatrixOrder ComplexOrder
open Matrix

noncomputable section

namespace MatrixSpencer

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The affine-in-the-inputs transport objective. -/
def transportCost (S M Z : Matrix n n ℂ) : ℝ :=
  realTrace (S * Z⁻¹) + realTrace (M * Z)

/-- Exact remainder identity; the inverse belongs to the positive comparison point `Z`. -/
theorem transportCost_remainder {S M T Z : Matrix n n ℂ}
    (hZ : Z.PosDef) (htransport : T * M * T = S) :
    transportCost S M Z - 2 * realTrace (M * T) =
      realTrace (M * ((Z - T) * Z⁻¹ * (Z - T))) := by
  letI : Invertible Z := hZ.isUnit.invertible
  have hexpand : (Z - T) * Z⁻¹ * (Z - T) = Z - T - T + T * Z⁻¹ * T := by
    calc
      _ = (Z * Z⁻¹) * Z - (T * Z⁻¹) * Z - (Z * Z⁻¹) * T + T * Z⁻¹ * T := by
        noncomm_ring
      _ = _ := by
        simp only [Matrix.mul_inv_of_invertible, Matrix.one_mul,
          Matrix.inv_mul_cancel_right_of_invertible]
  have hcycle : realTrace (M * (T * Z⁻¹ * T)) = realTrace (S * Z⁻¹) := by
    calc
      _ = realTrace ((T * M * T) * Z⁻¹) := by
        simpa only [Matrix.mul_assoc] using realTrace_mul_comm (M * T * Z⁻¹) T
      _ = _ := by rw [htransport]
  rw [hexpand]
  simp only [Matrix.mul_add, Matrix.mul_sub, realTrace_add, realTrace_sub]
  rw [hcycle]
  unfold transportCost
  ring

/-- Every positive comparison point has objective at least the transport value. -/
theorem transportCost_lower_bound {S M T Z : Matrix n n ℂ}
    (hM : M.PosSemidef) (hT : T.IsHermitian) (hZ : Z.PosDef)
    (htransport : T * M * T = S) :
    2 * realTrace (M * T) ≤ transportCost S M Z := by
  have hdiff := hZ.isHermitian.sub hT
  have hsq : ((Z - T) * Z⁻¹ * (Z - T)).PosSemidef := by
    simpa only [hdiff.eq] using hZ.inv.posSemidef.conjTranspose_mul_mul_same (Z - T)
  have h := realTrace_mul_nonneg hM hsq
  rw [← transportCost_remainder hZ htransport] at h
  linarith

/-- The transport point attains that lower bound. -/
theorem transportCost_at_transport {S M T : Matrix n n ℂ}
    (hT : T.PosDef) (htransport : T * M * T = S) :
    transportCost S M T = 2 * realTrace (M * T) := by
  have h := transportCost_remainder hT htransport
  simp only [sub_self, Matrix.zero_mul, Matrix.mul_zero, realTrace_zero] at h
  linarith

/-- A faithful transport solution is a genuine global minimizer over all positive matrices. -/
theorem transportCost_minimized {S M T : Matrix n n ℂ}
    (hM : M.PosSemidef) (hT : T.PosDef) (htransport : T * M * T = S) :
    ∀ Z : Matrix n n ℂ, Z.PosDef → transportCost S M T ≤ transportCost S M Z := by
  intro Z hZ
  rw [transportCost_at_transport hT htransport]
  exact transportCost_lower_bound hM hT.isHermitian hZ htransport

/-- The positive fidelity root. -/
def fidelityCore (S M : Matrix n n ℂ) : Matrix n n ℂ :=
  CFC.sqrt (CFC.sqrt S * M * CFC.sqrt S)

/-- Unnormalized matrix fidelity. -/
def fidelity (S M : Matrix n n ℂ) : ℝ := realTrace (fidelityCore S M)

/-- The actual transport matrix built from positive square roots. -/
def transportOptimizer (S M : Matrix n n ℂ) : Matrix n n ℂ :=
  CFC.sqrt S * (fidelityCore S M)⁻¹ * CFC.sqrt S

theorem fidelityCore_posDef {S M : Matrix n n ℂ} (hS : S.PosDef) (hM : M.PosDef) :
    (fidelityCore S M).PosDef := by
  have hi : Function.Injective (CFC.sqrt S).mulVec :=
    Matrix.mulVec_injective_iff_isUnit.mpr hS.posDef_sqrt.isUnit
  have h := hM.conjTranspose_mul_mul_same hi
  rw [hS.posDef_sqrt.isHermitian.eq] at h
  exact h.posDef_sqrt

theorem fidelityCore_mul_self {S M : Matrix n n ℂ} (hM : M.PosSemidef) :
    fidelityCore S M * fidelityCore S M = CFC.sqrt S * M * CFC.sqrt S := by
  have h := hM.conjTranspose_mul_mul_same (CFC.sqrt S)
  rw [(CFC.sqrt_nonneg S).posSemidef.isHermitian.eq] at h
  exact CFC.sqrt_mul_sqrt_self _ h.nonneg

theorem transportOptimizer_posDef {S M : Matrix n n ℂ} (hS : S.PosDef) (hM : M.PosDef) :
    (transportOptimizer S M).PosDef := by
  have hi : Function.Injective (CFC.sqrt S).mulVec :=
    Matrix.mulVec_injective_iff_isUnit.mpr hS.posDef_sqrt.isUnit
  have h := (fidelityCore_posDef hS hM).inv.conjTranspose_mul_mul_same hi
  simpa only [hS.posDef_sqrt.isHermitian.eq, transportOptimizer] using h

/-- The constructed matrix solves the transport equation without an existence assumption. -/
theorem transportOptimizer_solve {S M : Matrix n n ℂ} (hS : S.PosDef) (hM : M.PosDef) :
    transportOptimizer S M * M * transportOptimizer S M = S := by
  letI : Invertible (fidelityCore S M) := (fidelityCore_posDef hS hM).isUnit.invertible
  calc
    _ = CFC.sqrt S * (fidelityCore S M)⁻¹ *
        (CFC.sqrt S * M * CFC.sqrt S) * (fidelityCore S M)⁻¹ * CFC.sqrt S := by
      simp only [transportOptimizer, Matrix.mul_assoc]
    _ = CFC.sqrt S * (fidelityCore S M)⁻¹ *
        (fidelityCore S M * fidelityCore S M) * (fidelityCore S M)⁻¹ * CFC.sqrt S := by
      rw [fidelityCore_mul_self hM.posSemidef]
    _ = CFC.sqrt S * CFC.sqrt S := by
      simp only [Matrix.mul_assoc, Matrix.inv_mul_cancel_left_of_invertible,
        Matrix.mul_inv_cancel_left_of_invertible]
    _ = S := CFC.sqrt_mul_sqrt_self S hS.posSemidef.nonneg

/-- The trace value at the constructed transport matrix equals fidelity. -/
theorem trace_transportOptimizer_eq_fidelity {S M : Matrix n n ℂ}
    (hS : S.PosDef) (hM : M.PosDef) :
    realTrace (M * transportOptimizer S M) = fidelity S M := by
  letI : Invertible (fidelityCore S M) := (fidelityCore_posDef hS hM).isUnit.invertible
  calc
    _ = realTrace ((CFC.sqrt S * M * CFC.sqrt S) * (fidelityCore S M)⁻¹) := by
      simpa only [transportOptimizer, Matrix.mul_assoc] using
        realTrace_mul_comm (M * CFC.sqrt S * (fidelityCore S M)⁻¹) (CFC.sqrt S)
    _ = realTrace ((fidelityCore S M * fidelityCore S M) * (fidelityCore S M)⁻¹) := by
      rw [fidelityCore_mul_self hM.posSemidef]
    _ = fidelity S M := by
      rw [Matrix.mul_inv_cancel_right_of_invertible]
      rfl

/-- Faithful fidelity is the attained transport minimum, with the minimizer explicitly built. -/
theorem fidelity_variational_posDef {S M : Matrix n n ℂ} (hS : S.PosDef) (hM : M.PosDef) :
    ∃ T : Matrix n n ℂ, T.PosDef ∧ transportCost S M T = 2 * fidelity S M ∧
      ∀ Z : Matrix n n ℂ, Z.PosDef → 2 * fidelity S M ≤ transportCost S M Z := by
  refine ⟨transportOptimizer S M, transportOptimizer_posDef hS hM, ?_, ?_⟩
  · rw [transportCost_at_transport (transportOptimizer_posDef hS hM)
      (transportOptimizer_solve hS hM), trace_transportOptimizer_eq_fidelity hS hM]
  · intro Z hZ
    rw [← trace_transportOptimizer_eq_fidelity hS hM]
    exact transportCost_lower_bound hM.posSemidef (transportOptimizer_posDef hS hM).isHermitian
      hZ (transportOptimizer_solve hS hM)

theorem fidelity_nonneg (S M : Matrix n n ℂ) : 0 ≤ fidelity S M :=
  realTrace_nonneg (CFC.sqrt_nonneg _).posSemidef

theorem transportCost_swap_inv (S M : Matrix n n ℂ) {Z : Matrix n n ℂ} (hZ : Z.PosDef) :
    transportCost S M Z⁻¹ = transportCost M S Z := by
  letI : Invertible Z := hZ.isUnit.invertible
  simp only [transportCost, Matrix.inv_inv_of_invertible, add_comm]

/-- Symmetry follows from the variational formula and inversion of its actual minimizers. -/
theorem fidelity_symm_posDef {S M : Matrix n n ℂ} (hS : S.PosDef) (hM : M.PosDef) :
    fidelity S M = fidelity M S := by
  obtain ⟨T, hT, hval, hmin⟩ := fidelity_variational_posDef hS hM
  obtain ⟨U, hU, hval', hmin'⟩ := fidelity_variational_posDef hM hS
  have h₁ := hmin U⁻¹ hU.inv
  have h₂ := hmin' T⁻¹ hT.inv
  rw [transportCost_swap_inv S M hU, hval'] at h₁
  rw [transportCost_swap_inv M S hT, hval] at h₂
  linarith

theorem transportCost_mono {S₁ S₂ M₁ M₂ Z : Matrix n n ℂ}
    (hS : S₁ ≤ S₂) (hM : M₁ ≤ M₂) (hZ : Z.PosDef) :
    transportCost S₁ M₁ Z ≤ transportCost S₂ M₂ Z := by
  have h₁ := realTrace_mul_mono hZ.inv.posSemidef hS
  have h₂ := realTrace_mul_mono hZ.posSemidef hM
  rw [realTrace_mul_comm Z⁻¹ S₁, realTrace_mul_comm Z⁻¹ S₂] at h₁
  rw [realTrace_mul_comm Z M₁, realTrace_mul_comm Z M₂] at h₂
  exact add_le_add h₁ h₂

/-- Joint monotonicity on faithful inputs, with no commutation assumption. -/
theorem fidelity_mono_posDef {S₁ S₂ M₁ M₂ : Matrix n n ℂ}
    (hS₁ : S₁.PosDef) (hS₂ : S₂.PosDef) (hM₁ : M₁.PosDef) (hM₂ : M₂.PosDef)
    (hS : S₁ ≤ S₂) (hM : M₁ ≤ M₂) : fidelity S₁ M₁ ≤ fidelity S₂ M₂ := by
  obtain ⟨_, _, _, hmin⟩ := fidelity_variational_posDef hS₁ hM₁
  obtain ⟨T, hT, hval, _⟩ := fidelity_variational_posDef hS₂ hM₂
  have h := (hmin T hT).trans (transportCost_mono hS hM hT)
  rw [hval] at h
  linarith

theorem transportCost_weighted_add (S₁ S₂ M₁ M₂ Z : Matrix n n ℂ) (a b : ℝ) :
    transportCost (a • S₁ + b • S₂) (a • M₁ + b • M₂) Z =
      a * transportCost S₁ M₁ Z + b * transportCost S₂ M₂ Z := by
  simp only [transportCost, Matrix.add_mul, smul_mul_assoc, realTrace_add, realTrace_smul]
  ring

omit [DecidableEq n] in
/-- A positive convex mixture stays positive definite, including endpoint weights. -/
theorem posDef_convex_mixture {S T : Matrix n n ℂ} (hS : S.PosDef) (hT : T.PosDef)
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    (a • S + b • T).PosDef := by
  by_cases hzero : a = 0
  · have hb1 : b = 1 := by linarith
    simpa only [hzero, hb1, zero_smul, one_smul, zero_add] using hT
  · have ha' : 0 < a := lt_of_le_of_ne ha (Ne.symm hzero)
    exact (hS.smul ha').add_posSemidef
      (show (b • T).PosSemidef from (smul_nonneg hb hT.posSemidef.nonneg).posSemidef)

/-- Joint concavity of fidelity on positive definite input pairs. -/
theorem fidelity_concave_posDef {S₁ S₂ M₁ M₂ : Matrix n n ℂ}
    (hS₁ : S₁.PosDef) (hS₂ : S₂.PosDef) (hM₁ : M₁.PosDef) (hM₂ : M₂.PosDef)
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    a * fidelity S₁ M₁ + b * fidelity S₂ M₂ ≤
      fidelity (a • S₁ + b • S₂) (a • M₁ + b • M₂) := by
  obtain ⟨_, _, _, hmin₁⟩ := fidelity_variational_posDef hS₁ hM₁
  obtain ⟨_, _, _, hmin₂⟩ := fidelity_variational_posDef hS₂ hM₂
  obtain ⟨T, hT, hval, _⟩ := fidelity_variational_posDef
    (posDef_convex_mixture hS₁ hS₂ ha hb hab) (posDef_convex_mixture hM₁ hM₂ ha hb hab)
  have h := add_le_add (mul_le_mul_of_nonneg_left (hmin₁ T hT) ha)
    (mul_le_mul_of_nonneg_left (hmin₂ T hT) hb)
  rw [← transportCost_weighted_add, hval] at h
  linarith

end MatrixSpencer
