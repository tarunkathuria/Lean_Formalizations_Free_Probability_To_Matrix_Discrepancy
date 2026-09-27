import HigherRankKS.CarrierPower
import MatrixSpencer.DyadicRoot
import MatrixSpencer.TsallisHessian
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Tactic

/-!
# Smoothness of the actual dyadic carrier power

Repeated positive square roots are identified with `CFC.rpow`. Natural powers
of these roots prove smoothness of every nonnegative dyadic rational matrix
power, including the exponent `1 - 1/q` selected in Part III. The scalar trace
factor is differentiated as an actual positive real power.
-/

noncomputable section
open Matrix MatrixSpencer Filter Topology
open scoped MatrixOrder ComplexOrder Matrix.Norms.L2Operator ContDiff

namespace HigherRankKS

variable {n : Type*} [Fintype n] [DecidableEq n]
local instance carrierSmoothnessCStar : CStarAlgebra (Matrix n n ℂ) := {}

/-- The verified repeated square root agrees with the actual CFC fractional power. -/
theorem dyadicRoot_eq_rpow (k : ℕ) {M : Matrix n n ℂ} (hM : M.PosSemidef) :
    dyadicRoot k M = CFC.rpow M ((1 : ℝ) / (2 : ℝ) ^ k) := by
  induction k with
  | zero => simpa using (CFC.rpow_one M hM.nonneg).symm
  | succ k ih =>
    rw [dyadicRoot_succ, ih, CFC.sqrt_eq_rpow]
    simp only [CFC.rpow_eq_pow]
    rw [CFC.rpow_rpow_of_exponent_nonneg M ((1 : ℝ) / (2 : ℝ) ^ k) (1 / 2 : ℝ)
      (by positivity) (by norm_num) hM.nonneg]
    congr 1
    rw [pow_succ]
    ring

/-- Nonnegative dyadic rational powers have an explicit repeated-root polynomial. -/
theorem rpow_dyadic_eq_root_pow (k ℓ : ℕ) {M : Matrix n n ℂ} (hM : M.PosSemidef) :
    CFC.rpow M ((ℓ : ℝ) / (2 : ℝ) ^ k) = dyadicRoot k M ^ ℓ := by
  rw [dyadicRoot_eq_rpow k hM]
  simp only [CFC.rpow_eq_pow]
  rw [← CFC.rpow_natCast (M ^ ((1 : ℝ) / (2 : ℝ) ^ k)) ℓ CFC.rpow_nonneg,
    CFC.rpow_rpow_of_exponent_nonneg M ((1 : ℝ) / (2 : ℝ) ^ k) (ℓ : ℝ)
      (by positivity) (Nat.cast_nonneg _) hM.nonneg]
  congr 1
  ring

/-- Actual matrix power is smooth at each positive-definite Hermitian matrix. -/
theorem contDiffAt_rpow_dyadic (k ℓ : ℕ) (S : selfAdjoint (Matrix n n ℂ))
    (hS : (S : Matrix n n ℂ).PosDef) :
    ContDiffAt ℝ ∞ (fun X : selfAdjoint (Matrix n n ℂ) =>
      CFC.rpow (X : Matrix n n ℂ) ((ℓ : ℝ) / (2 : ℝ) ^ k)) S := by
  have hd := (hermitianInclusion (n := n)).contDiff.contDiffAt.comp S
    (contDiffAt_hermitianDyadicRoot k S hS)
  have hp : ContDiffAt ℝ ∞ (fun X : selfAdjoint (Matrix n n ℂ) =>
      dyadicRoot k (X : Matrix n n ℂ) ^ ℓ) S := by
    simpa only [Function.comp_apply, hermitianInclusion_apply, hermitianDyadicRoot_coe] using hd.pow ℓ
  apply hp.congr_of_eventuallyEq
  filter_upwards [eventually_nonneg_of_posDef S hS] with X hX
  exact rpow_dyadic_eq_root_pow k ℓ hX.posSemidef

theorem contDiffOn_rpow_dyadic (k ℓ : ℕ) :
    ContDiffOn ℝ ∞ (fun X : selfAdjoint (Matrix n n ℂ) =>
      CFC.rpow (X : Matrix n n ℂ) ((ℓ : ℝ) / (2 : ℝ) ^ k))
      {X | (X : Matrix n n ℂ).PosDef} :=
  fun X hX => (contDiffAt_rpow_dyadic k ℓ X hX).contDiffWithinAt

lemma dyadic_complement_eq (k : ℕ) :
    1 - (1 : ℝ) / (2 : ℝ) ^ k = ((2 ^ k - 1 : ℕ) : ℝ) / (2 : ℝ) ^ k := by
  rw [Nat.cast_sub (by exact one_le_pow₀ (by decide : (1 : ℕ) ≤ 2)), Nat.cast_pow]
  norm_num
  field_simp

theorem contDiffAt_rpow_dyadic_complement (k : ℕ) (S : selfAdjoint (Matrix n n ℂ))
    (hS : (S : Matrix n n ℂ).PosDef) :
    ContDiffAt ℝ ∞ (fun X : selfAdjoint (Matrix n n ℂ) =>
      CFC.rpow (X : Matrix n n ℂ) (1 - (1 : ℝ) / (2 : ℝ) ^ k)) S := by
  rw [dyadic_complement_eq]
  exact contDiffAt_rpow_dyadic k (2 ^ k - 1) S hS

theorem contDiffAt_carrierPower_dyadic (k : ℕ)
    (S : selfAdjoint (Matrix n n ℂ)) (hS : (S : Matrix n n ℂ).PosDef) :
    ContDiffAt ℝ ∞ (fun X : selfAdjoint (Matrix n n ℂ) =>
      carrierPower ((1 : ℝ) / (2 : ℝ) ^ k) (X : Matrix n n ℂ)) S := by
  rcases isEmpty_or_nonempty n with he | hn
  · letI := he
    have heq : (fun X : selfAdjoint (Matrix n n ℂ) =>
        carrierPower ((1 : ℝ) / (2 : ℝ) ^ k) (X : Matrix n n ℂ)) = fun _ => 0 := by
      funext X
      exact Subsingleton.elim _ _
    rw [heq]
    exact contDiffAt_const
  · letI := hn
    have ht : ContDiffAt ℝ ∞ (fun X : selfAdjoint (Matrix n n ℂ) =>
        realTrace (X : Matrix n n ℂ)) S :=
      (realTraceCLM (n := n)).contDiff.contDiffAt.comp S
        (hermitianInclusion (n := n)).contDiff.contDiffAt
    have htrace : 0 < realTrace (S : Matrix n n ℂ) := (Complex.pos_iff.mp hS.trace_pos).1
    have hscalar := ht.rpow_const_of_ne (p := (1 : ℝ) / (2 : ℝ) ^ k) htrace.ne'
    exact hscalar.smul (contDiffAt_rpow_dyadic_complement k S hS)

theorem contDiffOn_carrierPower_dyadic (k : ℕ) :
    ContDiffOn ℝ ∞ (fun X : selfAdjoint (Matrix n n ℂ) =>
      carrierPower ((1 : ℝ) / (2 : ℝ) ^ k) (X : Matrix n n ℂ))
      {X | (X : Matrix n n ℂ).PosDef} :=
  fun X hX => (contDiffAt_carrierPower_dyadic k X hX).contDiffWithinAt

/-- The exact natural-q formulation used by the parameter choice. -/
theorem contDiffAt_carrierPower_of_dyadic {q : ℕ} (hq : ∃ k : ℕ, q = 2 ^ k)
    (S : selfAdjoint (Matrix n n ℂ)) (hS : (S : Matrix n n ℂ).PosDef) :
    ContDiffAt ℝ ∞ (fun X : selfAdjoint (Matrix n n ℂ) =>
      carrierPower ((1 : ℝ) / q) (X : Matrix n n ℂ)) S := by
  obtain ⟨k, rfl⟩ := hq
  simpa using contDiffAt_carrierPower_dyadic k S hS

theorem contDiffOn_carrierPower_of_dyadic {q : ℕ} (hq : ∃ k : ℕ, q = 2 ^ k) :
    ContDiffOn ℝ ∞ (fun X : selfAdjoint (Matrix n n ℂ) =>
      carrierPower ((1 : ℝ) / q) (X : Matrix n n ℂ))
      {X | (X : Matrix n n ℂ).PosDef} :=
  fun X hX => (contDiffAt_carrierPower_of_dyadic hq X hX).contDiffWithinAt

/-- The same actual carrier with its natural Hermitian codomain. -/
def hermitianCarrierPower (β : ℝ) (X : selfAdjoint (Matrix n n ℂ)) :
    selfAdjoint (Matrix n n ℂ) := hermitianProjection (carrierPower β (X : Matrix n n ℂ))

@[simp] theorem hermitianCarrierPower_coe (β : ℝ) (X : selfAdjoint (Matrix n n ℂ)) :
    (hermitianCarrierPower β X : Matrix n n ℂ) = carrierPower β (X : Matrix n n ℂ) := by
  apply IsSelfAdjoint.coe_selfAdjointPart_apply
  exact (IsSelfAdjoint.all ((realTrace (X : Matrix n n ℂ)) ^ β)).smul
    CFC.rpow_nonneg.isSelfAdjoint

theorem contDiffAt_hermitianCarrierPower_of_dyadic {q : ℕ} (hq : ∃ k : ℕ, q = 2 ^ k)
    (S : selfAdjoint (Matrix n n ℂ)) (hS : (S : Matrix n n ℂ).PosDef) :
    ContDiffAt ℝ ∞ (hermitianCarrierPower ((1 : ℝ) / q)) S :=
  (hermitianProjection (n := n)).contDiff.contDiffAt.comp S
    (contDiffAt_carrierPower_of_dyadic hq S hS)

theorem contDiffOn_hermitianCarrierPower_of_dyadic {q : ℕ} (hq : ∃ k : ℕ, q = 2 ^ k) :
    ContDiffOn ℝ ∞ (hermitianCarrierPower (n := n) ((1 : ℝ) / q))
      {X | (X : Matrix n n ℂ).PosDef} :=
  fun X hX => (contDiffAt_hermitianCarrierPower_of_dyadic hq X hX).contDiffWithinAt

end HigherRankKS
