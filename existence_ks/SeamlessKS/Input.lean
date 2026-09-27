import MatrixSpencer.KSInitialBounds
import MatrixSpencer.KSDebitPotential
import SeamlessKS.Source

/-!
# Original Parseval input and the new source's initial bound

All labels, including zero atoms, are retained. The maximum atom size is a
finite max fold over explicitly computed squared vector norms. This file
uses only the general rank-one, source, and variance identities from the
copied library, not a previous KS walk or its endpoint theorem.
-/

open Matrix
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section
namespace SeamlessKS.Input
open MatrixSpencer

variable {N d : ℕ}
local instance {k : Type*} [Fintype k] [DecidableEq k] : CStarAlgebra (Matrix k k ℂ) := {}

def size (v : Fin N → Fin d → ℂ) (i : Fin N) : ℝ := ∑ j, Complex.normSq (v i j)
def maximum (l : List ℝ) : ℝ := l.foldr max 0
def epsilon (v : Fin N → Fin d → ℂ) : ℝ := maximum ((List.finRange N).map (size v))
def delta (v : Fin N → Fin d → ℂ) : ℝ := Real.sqrt (epsilon v)
def theta (v : Fin N → Fin d → ℂ) : ℝ := delta v / Real.sqrt (2 * (d : ℝ))

theorem size_eq_norm (v : Fin N → Fin d → ℂ) (i : Fin N) :
    size v i = ‖KSRankOne.atom (v i)‖ := by
  rw [KSRankOne.atom_norm, KSRankOne.realTrace_atom]
  rfl

theorem maximum_nonneg (l : List ℝ) : 0 ≤ maximum l := by
  induction l with
  | nil => exact le_rfl
  | cons a l ih => exact ih.trans (le_max_right _ _)

theorem le_maximum {l : List ℝ} {a : ℝ} (ha : a ∈ l) : a ≤ maximum l := by
  induction l with
  | nil => simp at ha
  | cons b l ih =>
    rcases List.mem_cons.mp ha with rfl | ha
    · exact le_max_left _ _
    · exact (ih ha).trans (le_max_right _ _)

theorem maximum_le {l : List ℝ} {R : ℝ} (hR : 0 ≤ R)
    (hl : ∀ a ∈ l, a ≤ R) : maximum l ≤ R := by
  induction l with
  | nil => exact hR
  | cons a l ih =>
    exact max_le (hl a List.mem_cons_self) (ih (fun b hb => hl b (List.mem_cons_of_mem _ hb)))

theorem epsilon_nonneg (v : Fin N → Fin d → ℂ) : 0 ≤ epsilon v := maximum_nonneg _

theorem atom_norm_le_epsilon (v : Fin N → Fin d → ℂ) (i : Fin N) :
    ‖KSRankOne.atom (v i)‖ ≤ epsilon v := by
  rw [← size_eq_norm]
  exact le_maximum (List.mem_map.mpr ⟨i, by simp, rfl⟩)

theorem epsilon_le (v : Fin N → Fin d → ℂ) {e : ℝ} (he : 0 ≤ e)
    (hsize : ∀ i, ‖KSRankOne.atom (v i)‖ ≤ e) : epsilon v ≤ e := by
  apply maximum_le he
  intro a ha
  obtain ⟨i, _, rfl⟩ := List.mem_map.mp ha
  exact (size_eq_norm v i).le.trans (hsize i)

theorem atom_norm_le_one (v : Fin N → Fin d → ℂ)
    (hp : (∑ i, KSRankOne.atom (v i)) = 1) (i : Fin N) :
    ‖KSRankOne.atom (v i)‖ ≤ 1 := by
  have hle : KSRankOne.atom (v i) ≤ 1 := by
    rw [← hp]
    exact Finset.single_le_sum
      (fun j (_ : j ∈ Finset.univ) => (KSRankOne.atom_posSemidef (v j)).nonneg)
      (Finset.mem_univ i)
  apply (CStarAlgebra.norm_le_iff_le_algebraMap _ zero_le_one
    (KSRankOne.atom_posSemidef (v i)).nonneg).mpr
  simpa using hle

theorem epsilon_le_one (v : Fin N → Fin d → ℂ)
    (hp : (∑ i, KSRankOne.atom (v i)) = 1) : epsilon v ≤ 1 :=
  epsilon_le v zero_le_one (atom_norm_le_one v hp)

/-- Tracing Parseval uses every original label. -/
theorem dimension_le_labels_epsilon (v : Fin N → Fin d → ℂ)
    (hp : (∑ i, KSRankOne.atom (v i)) = 1) : (d : ℝ) ≤ (N : ℝ) * epsilon v := by
  have he := congrArg realTrace hp
  rw [realTrace_sum] at he
  have hone : realTrace (1 : Matrix (Fin d) (Fin d) ℂ) = d := by simp [realTrace]
  rw [hone] at he
  have hh := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => atom_norm_le_epsilon v i)
  simp only [KSRankOne.atom_norm, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul] at hh
  rwa [he] at hh

theorem dimension_le_labels (v : Fin N → Fin d → ℂ)
    (hp : (∑ i, KSRankOne.atom (v i)) = 1) : d ≤ N := by
  have h := dimension_le_labels_epsilon v hp
  have hu := mul_le_mul_of_nonneg_left (epsilon_le_one v hp) (Nat.cast_nonneg N : (0:ℝ) ≤ N)
  have hh : (d : ℝ) ≤ N := by linarith
  exact_mod_cast hh

theorem labels_pos (v : Fin N → Fin d → ℂ) (hd : 0 < d)
    (hp : (∑ i, KSRankOne.atom (v i)) = 1) : 0 < N :=
  hd.trans_le (dimension_le_labels v hp)

theorem epsilon_pos (v : Fin N → Fin d → ℂ) (hd : 0 < d)
    (hp : (∑ i, KSRankOne.atom (v i)) = 1) : 0 < epsilon v := by
  have h := dimension_le_labels_epsilon v hp
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  by_contra hh
  have hm := mul_nonpos_of_nonneg_of_nonpos hN (le_of_not_gt hh)
  linarith

theorem dimension_div_labels_le_epsilon (v : Fin N → Fin d → ℂ) (hd : 0 < d)
    (hp : (∑ i, KSRankOne.atom (v i)) = 1) : (d : ℝ)/(N : ℝ) ≤ epsilon v := by
  have hN : (0 : ℝ) < N := by exact_mod_cast labels_pos v hd hp
  apply (div_le_iff₀ hN).mpr
  simpa only [mul_comm] using dimension_le_labels_epsilon v hp

theorem one_div_labels_le_epsilon (v : Fin N → Fin d → ℂ) (hd : 0 < d)
    (hp : (∑ i, KSRankOne.atom (v i)) = 1) : 1/(N : ℝ) ≤ epsilon v := by
  have hd' : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hN : (0 : ℝ) < N := by exact_mod_cast labels_pos v hd hp
  exact (div_le_div_of_nonneg_right hd' hN.le).trans (dimension_div_labels_le_epsilon v hd hp)

theorem delta_pos (v : Fin N → Fin d → ℂ) (hd : 0 < d)
    (hp : (∑ i, KSRankOne.atom (v i)) = 1) : 0 < delta v :=
  Real.sqrt_pos.mpr (epsilon_pos v hd hp)

theorem delta_nonneg (v : Fin N → Fin d → ℂ) : 0 ≤ delta v := Real.sqrt_nonneg _

theorem delta_sq (v : Fin N → Fin d → ℂ) : delta v ^ 2 = epsilon v :=
  Real.sq_sqrt (epsilon_nonneg v)

theorem delta_le_one (v : Fin N → Fin d → ℂ)
    (hp : (∑ i, KSRankOne.atom (v i)) = 1) : delta v ≤ 1 := by
  simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt (epsilon_le_one v hp)

theorem delta_inv_le_sqrt_labels (v : Fin N → Fin d → ℂ) (hd : 0 < d)
    (hp : (∑ i, KSRankOne.atom (v i)) = 1) : (delta v)⁻¹ ≤ Real.sqrt (N : ℝ) := by
  have he := one_div_labels_le_epsilon v hd hp
  have hep := epsilon_pos v hd hp
  have hN : (0 : ℝ) < N := by exact_mod_cast labels_pos v hd hp
  have hi : (epsilon v)⁻¹ ≤ (N : ℝ) := by
    rw [inv_eq_one_div]
    apply (div_le_iff₀ hep).mpr
    have hh := (div_le_iff₀ hN).mp he
    nlinarith
  simpa only [Real.sqrt_inv, delta] using Real.sqrt_le_sqrt hi

theorem theta_eq_regularizer (v : Fin N → Fin d → ℂ) :
    theta v = ksRegularizerScale (epsilon v) (Fin d) := by
  simp only [theta, delta, ksRegularizerScale, Fintype.card_sum, Fintype.card_fin,
    Nat.cast_add]
  congr 2
  ring

theorem theta_pos (v : Fin N → Fin d → ℂ) (hd : 0 < d)
    (hp : (∑ i, KSRankOne.atom (v i)) = 1) : 0 < theta v := by
  unfold theta
  exact div_pos (delta_pos v hd hp) (Real.sqrt_pos.mpr (by exact_mod_cast (show 0 < 2*d by omega)))

theorem theta_inv_le_sqrt_two_labels (v : Fin N → Fin d → ℂ) (hd : 0 < d)
    (hp : (∑ i, KSRankOne.atom (v i)) = 1) :
    (theta v)⁻¹ ≤ Real.sqrt (2*(N : ℝ)) := by
  have hep := epsilon_pos v hd hp
  have hdim := dimension_le_labels_epsilon v hp
  have hquot : (2*(d : ℝ))/epsilon v ≤ 2*(N : ℝ) := by
    apply (div_le_iff₀ hep).mpr
    nlinarith
  have heq : (theta v)⁻¹ = Real.sqrt ((2*(d : ℝ))/epsilon v) := by
    rw [Real.sqrt_div (by positivity)]
    simp [theta, delta]
  rw [heq]
  exact Real.sqrt_le_sqrt hquot

/-- Arbitrary nonnegative source weights bounded by 128 satisfy the new
physical variance budget, uniformly on every face. -/
theorem source_variance_le (v : Fin N → Fin d → ℂ)
    (hp : (∑ i, KSRankOne.atom (v i)) = 1) (c : Fin N → ℝ)
    (hc : ∀ i, c i ≤ 128) :
    covarianceSource (KSSpinSource.family (fun i => KSRankOne.atom (v i)))
      (KSSpinSource.coefficientCovariance c) 1 ≤
        (256 * epsilon v) • (1 : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) ℂ) := by
  calc
    _ ≤ covarianceSource (KSSpinSource.family (fun i => KSRankOne.atom (v i)))
        (KSSpinSource.coefficientCovariance (fun _ => 128)) 1 := by
      rw [KSSpinSource.source_identity, KSSpinSource.source_identity]
      apply Finset.sum_le_sum
      intro i _
      apply smul_le_smul_of_nonneg_right (by linarith [hc i])
      apply Matrix.PosSemidef.nonneg
      apply KSSpinSource.doubled_posSemidef
      simpa only [pow_two] using (KSRankOne.atom_posSemidef (v i)).pow 2
    _ ≤ _ := by
      simpa only [show (2:ℝ)*128=256 by norm_num] using
        KSSpinSource.initial_variance_le v hp (atom_norm_le_epsilon v) (by norm_num : (0:ℝ) ≤ 128)

theorem initial_potential_le (v : Fin N → Fin d → ℂ) (hd : 0 < d)
    (hp : (∑ i, KSRankOne.atom (v i)) = 1) (c : Fin N → ℝ)
    (hc0 : ∀ i, 0 ≤ c i) (hc128 : ∀ i, c i ≤ 128) :
    KSDebitPotential.potential 0 0 v c (theta v) ≤ 34 * delta v := by
  letI : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  have hb := ks_ownerPotential_le_variance Matrix.isHermitian_zero
    (KSSpinSource.family (fun i => KSRankOne.atom (v i)))
    (KSSpinSource.family_isHermitian _ (fun i => KSRankOne.atom_isHermitian _))
    (KSSpinSource.coefficientCovariance_posSemidef hc0) (theta_pos v hd hp).le
    (source_variance_le v hp c hc128)
  have hreg := ksRegularizerScale_budget (n := Fin d) (epsilon v)
  rw [← theta_eq_regularizer v] at hreg
  have hs : Real.sqrt (256 * epsilon v) = 16 * delta v := by
    rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 256)]
    norm_num [delta]
  rw [norm_zero, zero_add, hs, hreg] at hb
  have hz : KSDebitCenter.center (0 : Matrix (Fin d) (Fin d) ℂ) 0 = 0 := by
    simp [KSDebitCenter.center, signedLift, KSSpinSource.doubled]
  unfold KSDebitPotential.potential
  rw [hz]
  dsimp only [delta] at *
  linarith

/-- The actual smooth source satisfies the bound at the origin. -/
theorem smooth_initial_potential_le (v : Fin N → Fin d → ℂ) (hd : 0 < d)
    (hp : (∑ i, KSRankOne.atom (v i)) = 1) {zeta : ℝ} (hzeta : 0 ≤ zeta) :
    KSDebitPotential.potential 0 0 v (fun _ => Source.weight 64 zeta 0) (theta v) ≤
      34 * delta v := by
  apply initial_potential_le v hd hp
  · intro i
    exact Source.weight_nonneg (by norm_num) (by norm_num)
  · intro i
    simpa only [show (2:ℝ)*64=128 by norm_num] using
      Source.weight_upper (by norm_num : (0:ℝ) ≤ 64) hzeta 0

end SeamlessKS.Input
