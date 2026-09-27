import MatrixSpencer.KSGlobalMinima
import MatrixSpencer.KSEndpointRetirement

/-! Exact updates of the original coefficients, centers, and owners at a retirement. -/

open scoped BigOperators Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
open Matrix Set

noncomputable section
namespace MatrixSpencer.KSPotentialModels

variable {N : ℕ} {n : Type*} [Fintype n] [DecidableEq n]

theorem center_update (A : Fin N → Matrix n n ℂ) (x : Fin N → ℝ) (i : Fin N) (s : ℝ) :
    center A (Function.update x i s) = center A x + (s - x i) • A i := by
  have hd : center A (Function.update x i s) - center A x = (s - x i) • A i := by
    rw [center, center, ← Finset.sum_sub_distrib]
    rw [Finset.sum_eq_single i]
    · simp only [Function.update_self, sub_smul]
    · intro j _ hji
      simp only [Function.update_of_ne hji, sub_self]
    · simp
  exact (sub_eq_iff_eq_add.mp hd).trans (add_comm _ _)

theorem signed_center_update (A : Fin N → Matrix n n ℂ) (x : Fin N → ℝ)
    (i : Fin N) (s : ℝ) :
    signedLift (center A (Function.update x i s)) =
      signedLift (center A x) + (s - x i) • signedLift (A i) := by
  rw [center_update]
  ext a b
  cases a <;> cases b <;>
    simp [signedLift, Matrix.fromBlocks, Matrix.add_apply, Matrix.smul_apply, Matrix.neg_apply,
      smul_add, smul_neg] <;> ring

theorem naturalOwners_update_endpoint (u : ℝ) (x : Fin N → ℝ) (i : Fin N)
    {s : ℝ} (hs : IsSign s) :
    naturalOwners u (Function.update x i s) = Function.update (naturalOwners u x) i 0 := by
  funext j
  by_cases hj : j = i
  · subst j
    simp only [naturalOwners, Function.update_self, hs.sq_eq_one, sub_self, mul_zero]
  · simp only [naturalOwners, Function.update_of_ne hj]

theorem truncatedOwners_update_endpoint (u : ℝ) {a : ℝ} (ha : 0 ≤ a)
    (x : Fin N → ℝ) (i : Fin N) {s : ℝ} (hs : s = -a ∨ s = a) :
    truncatedOwners a u (Function.update x i s) = Function.update (truncatedOwners a u x) i 0 := by
  have hsa : |s| = a := by rcases hs with rfl | rfl <;> simp [abs_of_nonneg ha]
  funext j
  by_cases hj : j = i
  · subst j
    simp [truncatedOwners, maskedOwners, live, Function.update_self, hsa]
  · simp [truncatedOwners, maskedOwners, live, naturalOwners, Function.update_of_ne hj]

def independentStateTransport [Nonempty n] (v : Fin N → n → ℂ) (θ : ℝ) (x : Fin N → ℝ) :=
  KSEndpointRetirement.independentTransport (signedLift (center (fun j => KSRankOne.atom (v j)) x))
    v (truncatedOwners (1 / 8) 64 x) θ

def spinStateTransport [Nonempty n] (v : Fin N → n → ℂ) (θ : ℝ) (x : Fin N → ℝ) :=
  KSEndpointRetirement.spinTransport (signedLift (center (fun j => KSRankOne.atom (v j)) x))
    v (naturalOwners 64 x) θ

theorem eighth_retire_plus [Nonempty n] (v : Fin N → n → ℂ) {θ : ℝ} (hθ : 0 < θ)
    {x : Fin N → ℝ} (hx : x ∈ ksCube (1 / 8)) (i : Fin N)
    (hsafe : 1 / 8 - x i ≤ truncatedOwners (1 / 8) 64 x i *
      realTrace (leftDensity (KSRankOne.atom (v i)) * independentStateTransport v θ x)) :
    eighthPotential (fun j => KSRankOne.atom (v j)) θ (Function.update x i (1 / 8)) ≤
      eighthPotential (fun j => KSRankOne.atom (v j)) θ x := by
  have hx' := ksCube_update_endpoint (by norm_num : (0 : ℝ) ≤ 1 / 8) hx i (Or.inr rfl)
  have hc : ∀ j, 0 ≤ truncatedOwners (1 / 8) 64 x j :=
    fun j => maskedOwners_nonneg (by norm_num) (by norm_num) hx _ j
  have hc' : ∀ j, 0 ≤ truncatedOwners (1 / 8) 64 (Function.update x i (1 / 8)) j :=
    fun j => maskedOwners_nonneg (by norm_num) (by norm_num) hx' _ j
  unfold eighthPotential commonPotential
  rw [KSCommonSource.potential_eq_independent _ _ (fun _ => KSRankOne.atom_isHermitian _) hc hθ,
    KSCommonSource.potential_eq_independent _ _ (fun _ => KSRankOne.atom_isHermitian _) hc' hθ,
    signed_center_update, truncatedOwners_update_endpoint 64 (by norm_num) x i (Or.inr rfl)]
  exact KSEndpointRetirement.independent_retire_plus _ v _ hc hθ i (hx.2 i) hsafe

theorem eighth_retire_minus [Nonempty n] (v : Fin N → n → ℂ) {θ : ℝ} (hθ : 0 < θ)
    {x : Fin N → ℝ} (hx : x ∈ ksCube (1 / 8)) (i : Fin N)
    (hsafe : 1 / 8 + x i ≤ truncatedOwners (1 / 8) 64 x i *
      realTrace (rightDensity (KSRankOne.atom (v i)) * independentStateTransport v θ x)) :
    eighthPotential (fun j => KSRankOne.atom (v j)) θ (Function.update x i (-(1 / 8))) ≤
      eighthPotential (fun j => KSRankOne.atom (v j)) θ x := by
  have hx' := ksCube_update_endpoint (by norm_num : (0 : ℝ) ≤ 1 / 8) hx i (Or.inl rfl)
  have hc : ∀ j, 0 ≤ truncatedOwners (1 / 8) 64 x j :=
    fun j => maskedOwners_nonneg (by norm_num) (by norm_num) hx _ j
  have hc' : ∀ j, 0 ≤ truncatedOwners (1 / 8) 64 (Function.update x i (-(1 / 8))) j :=
    fun j => maskedOwners_nonneg (by norm_num) (by norm_num) hx' _ j
  unfold eighthPotential commonPotential
  rw [KSCommonSource.potential_eq_independent _ _ (fun _ => KSRankOne.atom_isHermitian _) hc hθ,
    KSCommonSource.potential_eq_independent _ _ (fun _ => KSRankOne.atom_isHermitian _) hc' hθ,
    signed_center_update, truncatedOwners_update_endpoint 64 (by norm_num) x i (Or.inl rfl)]
  exact KSEndpointRetirement.independent_retire_minus _ v _ hc hθ i (hx.1 i) hsafe

def nearestSign (t : ℝ) : ℝ := if 0 ≤ t then 1 else -1

theorem nearestSign_isSign (t : ℝ) : IsSign (nearestSign t) := by
  unfold nearestSign
  split_ifs <;> simp [IsSign]

theorem nearestSign_distance {t : ℝ} (ht : -1 ≤ t ∧ t ≤ 1) :
    |nearestSign t - t| = 1 - |t| := by
  unfold nearestSign
  split_ifs with h
  · rw [abs_of_nonneg h, abs_of_nonneg (by linarith : 0 ≤ 1 - t)]
  · rw [abs_of_neg (lt_of_not_ge h), abs_of_nonpos (by linarith : -1 - t ≤ 0)]
    ring

theorem spin_retire_nearest [Nonempty n] (v : Fin N → n → ℂ) {θ : ℝ} (hθ : 0 < θ)
    {x : Fin N → ℝ} (hx : x ∈ ksCube 1) (i : Fin N)
    (hsafe : 1 - |x i| ≤ naturalOwners 64 x i *
      realTrace (KSSpinSource.doubled (KSRankOne.atom (v i)) * spinStateTransport v θ x)) :
    spinPotential (fun j => KSRankOne.atom (v j)) θ (Function.update x i (nearestSign (x i))) ≤
      spinPotential (fun j => KSRankOne.atom (v j)) θ x := by
  have hc : ∀ j, 0 ≤ naturalOwners 64 x j := fun j => naturalOwners_nonneg (by norm_num) le_rfl hx j
  unfold spinPotential
  rw [signed_center_update, naturalOwners_update_endpoint 64 x i (nearestSign_isSign _)]
  apply KSEndpointRetirement.spin_retire _ v _ hc hθ i
  rw [nearestSign_distance ⟨hx.1 i, hx.2 i⟩]
  exact hsafe

def MaxFrozenMinimum (a : ℝ) (f : (Fin N → ℝ) → ℝ) (x : Fin N → ℝ) : Prop :=
  x ∈ ksCube a ∧ IsMinOn f (ksCube a) x ∧
    ∀ y ∈ ksCube a, IsMinOn f (ksCube a) y → (ksFrozen a y).card ≤ (ksFrozen a x).card

theorem exists_maxFrozen_minimum (a : ℝ) (f : (Fin N → ℝ) → ℝ)
    (hmin : ∃ x ∈ ksCube a, IsMinOn f (ksCube a) x) :
    ∃ x, MaxFrozenMinimum a f x := by
  obtain ⟨x, hx, hm, hr⟩ := ks_exists_minimum_maximal_rank (ksCube a) f
    (fun x => (ksFrozen a x).card) N hmin (fun x _ => ksFrozen_card_le a x)
  exact ⟨x, hx, hm, hr⟩

theorem MaxFrozenMinimum.no_update {a : ℝ} (ha : 0 ≤ a)
    {f : (Fin N → ℝ) → ℝ} {x : Fin N → ℝ} (hx : MaxFrozenMinimum a f x)
    (i : Fin N) (hi : |x i| < a) {s : ℝ} (hs : s = -a ∨ s = a) :
    ¬ f (Function.update x i s) ≤ f x := by
  intro hle
  have hy := ksCube_update_endpoint ha hx.1 i hs
  have hm : IsMinOn f (ksCube a) (Function.update x i s) := fun y hy => hle.trans (hx.2.1 hy)
  have hcount := hx.2.2 _ hy hm
  have habs : |s| = a := by rcases hs with rfl | rfl <;> simp [abs_of_nonneg ha]
  exact (not_lt_of_ge hcount) (ksFrozen_lt_update x i hi s habs)

theorem eighth_maxFrozen_noSafe [Nonempty n] (v : Fin N → n → ℂ) {θ : ℝ} (hθ : 0 < θ)
    {x : Fin N → ℝ} (hx : MaxFrozenMinimum (1 / 8) (eighthPotential (fun j => KSRankOne.atom (v j)) θ) x)
    (i : Fin N) (hi : |x i| < 1 / 8) :
    truncatedOwners (1 / 8) 64 x i *
      realTrace (leftDensity (KSRankOne.atom (v i)) * independentStateTransport v θ x) < 1 / 8 - x i ∧
    truncatedOwners (1 / 8) 64 x i *
      realTrace (rightDensity (KSRankOne.atom (v i)) * independentStateTransport v θ x) < 1 / 8 + x i := by
  constructor
  · apply lt_of_not_ge
    intro hs
    exact hx.no_update (by norm_num) i hi (Or.inr rfl) (eighth_retire_plus v hθ hx.1 i hs)
  · apply lt_of_not_ge
    intro hs
    exact hx.no_update (by norm_num) i hi (Or.inl rfl) (eighth_retire_minus v hθ hx.1 i hs)

theorem spin_maxFrozen_noSafe [Nonempty n] (v : Fin N → n → ℂ) {θ : ℝ} (hθ : 0 < θ)
    {x : Fin N → ℝ} (hx : MaxFrozenMinimum 1 (spinPotential (fun j => KSRankOne.atom (v j)) θ) x)
    (i : Fin N) (hi : |x i| < 1) :
    naturalOwners 64 x i *
      realTrace (KSSpinSource.doubled (KSRankOne.atom (v i)) * spinStateTransport v θ x) < 1 - |x i| := by
  apply lt_of_not_ge
  intro hs
  have hsign := nearestSign_isSign (x i)
  have hsend : nearestSign (x i) = -(1 : ℝ) ∨ nearestSign (x i) = 1 := hsign.symm
  exact hx.no_update (by norm_num) i hi hsend (spin_retire_nearest v hθ hx.1 i hs)

/-- Failed genuine endpoint tests give the exact small-atom and force bounds
used in the full-cube projection argument. -/
theorem spin_noSafe_scalar_bounds {x q : ℝ} (hx : |x| < 1) (hq : 0 < q)
    (hsafe : (64 * (1 - x ^ 2)) * q < 1 - |x|) :
    (64 * (1 - x ^ 2)) * q ^ 2 ≤ 1 / 64 ∧ |128 * x * q| ≤ 1 := by
  have ha := abs_nonneg x
  have hrho : 0 < 1 - |x| := by linarith
  have hfactor : 64 * (1 - x ^ 2) = 64 * (1 - |x|) * (1 + |x|) := by
    nlinarith [sq_abs x]
  have hmul : 64 * (1 + |x|) * q < 1 := by
    apply (mul_lt_mul_left hrho).mp
    calc
      (1 - |x|) * (64 * (1 + |x|) * q) = (64 * (1 - x ^ 2)) * q := by rw [hfactor]; ring
      _ < 1 - |x| := hsafe
      _ = (1 - |x|) * 1 := by ring
  have hqcap : q ≤ 1 / 64 := by nlinarith [mul_nonneg ha hq.le]
  constructor
  · have hp := mul_lt_mul_of_pos_right hsafe hq
    nlinarith [mul_nonneg ha hq.le]
  · rw [abs_mul, abs_mul, abs_of_pos hq]
    norm_num
    nlinarith [mul_nonneg (by linarith : 0 ≤ 1 - |x|) hq.le]

end MatrixSpencer.KSPotentialModels
