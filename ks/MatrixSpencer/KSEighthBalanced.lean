import MatrixSpencer.KSEighthCompletion
import MatrixSpencer.KSBalancedSpin
import MatrixSpencer.KSRankOne

/-!
# The  coefficient data from physical rank-one transport

The actual matrices S and Z are positive on the fixed physical source support.
The construction below discharges every Fisher and no-safe hypothesis of the
finite two-sign completion theorem from that concrete transport equation.
-/

open Matrix
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section
namespace MatrixSpencer.KSEighthBalanced
open KSEighthComparison

variable {ι n : Type*} [Fintype ι] [DecidableEq ι] [Fintype n] [DecidableEq n]
local instance : CStarAlgebra (Matrix n n ℂ) := {}

/-- Rectangular congruence preserves the literal complex rank-one atom. -/
theorem atom_congruence {m : Type*} [Fintype m] [DecidableEq m]
    (V : Matrix m n ℂ) (v : n → ℂ) :
    V * KSRankOne.atom v * Vᴴ = KSRankOne.atom (V *ᵥ v) := by
  simp only [KSRankOne.atom, Matrix.mul_vecMulVec, Matrix.vecMulVec_mul,
    Matrix.star_mulVec]

/-- Positive scaling and congruence retain the exact rank-one square identity. -/
theorem scaled_atom_square (v : n → ℂ) (R : Matrix n n ℂ) (s : ℝ) :
    (s • (R * KSRankOne.atom v * Rᴴ)) * (s • (R * KSRankOne.atom v * Rᴴ)) =
      realTrace (s • (R * KSRankOne.atom v * Rᴴ)) •
        (s • (R * KSRankOne.atom v * Rᴴ)) := by
  rw [atom_congruence]
  simp only [Matrix.smul_mul, Matrix.mul_smul, KSRankOne.atom_sq_real,
    realTrace_smul, smul_smul]
  congr 1
  ring

def owner (x : ι → ℝ) (i : ι) : ℝ := 64 * (1 - x i ^ 2)

def probe (v : ι → n → ℂ) (Z : Matrix n n ℂ) (i : ι) : ℝ :=
  realTrace (Z * KSRankOne.atom (v i))

def atoms (v : ι → n → ℂ) (x : ι → ℝ) (Z : Matrix n n ℂ) : ι → Matrix n n ℂ :=
  KSBalancedSpin.atom (fun i => KSRankOne.atom (v i)) (owner x) Z

def masses (v : ι → n → ℂ) (x : ι → ℝ) (S Z : Matrix n n ℂ) : ι → ℝ :=
  KSBalancedSpin.mass (fun i => KSRankOne.atom (v i)) (owner x) S Z

theorem owner_pos (x : ι → ℝ) (hx : ∀ i, |x i| ≤ (1 / 8 : ℝ)) (i : ι) :
    0 < owner x i := by
  have hh := eighth_owner_lower (hx i)
  change 0 < 64 * (1 - x i ^ 2)
  linarith

theorem atoms_square (v : ι → n → ℂ) (x : ι → ℝ) (Z : Matrix n n ℂ) (i : ι) :
    atoms v x Z i * atoms v x Z i = realTrace (atoms v x Z i) • atoms v x Z i := by
  simpa only [atoms, KSBalancedSpin.atom, balancedKraus,
    (CFC.sqrt_nonneg Z).posSemidef.isHermitian.eq] using
    scaled_atom_square (v i) (CFC.sqrt Z) (Real.sqrt (owner x i))

theorem physicalGram_diagonal (v : ι → n → ℂ) (x : ι → ℝ) (S Z : Matrix n n ℂ) (i : ι) :
    physicalRealGram (balancedDensity S Z) (atoms v x Z) i i =
      realTrace (atoms v x Z i) * masses v x S Z i := by
  change realTrace (balancedDensity S Z * atoms v x Z i * atoms v x Z i) = _
  rw [Matrix.mul_assoc, atoms_square, Matrix.mul_smul, realTrace_smul]
  rfl

theorem trace_atoms_sq (v : ι → n → ℂ) (x : ι → ℝ)
    (hx : ∀ i, |x i| ≤ (1 / 8 : ℝ)) {Z : Matrix n n ℂ} (hZ : Z.PosDef) (i : ι) :
    realTrace (atoms v x Z i) ^ 2 = owner x i * probe v Z i ^ 2 := by
  rw [atoms, KSBalancedSpin.trace_atom _ _ hZ]
  change (Real.sqrt (owner x i) * probe v Z i) ^ 2 = _
  rw [mul_pow, Real.sq_sqrt (owner_pos x hx i).le]

/-- Every field is derived from the actual faithful support density, positive
transport, and the exact trace-and-prepare transport equation. -/
def data (v : ι → n → ℂ) (hv : ∀ i, v i ≠ 0)
    (x : ι → ℝ) (hx : ∀ i, |x i| ≤ (1 / 8 : ℝ))
    (σ : ℝ) (hσ : σ = -1 ∨ σ = 1) (S Z : Matrix n n ℂ)
    (hS : S.PosDef) (hZ : Z.PosDef)
    (htransport : Z * KSBalancedSpin.source (fun i => KSRankOne.atom (v i)) (owner x) S * Z = S)
    (hns : ∀ i, owner x i * probe v Z i < 1 / 8 - σ * x i) :
    KSEighthCompletion.Data ι where
  Γ := physicalRealGram (balancedDensity S Z) (atoms v x Z)
  T := KSFisher.gram (atoms v x Z)
  r := fun i => realTrace (atoms v x Z i)
  m := masses v x S Z
  e := fun i => x i / (8 * Real.sqrt (1 - x i ^ 2))
  b := fun i => σ - 128 * x i * probe v Z i
  Γ_posSemidef := KSFisher.physicalGram_posSemidef (balancedDensity_posDef hS hZ).posSemidef
    _ (fun i => (KSBalancedSpin.atom_posSemidef _ _ (fun j => KSRankOne.atom_posSemidef (v j)) Z i).isHermitian)
  T_isHermitian := KSFisher.gram_isHermitian _
  r_pos := KSBalancedSpin.trace_atom_pos _ _ (fun i => KSRankOne.atom_posSemidef (v i))
    (fun i => (KSRankOne.atom_eq_zero_iff (v i)).not.mpr (hv i)) (owner_pos x hx) hZ
  m_pos := KSBalancedSpin.mass_pos _ _ (fun i => KSRankOne.atom_posSemidef (v i))
    (fun i => (KSRankOne.atom_eq_zero_iff (v i)).not.mpr (hv i)) (owner_pos x hx) hS hZ
  diagonal_eq := physicalGram_diagonal v x S Z
  fisher := KSFisher.gram_fisher _
    (KSBalancedSpin.atom_posSemidef _ _ (fun i => KSRankOne.atom_posSemidef (v i)) Z)
    _ (fun i => (KSBalancedSpin.mass_pos _ _ (fun i => KSRankOne.atom_posSemidef (v i))
      (fun i => (KSRankOne.atom_eq_zero_iff (v i)).not.mpr (hv i)) (owner_pos x hx) hS hZ i).le)
    (KSBalancedSpin.trace_atom_pos _ _ (fun i => KSRankOne.atom_posSemidef (v i))
      (fun i => (KSRankOne.atom_eq_zero_iff (v i)).not.mpr (hv i)) (owner_pos x hx) hZ)
    (KSBalancedSpin.balancedDensity_eq_sum _ _ (fun i => (owner_pos x hx i).le) hZ htransport)
  mixed_bound := fun i => eighth_mixed_coefficient_bound (hx i)
  trace_bound := fun i => by
    rw [trace_atoms_sq v x hx hZ]
    exact (no_safe_probe_bounds (hx i)
      (realTrace_mul_nonneg hZ.posSemidef (KSRankOne.atom_posSemidef (v i))) hσ (hns i)).2
  force_bound := fun i => (no_safe_force_bounds (hx i)
    (realTrace_mul_nonneg hZ.posSemidef (KSRankOne.atom_posSemidef (v i))) hσ (hns i)).2
  force_ne_zero := fun i => (no_safe_force_bounds (hx i)
    (realTrace_mul_nonneg hZ.posSemidef (KSRankOne.atom_posSemidef (v i))) hσ (hns i)).1

theorem sqrt_owner (x : ι → ℝ) (hx : ∀ i, |x i| ≤ (1 / 8 : ℝ)) (i : ι) :
    Real.sqrt (owner x i) = 8 * Real.sqrt (1 - x i ^ 2) := by
  rw [owner, Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 64)]
  norm_num

def direction (x y : ι → ℝ) : ι → ℝ :=
  KSBalancedSpin.coefficientDirection (owner x) (1 / 8) y

theorem direction_eq (x y : ι → ℝ) (hx : ∀ i, |x i| ≤ (1 / 8 : ℝ)) (i : ι) :
    direction x y i = Real.sqrt (1 - x i ^ 2) * y i := by
  simp only [direction, KSBalancedSpin.coefficientDirection, sqrt_owner x hx]
  ring

def balancedCompletion (v : ι → n → ℂ) (x : ι → ℝ) (Z : Matrix n n ℂ)
    (ξ : ι → ℝ) : Matrix n n ℂ := (1 / 8 : ℝ) • KSFisher.synthesis (atoms v x Z) ξ

def transportCompletion (v : ι → n → ℂ) (x : ι → ℝ) (Z : Matrix n n ℂ)
    (ξ : ι → ℝ) : Matrix n n ℂ := KSBalancedSpin.liftTransport Z (balancedCompletion v x Z ξ)

theorem transportCompletion_isHermitian (v : ι → n → ℂ) (x : ι → ℝ)
    (Z : Matrix n n ℂ) (ξ : ι → ℝ) : (transportCompletion v x Z ξ).IsHermitian := by
  apply KSBalancedSpin.liftTransport_isHermitian
  have hY := KSFisher.synthesis_isHermitian (atoms v x Z) (fun i =>
    (KSBalancedSpin.atom_posSemidef _ (owner x) (fun j => KSRankOne.atom_posSemidef (v j)) Z i).isHermitian) ξ
  simp only [balancedCompletion, Matrix.IsHermitian, Matrix.conjTranspose_smul,
    star_trivial, hY.eq]

/-- The old legal coefficient equation cancels the actual physical center
velocity. This is an equality of matrices, not an assumed Hessian formula. -/
theorem physical_velocity_zero (v : ι → n → ℂ) (x : ι → ℝ)
    (hx : ∀ i, |x i| ≤ (1 / 8 : ℝ)) {Z : Matrix n n ℂ} (hZ : Z.PosDef)
    (σ : ℝ) (y ξ : ι → ℝ)
    (hlegal : ∀ i, (σ - 128 * x i * probe v Z i) * y i =
      ξ i - (KSFisher.gram (atoms v x Z) *ᵥ ξ) i) :
    KSBalancedSpin.physicalForce (fun i => KSRankOne.atom (v i))
        (σ • (1 : Matrix n n ℂ)) 64 x (direction x y) (probe v Z) -
      Z⁻¹ * transportCompletion v x Z ξ * Z⁻¹ +
      KSBalancedSpin.source (fun i => KSRankOne.atom (v i)) (owner x)
        (transportCompletion v x Z ξ) = 0 := by
  suffices hc : balancedCompletion v x Z ξ -
      KSFisher.prepare (atoms v x Z) (balancedCompletion v x Z ξ) =
      KSBalancedSpin.liftTransport Z (KSBalancedSpin.physicalForce
        (fun i => KSRankOne.atom (v i)) (σ • (1 : Matrix n n ℂ)) 64 x
        (direction x y) (probe v Z)) by
    simpa only [add_zero, transportCompletion] using
      KSBalancedSpin.physical_velocity_zero_of_completion (fun i => KSRankOne.atom (v i))
        (owner x) (fun i => (owner_pos x hx i).le) hZ
        (KSBalancedSpin.physicalForce (fun i => KSRankOne.atom (v i)) (σ • (1 : Matrix n n ℂ))
          64 x (direction x y) (probe v Z)) 0 (balancedCompletion v x Z ξ)
        (by simpa only [add_zero] using hc)
  rw [balancedCompletion, KSBalancedSpin.prepare_smul, ← smul_sub,
    KSFisher.defect_intertwining]
  rw [direction, KSBalancedSpin.liftTransport_physicalForce _ _
    (show (σ • (1 : Matrix n n ℂ)) * Z = Z * (σ • 1) by simp)]
  congr 1
  simp only [Matrix.smul_mul, Matrix.one_mul, KSFisher.synthesis,
    Matrix.sub_mulVec, Matrix.one_mulVec, Pi.sub_apply, Finset.smul_sum,
    smul_smul, ← Finset.sum_sub_distrib, Matrix.mulVec_diagonal]
  apply Finset.sum_congr rfl
  intro i _
  rw [← sub_smul, ← hlegal]
  congr 1
  ring

/-- Exact identification of the constructed physical curvature with the
finite comparison energy. -/
theorem physical_acceleration_eq (v : ι → n → ℂ) (hv : ∀ i, v i ≠ 0)
    (x : ι → ℝ) (hx : ∀ i, |x i| ≤ (1 / 8 : ℝ))
    (σ : ℝ) (hσ : σ = -1 ∨ σ = 1) (S Z : Matrix n n ℂ)
    (hS : S.PosDef) (hZ : Z.PosDef)
    (htransport : Z * KSBalancedSpin.source (fun i => KSRankOne.atom (v i)) (owner x) S * Z = S)
    (hns : ∀ i, owner x i * probe v Z i < 1 / 8 - σ * x i) (ξ : ι → ℝ) :
    let d := data v hv x hx σ hσ S Z hS hZ htransport hns
    realTrace (S * KSBalancedSpin.physicalAcceleration (fun i => KSRankOne.atom (v i))
      Z (transportCompletion v x Z ξ) 64 x (direction x (d.completion *ᵥ ξ)) (probe v Z)) =
        2 * d.energy ξ := by
  dsimp only
  have hh := KSBalancedSpin.normalized_acceleration_pairing
    (fun i => KSRankOne.atom (v i)) (owner x) (fun i => (owner_pos x hx i).le)
    S hZ (KSFisher.synthesis (atoms v x Z) ξ) 64 (1 / 8) (by norm_num) x
    ((data v hv x hx σ hσ S Z hS hZ htransport hns).completion *ᵥ ξ)
  change realTrace (S * KSBalancedSpin.physicalAcceleration _ Z
      (transportCompletion v x Z ξ) 64 x
      (direction x ((data v hv x hx σ hσ S Z hS hZ htransport hns).completion *ᵥ ξ))
      (probe v Z)) = _ at hh
  rw [hh]
  rw [← KSFisher.physicalGram_quadratic]
  simp only [KSEighthCompletion.Data.energy, data]
  have hmass (i : ι) : masses v x S Z i =
      (8 * Real.sqrt (1 - x i ^ 2)) * realTrace (S * KSRankOne.atom (v i)) := by
    rw [masses, KSBalancedSpin.mass_eq _ _ _ hZ, sqrt_owner x hx]
  have hs : ∀ i, Real.sqrt (1 - x i ^ 2) ≠ 0 := by
    intro i
    have hh := eighth_square_bound (hx i)
    apply (Real.sqrt_pos.mpr (by linarith : 0 < 1 - x i ^ 2)).ne'
  rw [Finset.sum_add_distrib]
  let y := (data v hv x hx σ hσ S Z hS hZ htransport hns).completion *ᵥ ξ
  change 2 * ((1 / 8 : ℝ) ^ 2 * (ξ ⬝ᵥ (physicalRealGram (balancedDensity S Z) (atoms v x Z) *ᵥ ξ)) -
    ((∑ i, realTrace (atoms v x Z i) * masses v x S Z i * y i ^ 2) +
      ∑ i, 2 * x i * realTrace (S * KSRankOne.atom (v i)) * y i *
        realTrace (atoms v x Z i * KSFisher.synthesis (atoms v x Z) ξ))) =
    2 * ((ξ ⬝ᵥ (physicalRealGram (balancedDensity S Z) (atoms v x Z) *ᵥ ξ)) / 64 +
      (∑ i, -2 * masses v x S Z i * (x i / (8 * Real.sqrt (1 - x i ^ 2))) *
        (KSFisher.gram (atoms v x Z) *ᵥ ξ) i * y i) -
      ∑ i, realTrace (atoms v x Z i) * masses v x S Z i * y i ^ 2)
  simp only [← KSFisher.gram_mulVec]
  have hsum : (∑ i, 2 * x i * realTrace (S * KSRankOne.atom (v i)) *
        ((data v hv x hx σ hσ S Z hS hZ htransport hns).completion *ᵥ ξ) i *
        (KSFisher.gram (atoms v x Z) *ᵥ ξ) i) =
      -(∑ i, -2 * masses v x S Z i * (x i / (8 * Real.sqrt (1 - x i ^ 2))) *
        (KSFisher.gram (atoms v x Z) *ᵥ ξ) i *
        ((data v hv x hx σ hσ S Z hS hZ htransport hns).completion *ᵥ ξ) i) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [hmass]
    field_simp [hs i]
    <;> ring
  change 2 * ((1 / 8 : ℝ) ^ 2 * _ - (_ + _)) = _
  rw [hsum]
  ring

/-- The two actual compressed sign blocks have one nonzero direction and
separate Hermitian transport corrections with strictly negative total curvature. -/
theorem exists_two_sign_completions [Nonempty ι]
    (v : ι → n → ℂ) (hv : ∀ i, v i ≠ 0)
    (x : ι → ℝ) (hx : ∀ i, |x i| ≤ (1 / 8 : ℝ))
    (S₁ S₂ Z₁ Z₂ : Matrix n n ℂ) (hS₁ : S₁.PosDef) (hS₂ : S₂.PosDef)
    (hZ₁ : Z₁.PosDef) (hZ₂ : Z₂.PosDef)
    (htransport₁ : Z₁ * KSBalancedSpin.source (fun i => KSRankOne.atom (v i)) (owner x) S₁ * Z₁ = S₁)
    (htransport₂ : Z₂ * KSBalancedSpin.source (fun i => KSRankOne.atom (v i)) (owner x) S₂ * Z₂ = S₂)
    (hns₁ : ∀ i, owner x i * probe v Z₁ i < 1 / 8 - x i)
    (hns₂ : ∀ i, owner x i * probe v Z₂ i < 1 / 8 + x i) :
    ∃ (h : ι → ℝ) (U₁ U₂ : Matrix n n ℂ), h ≠ 0 ∧ U₁.IsHermitian ∧ U₂.IsHermitian ∧
      (KSBalancedSpin.physicalForce (fun i => KSRankOne.atom (v i)) 1 64 x h (probe v Z₁) -
        Z₁⁻¹ * U₁ * Z₁⁻¹ + KSBalancedSpin.source (fun i => KSRankOne.atom (v i)) (owner x) U₁ = 0) ∧
      (KSBalancedSpin.physicalForce (fun i => KSRankOne.atom (v i)) (-1) 64 x h (probe v Z₂) -
        Z₂⁻¹ * U₂ * Z₂⁻¹ + KSBalancedSpin.source (fun i => KSRankOne.atom (v i)) (owner x) U₂ = 0) ∧
      realTrace (S₁ * KSBalancedSpin.physicalAcceleration (fun i => KSRankOne.atom (v i))
        Z₁ U₁ 64 x h (probe v Z₁)) +
      realTrace (S₂ * KSBalancedSpin.physicalAcceleration (fun i => KSRankOne.atom (v i))
        Z₂ U₂ 64 x h (probe v Z₂)) < 0 := by
  have hn₁ : ∀ i, owner x i * probe v Z₁ i < 1 / 8 - (1 : ℝ) * x i := by simpa using hns₁
  have hn₂ : ∀ i, owner x i * probe v Z₂ i < 1 / 8 - (-1 : ℝ) * x i := by simpa using hns₂
  let d₁ := data v hv x hx 1 (Or.inr rfl) S₁ Z₁ hS₁ hZ₁ htransport₁ hn₁
  let d₂ := data v hv x hx (-1) (Or.inl rfl) S₂ Z₂ hS₂ hZ₂ htransport₂ hn₂
  obtain ⟨y, ξ₁, ξ₂, hy, hξ₁, hξ₂, he₁, he₂⟩ :=
    KSEighthCompletion.exists_common_negative_completions d₁ d₂
  refine ⟨direction x y, transportCompletion v x Z₁ ξ₁, transportCompletion v x Z₂ ξ₂,
    ?_, transportCompletion_isHermitian v x Z₁ ξ₁,
    transportCompletion_isHermitian v x Z₂ ξ₂, ?_, ?_, ?_⟩
  · intro hz
    apply hy
    funext i
    have hh := congrFun hz i
    rw [direction_eq x y hx] at hh
    have hp : 0 < Real.sqrt (1 - x i ^ 2) := by
      apply Real.sqrt_pos.mpr
      have hi := eighth_square_bound (hx i)
      linarith
    exact (mul_eq_zero.mp hh).resolve_left hp.ne'
  · have hl := d₁.completion_legal ξ₁
    rw [hξ₁] at hl
    simpa only [one_smul] using physical_velocity_zero v x hx hZ₁ 1 y ξ₁ hl
  · have hl := d₂.completion_legal ξ₂
    rw [hξ₂] at hl
    simpa only [neg_smul, one_smul] using physical_velocity_zero v x hx hZ₂ (-1) y ξ₂ hl
  · have ha₁ := physical_acceleration_eq v hv x hx 1 (Or.inr rfl) S₁ Z₁ hS₁ hZ₁ htransport₁ hn₁ ξ₁
    have ha₂ := physical_acceleration_eq v hv x hx (-1) (Or.inl rfl) S₂ Z₂ hS₂ hZ₂ htransport₂ hn₂ ξ₂
    change realTrace (S₁ * KSBalancedSpin.physicalAcceleration _ Z₁
      (transportCompletion v x Z₁ ξ₁) 64 x (direction x (d₁.completion *ᵥ ξ₁)) (probe v Z₁)) =
        2 * d₁.energy ξ₁ at ha₁
    change realTrace (S₂ * KSBalancedSpin.physicalAcceleration _ Z₂
      (transportCompletion v x Z₂ ξ₂) 64 x (direction x (d₂.completion *ᵥ ξ₂)) (probe v Z₂)) =
        2 * d₂.energy ξ₂ at ha₂
    rw [hξ₁] at ha₁
    rw [hξ₂] at ha₂
    rw [ha₁, ha₂]
    linarith

end MatrixSpencer.KSEighthBalanced
