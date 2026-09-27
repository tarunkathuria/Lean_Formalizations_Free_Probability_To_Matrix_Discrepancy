import AugmentedHigherRankKS.DyadicSDPLift
import AugmentedHigherRankKS.FourBlockOptimizer
import MatrixSpencer.KSFullManuscriptSDPIdentity

/-! Exact semidefinite materialization of the four-block value query. -/
open Matrix MatrixSpencer HigherRankKS
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section
namespace AugmentedHigherRankKS.FourBlockSDP
variable {ι n : Type*} [Fintype ι] [Fintype n] [DecidableEq n]
local instance fourSDPCStar {j : Type*} [Fintype j] [DecidableEq j] :
    CStarAlgebra (Matrix j j ℂ) := {}

abbrev Lift (ι n : Type*) := ι → ℕ → Matrix n n ℂ

def ownerCarrier (A : Matrix n n ℂ) (S : Matrix (FourSpin n) (FourSpin n) ℂ) :=
  HigherRankKS.carrier A (HigherRankKS.marginal S)

def output (A Y : Matrix n n ℂ) : Matrix (FourSpin n) (FourSpin n) ℂ :=
  spinDuplicateCLM (spinDuplicateCLM (CFC.sqrt A * Y * CFC.sqrt A))

def liftedSource (A : ι → Matrix n n ℂ) (c : ι → ℝ) (k : ℕ) (Y : Lift ι n) :
    Matrix (FourSpin n) (FourSpin n) ℂ := ∑ i, c i • output (A i) (Y i k)

def PowerFeasible (A : ι → Matrix n n ℂ) (k : ℕ)
    (S : Matrix (FourSpin n) (FourSpin n) ℂ) (Y : Lift ι n) : Prop :=
  ∀ i, DyadicSDP.Feasible (ownerCarrier (A i) S) (realTrace (ownerCarrier (A i) S)) k (Y i)

def Feasible (A : ι → Matrix n n ℂ) (k : ℕ) (c : ι → ℝ)
    (S U X : Matrix (FourSpin n) (FourSpin n) ℂ) (Y : Lift ι n) : Prop :=
  PowerFeasible A k S Y ∧
    KSFullManuscriptSDPIdentity.Feasible (fun _ => liftedSource A c k Y) 0 S U X

abbrev value := @KSFullManuscriptSDPIdentity.value (FourSpin n) inferInstance

theorem duplicate_mono {j : Type*} [Fintype j] [DecidableEq j]
    {M N : Matrix j j ℂ} (h : M ≤ N) : spinDuplicateCLM M ≤ spinDuplicateCLM N := by
  apply Matrix.le_iff.mpr
  have hd := posSemidef_fromBlocks_diagonal (Matrix.le_iff.mp h) (Matrix.le_iff.mp h)
  simpa only [← map_sub, spinDuplicateCLM] using hd

theorem output_posSemidef (A : Matrix n n ℂ) {Y : Matrix n n ℂ}
    (hY : Y.PosSemidef) : (output A Y).PosSemidef := by
  have hp : (CFC.sqrt A * Y * CFC.sqrt A).PosSemidef := by
    simpa only [(CFC.sqrt_nonneg A).posSemidef.isHermitian.eq] using
      hY.conjTranspose_mul_mul_same (CFC.sqrt A)
  exact posSemidef_fromBlocks_diagonal (posSemidef_fromBlocks_diagonal hp hp)
    (posSemidef_fromBlocks_diagonal hp hp)

theorem output_mono (A : Matrix n n ℂ) {Y Z : Matrix n n ℂ} (h : Y ≤ Z) :
    output A Y ≤ output A Z := by
  exact duplicate_mono (duplicate_mono
    ((CFC.sqrt_nonneg A).posSemidef.isHermitian.isSelfAdjoint.conjugate_le_conjugate h))

theorem ownerCarrier_posSemidef (A : Matrix n n ℂ)
    {S : Matrix (FourSpin n) (FourSpin n) ℂ} (hS : S.PosSemidef) :
    (ownerCarrier A S).PosSemidef :=
  HigherRankKS.carrier_posSemidef A (HigherRankKS.marginal_posSemidef hS)

theorem liftedSource_posSemidef (A : ι → Matrix n n ℂ) {c : ι → ℝ}
    (hc : ∀ i, 0 ≤ c i) (k : ℕ) {Y : Lift ι n}
    (hY : ∀ i, (Y i k).PosSemidef) : (liftedSource A c k Y).PosSemidef := by
  apply Matrix.nonneg_iff_posSemidef.mp
  exact Finset.sum_nonneg (fun i _ => smul_nonneg (hc i) (output_posSemidef (A i) (hY i)).nonneg)

theorem liftedSource_le_source (A : ι → Matrix n n ℂ) {c : ι → ℝ}
    (hc : ∀ i, 0 ≤ c i) (k : ℕ) {S : Matrix (FourSpin n) (FourSpin n) ℂ}
    (hS : S.PosSemidef) {Y : Lift ι n} (hY : PowerFeasible A k S Y) :
    liftedSource A c k Y ≤ source A ((1 : ℝ) / 2 ^ k) c S := by
  apply Finset.sum_le_sum
  intro i _
  apply smul_le_smul_of_nonneg_left _ (hc i)
  exact output_mono (A i)
    (DyadicSDP.feasible_le_carrierPower (ownerCarrier_posSemidef (A i) hS) (hY i))

/-- Every feasible lifted point is below the actual nonlinear objective. -/
theorem feasible_value_le {A : ι → Matrix n n ℂ} {k : ℕ} {c : ι → ℝ}
    (hc : ∀ i, 0 ≤ c i) {θ : ℝ} (hθ : 0 ≤ θ)
    {H S U X : Matrix (FourSpin n) (FourSpin n) ℂ} {Y : Lift ι n}
    (h : Feasible A k c S U X Y) :
    value H θ S U X ≤ objective H A ((1 : ℝ) / 2 ^ k) c θ S := by
  have hS := KSFullManuscriptSDPIdentity.feasible_density h.2
  have hL := liftedSource_posSemidef A hc k (fun i => (h.1 i).2.1 k le_rfl)
  have hsource := source_posSemidef A ((1 : ℝ) / 2 ^ k) hc hS.1
  have hf := fidelity_mono hS.1 hS.1 hL hsource le_rfl
    (liftedSource_le_source A hc k hS.1 h.1)
  have hb := KSFullManuscriptSDPIdentity.feasible_value_le (H := H) hθ h.2
  simp only [KSFullManuscriptSDPIdentity.objective, zero_smul, add_zero] at hb
  unfold value objective
  linarith

def canonicalLift (A : ι → Matrix n n ℂ)
    (S : Matrix (FourSpin n) (FourSpin n) ℂ) : Lift ι n :=
  fun i => DyadicSDP.target (realTrace (ownerCarrier (A i) S)) (ownerCarrier (A i) S)

theorem canonicalLift_feasible (A : ι → Matrix n n ℂ) (k : ℕ)
    {S : Matrix (FourSpin n) (FourSpin n) ℂ} (hS : S.PosSemidef) :
    PowerFeasible A k S (canonicalLift A S) := by
  intro i
  exact DyadicSDP.target_feasible (realTrace_nonneg (ownerCarrier_posSemidef (A i) hS))
    (ownerCarrier_posSemidef (A i) hS) k

theorem canonicalLift_source (A : ι → Matrix n n ℂ) (c : ι → ℝ) (k : ℕ)
    (S : Matrix (FourSpin n) (FourSpin n) ℂ) :
    liftedSource A c k (canonicalLift A S) = source A ((1 : ℝ) / 2 ^ k) c S := rfl

/-- Explicit attainment at a faithful density. Singular input owners and
singular total sources are allowed. -/
theorem fixed_density_attainment (A : ι → Matrix n n ℂ) (k : ℕ)
    {c : ι → ℝ} (hc : ∀ i, 0 ≤ c i) (θ : ℝ)
    (H : Matrix (FourSpin n) (FourSpin n) ℂ)
    {S : Matrix (FourSpin n) (FourSpin n) ℂ} (hS : S ∈ densitySet)
    (hSpos : S.PosDef) :
    ∃ U X Y, Feasible A k c S U X Y ∧
      value H θ S U X = objective H A ((1 : ℝ) / 2 ^ k) c θ S := by
  obtain ⟨X, hX, ht⟩ := KSFullManuscriptFidelityBlock.exists_attaining_block hSpos
    (source_posSemidef A ((1 : ℝ) / 2 ^ k) hc hS.1)
  refine ⟨CFC.sqrt S, X, canonicalLift A S, ⟨canonicalLift_feasible A k hS.1, ?_⟩, ?_⟩
  · refine ⟨hS.2, (CFC.sqrt_nonneg S).posSemidef, ?_,
      KSFullManuscriptSDPIdentity.regularizer_block hS.1⟩
    simpa only [zero_smul, add_zero, canonicalLift_source] using hX
  · simp only [value, KSFullManuscriptSDPIdentity.value, objective, ht]

/-- The concrete lifted SDP attains precisely the four-block potential.
Only the dyadic exponent, nonnegative reserves, and positive smoothing
parameter are required; no oracle is used in this representation theorem. -/
theorem SDP_exact [Nonempty n]
    (H : Matrix (FourSpin n) (FourSpin n) ℂ) (A : ι → Matrix n n ℂ)
    (k : ℕ) (hk : 1 ≤ k) {c : ι → ℝ} (hc : ∀ i, 0 ≤ c i)
    {θ : ℝ} (hθ : 0 < θ) :
    ∃ S U X Y, Feasible A k c S U X Y ∧
      value H θ S U X = potential H A ((1 : ℝ) / 2 ^ k) c θ ∧
      ∀ S' U' X' Y', Feasible A k c S' U' X' Y' →
        value H θ S' U' X' ≤ value H θ S U X := by
  have hβ : 0 < (1 : ℝ) / 2 ^ k := by positivity
  have hβ1 : (1 : ℝ) / 2 ^ k < 1 := by
    apply (div_lt_one (by positivity)).mpr
    exact one_lt_pow₀ (by norm_num) (by omega)
  obtain ⟨S, hS, hmax⟩ := exists_optimizer H A hβ.le hβ1.le hc θ
  have hp := maximizer_posDef H A hβ hβ1 hc hθ hS hmax
  obtain ⟨U, X, Y, hf, hv⟩ := fixed_density_attainment A k hc θ H hS hp
  have he := potential_eq_of_optimizer H A ((1 : ℝ) / 2 ^ k) c θ hS hmax
  refine ⟨S, U, X, Y, hf, hv.trans he.symm, ?_⟩
  intro S' U' X' Y' hh
  rw [hv]
  exact (feasible_value_le hc hθ.le hh).trans
    (hmax S' (KSFullManuscriptSDPIdentity.feasible_density hh.2))


end AugmentedHigherRankKS.FourBlockSDP
