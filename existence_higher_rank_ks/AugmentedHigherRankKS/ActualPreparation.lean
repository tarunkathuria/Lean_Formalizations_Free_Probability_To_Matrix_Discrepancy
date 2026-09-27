import AugmentedHigherRankKS.EpochActive
import AugmentedHigherRankKS.FourBlockPotentialFirstDerivative
import AugmentedHigherRankKS.FourBlockSupportedSource
import HigherRankKS.BalancedFrames

/-! The response cap is derived from the actual optimizing density and the
feasible preparation curve, rather than assumed as a favorable covariance. -/
open Matrix MatrixSpencer HigherRankKS.BalancedFrames Set
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator ContDiff
noncomputable section
namespace AugmentedHigherRankKS
variable {ι n : Type*} [Fintype ι] [DecidableEq ι] [Fintype n] [DecidableEq n] [Nonempty n]
local instance prepCStar {j : Type*} [Fintype j] [DecidableEq j] :
    CStarAlgebra (Matrix j j ℂ) := {}

theorem budgetProbe_le_spinAtom {A : Matrix n n ℂ} (hA : A.PosSemidef) :
    augmentedCenter 0 A ≤ spinAtom A := by
  apply sub_nonneg.mp
  have hp := posSemidef_fromBlocks_diagonal
    (HigherRankKS.spinAtom_posSemidef hA)
    (posSemidef_fromBlocks_diagonal (show (0 : Matrix n n ℂ).PosSemidef from Matrix.PosSemidef.zero)
      ((smul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hA.nonneg).posSemidef))
  convert hp.nonneg using 1
  ext (i | i) (j | j) <;> cases i <;> cases j <;>
    simp [augmentedCenter, signedLift, spinAtom, HigherRankKS.spinAtom,
      Matrix.fromBlocks] <;> ring

theorem budgetProbe_trace_le {A : Matrix n n ℂ} (hA : A.PosSemidef)
    {S : Matrix (FourSpin n) (FourSpin n) ℂ} (hS : S.PosSemidef) :
    realTrace (augmentedCenter 0 A * S) ≤ realTrace (spinAtom A * S) := by
  simpa only [realTrace_mul_comm S] using realTrace_mul_mono hS (budgetProbe_le_spinAtom hA)

/-- Differentiating one exact preparation probe at the actual optimizer. -/
theorem preparation_potential_deriv
    (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).PosSemidef)
    (k : ℕ) (hk : 1 ≤ k) (θ : ℝ) (hθ : 0 < θ)
    (H : Matrix (FourSpin n) (FourSpin n) ℂ) (c : ι → ℝ) (hc : ∀ i, 0 < c i)
    (a : ℝ) (i : ι)
    (S : selfAdjoint (Matrix (FourSpin n) (FourSpin n) ℂ))
    (hS : (S : Matrix (FourSpin n) (FourSpin n) ℂ) ∈ densitySet)
    (hmax : ∀ T ∈ densitySet, objective H A ((1 : ℝ) / 2 ^ k) c θ T ≤
      objective H A ((1 : ℝ) / 2 ^ k) c θ S) :
    deriv (fun t : ℝ => potential (H + t • ((1 / a) • augmentedCenter 0 (A i)))
      A ((1 : ℝ) / 2 ^ k) (fun j => c j - if j = i then t else 0) θ) 0 =
      realTrace (augmentedCenter 0 (A i) * (S : Matrix _ _ ℂ)) / a -
        realTrace (SupportedSpin.transport A ((1 : ℝ) / 2 ^ k) c S *
          SupportedSpin.term A ((1 : ℝ) / 2 ^ k) S i) := by
  let K := (1 / a) • augmentedCenter 0 (A i)
  let cs : ℝ → ι → ℝ := fun t j => c j - if j = i then t else 0
  have hcs : ContDiffAt ℝ ∞ cs 0 := by
    apply contDiffAt_pi.mpr
    intro j
    by_cases hji : j = i
    · simp only [cs, if_pos hji]; fun_prop
    · simp only [cs, if_neg hji]; fun_prop
  have hc0 : cs 0 = c := by funext j; simp [cs]
  have hH : ContDiffAt ℝ ∞ (fun t : ℝ => H + t • K) 0 := by fun_prop
  have hd := potential_deriv_formula A hA k hk θ hθ (fun t : ℝ => H + t • K)
    cs hH hcs (by simpa [hc0] using hc) S hS (by simpa [hc0] using hmax)
  have hdc : (fun j => deriv (fun t => cs t j) 0) =
      (fun j => if j = i then (-1 : ℝ) else 0) := by
    funext j
    by_cases hji : j = i
    · simp only [cs, if_pos hji]
      exact ((hasDerivAt_id (0 : ℝ)).const_sub (c j)).deriv
    · simp [cs, hji]
  have hdcsource : compressedSource A ((1 : ℝ) / 2 ^ k)
      (fun j => if j = i then (-1 : ℝ) else 0) S =
        -SupportedSpin.term A ((1 : ℝ) / 2 ^ k) S i := by
    rw [SupportedSpin.compressedSource_eq_sum]
    simp
  rw [hdc, hdcsource, hc0] at hd
  have hHderiv : deriv (fun t : ℝ => H + t • K) 0 = K := by
    simpa using (((hasDerivAt_id (0 : ℝ)).smul_const K).const_add H).deriv
  rw [hHderiv, Matrix.mul_neg, realTrace_neg] at hd
  simpa [K, cs, SupportedSpin.transport, SupportedSpin.density, MatrixSpencer.KSSupportSymmetry.compress,
    Matrix.smul_mul, realTrace_smul, div_eq_mul_inv, mul_comm, sub_eq_add_neg] using hd

/-- The same formula packaged with differentiability, for one-sided optimality. -/
theorem preparation_potential_hasDerivAt
    (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).PosSemidef)
    (k : ℕ) (hk : 1 ≤ k) (θ : ℝ) (hθ : 0 < θ)
    (H : Matrix (FourSpin n) (FourSpin n) ℂ) (c : ι → ℝ) (hc : ∀ i, 0 < c i)
    (a : ℝ) (i : ι)
    (S : selfAdjoint (Matrix (FourSpin n) (FourSpin n) ℂ))
    (hS : (S : Matrix (FourSpin n) (FourSpin n) ℂ) ∈ densitySet)
    (hmax : ∀ T ∈ densitySet, objective H A ((1 : ℝ) / 2 ^ k) c θ T ≤
      objective H A ((1 : ℝ) / 2 ^ k) c θ S) :
    HasDerivAt (fun t : ℝ => potential (H + t • ((1 / a) • augmentedCenter 0 (A i)))
      A ((1 : ℝ) / 2 ^ k) (fun j => c j - if j = i then t else 0) θ)
      (realTrace (augmentedCenter 0 (A i) * (S : Matrix _ _ ℂ)) / a -
        realTrace (SupportedSpin.transport A ((1 : ℝ) / 2 ^ k) c S *
          SupportedSpin.term A ((1 : ℝ) / 2 ^ k) S i)) 0 := by
  have hcs : ContDiffAt ℝ ∞ (fun t : ℝ => fun j => c j - if j = i then t else 0) 0 := by
    apply contDiffAt_pi.mpr
    intro j
    by_cases hji : j = i
    · simp only [if_pos hji]; fun_prop
    · simp only [if_neg hji]; fun_prop
  have hs := contDiffAt_potential_of_positive_weights A hA k hk θ hθ
    (fun t : ℝ => H + t • ((1 / a) • augmentedCenter 0 (A i)))
    (fun t : ℝ => fun j => c j - if j = i then t else 0) 0
    (by fun_prop) hcs (by simpa using hc)
  have hd := (hs.differentiableAt (by simp)).hasDerivAt
  rw [preparation_potential_deriv A hA k hk θ hθ H c hc a i S hS hmax] at hd
  exact hd

/-- A preparation minimum forces the actual optimized probe cap. The carrier
and transport in this formula are the ones used by the response theorem. -/
theorem actual_preparation_response_cap
    (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).PosSemidef)
    (hne : ∀ i, A i ≠ 0) (k : ℕ) (hk : 1 ≤ k) (θ : ℝ) (hθ : 0 < θ)
    (H : Matrix (FourSpin n) (FourSpin n) ℂ) (c : ι → ℝ) (hc : ∀ i, 0 < c i)
    {a R : ℝ} (ha : 0 < a) (hcR : ∀ i, c i ≤ a * R)
    (S : selfAdjoint (Matrix (FourSpin n) (FourSpin n) ℂ))
    (hS : (S : Matrix (FourSpin n) (FourSpin n) ℂ) ∈ densitySet)
    (hmax : ∀ T ∈ densitySet, objective H A ((1 : ℝ) / 2 ^ k) c θ T ≤
      objective H A ((1 : ℝ) / 2 ^ k) c θ S)
    (hprep : ∀ i t, 0 ≤ t → t ≤ c i →
      potential H A ((1 : ℝ) / 2 ^ k) c θ ≤
        potential (H + t • ((1 / a) • augmentedCenter 0 (A i)))
          A ((1 : ℝ) / 2 ^ k) (fun j => c j - if j = i then t else 0) θ) :
    ∀ i, c i *
      (transportMass (SupportedSpin.term A ((1 : ℝ) / 2 ^ k) S)
          (SupportedSpin.transport A ((1 : ℝ) / 2 ^ k) c S) i /
        carrierMass (SupportedSpin.probe A) (SupportedSpin.density A S) i)^2 ≤ R / a := by
  have hβ : 0 < (1 : ℝ) / 2 ^ k := by positivity
  have hβ1 : (1 : ℝ) / 2 ^ k < 1 := by
    apply (div_lt_one (by positivity)).mpr
    exact one_lt_pow₀ (by norm_num) (by omega)
  have hSpos := maximizer_posDef H A hβ hβ1 (fun i => (hc i).le) hθ hS hmax
  have hp := carrierMass_pos (SupportedSpin.probe A) (SupportedSpin.probe_posSemidef A hA)
    (fun i => SupportedSpin.probe_ne_zero A hA i (hne i)) (SupportedSpin.density_posDef A hSpos)
  have hτ := transportMass_pos (SupportedSpin.term A ((1 : ℝ) / 2 ^ k) S)
    (SupportedSpin.term_posSemidef A _ hSpos.posSemidef)
    (fun i => SupportedSpin.term_ne_zero A hA hSpos k hk i (hne i))
    (SupportedSpin.transport_posDef A hA hc hSpos k hk)
  intro i
  have hderiv := derivative_nonneg_of_right_minimum (hc i)
    (preparation_potential_hasDerivAt A hA k hk θ hθ H c hc a i S hS hmax)
    (fun t ht htc => by simpa using hprep i t ht htc)
  apply preparation_response_cap ha (hc i).le (hcR i) (hp i) (hτ i).le _ hderiv
  rw [carrierMass, SupportedSpin.probe_pairing A hA]
  exact budgetProbe_trace_le (hA i) hSpos.posSemidef

/-- The compact epoch minimum supplies every preparation inequality needed
for the cap, after exact restriction to its positive-reserve owners. -/
theorem epoch_minimizer_preparation_cap
    (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).PosSemidef)
    (k : ℕ) (hk : 1 ≤ k) (θ : ℝ) (hθ : 0 < θ) (x₀ : ι → ℝ)
    {a R : ℝ} (ha : 0 < a) {z : EpochState ι} (hz : z ∈ epochDomain a R)
    (hmin : IsMinOn (epochPotential A ((1 : ℝ) / 2 ^ k) θ x₀) (epochDomain a R) z)
    (hzero : ∀ i, A i = 0 → reserve z i = 0)
    (S : selfAdjoint (Matrix (FourSpin n) (FourSpin n) ℂ))
    (hS : (S : Matrix (FourSpin n) (FourSpin n) ℂ) ∈ densitySet)
    (hmax : ∀ T ∈ densitySet,
      objective (augmentedCenter (discrepancy A x₀ z) (budgetCenter A x₀ z))
        (fun i : ActiveOwners z => A i) ((1 : ℝ) / 2 ^ k) (fun i => reserve z i) θ T ≤
      objective (augmentedCenter (discrepancy A x₀ z) (budgetCenter A x₀ z))
        (fun i : ActiveOwners z => A i) ((1 : ℝ) / 2 ^ k) (fun i => reserve z i) θ S) :
    ∀ i : ActiveOwners z, reserve z i *
      (transportMass (SupportedSpin.term (fun j : ActiveOwners z => A j) ((1 : ℝ) / 2 ^ k) S)
          (SupportedSpin.transport (fun j : ActiveOwners z => A j) ((1 : ℝ) / 2 ^ k)
            (fun j => reserve z j) S) i /
        carrierMass (SupportedSpin.probe (fun j : ActiveOwners z => A j))
          (SupportedSpin.density (fun j : ActiveOwners z => A j) S) i)^2 ≤ R / a := by
  have hc : ∀ i : ActiveOwners z, 0 < reserve z i :=
    fun i => (mem_positiveReserves z i).mp i.property
  have hne : ∀ i : ActiveOwners z, A i ≠ 0 := by
    intro i hi
    exact (ne_of_gt (hc i)) (hzero i hi)
  apply actual_preparation_response_cap (fun i : ActiveOwners z => A i) (fun i => hA i)
    hne k hk θ hθ _ (fun i => reserve z i) hc ha
    (fun i => (hz i).2.2.2.2.2.1) S hS hmax
  intro i t ht htc
  have hm := hmin (prepareOne_mem ha hz i.val ht htc)
  change epochPotential A ((1 : ℝ) / 2 ^ k) θ x₀ z ≤
    epochPotential A ((1 : ℝ) / 2 ^ k) θ x₀ (prepareOne a z i.val t) at hm
  rw [epochPotential_prepareOne_eq A ((1 : ℝ) / 2 ^ k) θ x₀ hz i t,
    epochPotential_eq_active A ((1 : ℝ) / 2 ^ k) θ x₀ hz] at hm
  exact hm

end AugmentedHigherRankKS
