import AugmentedHigherRankKS.AffineFidelityRegularity
import AugmentedHigherRankKS.FourBlockSmoothness

/-! Fixed-carrier transfer of the actual relative source bounds to fidelity. -/
open Matrix MatrixSpencer HigherRankKS Filter
open scoped BigOperators Topology ContDiff MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section
set_option maxHeartbeats 2500000
namespace AugmentedHigherRankKS
open BalancedTransportJets BalancedRegularity
variable {ι n : Type*} [Fintype ι] [Fintype n] [DecidableEq n]
local instance fourFidCStar {m : Type*} [Fintype m] [DecidableEq m] :
    CStarAlgebra (Matrix m m ℂ) := {}

theorem sourceCarrier_card_le (A : ι → Matrix n n ℂ) :
    Fintype.card (SourceCarrierIndex A) ≤ Fintype.card (FourSpin n) := by
  simpa only [SourceCarrierIndex, Fintype.card_fin, finrank_euclideanSpace] using
    Submodule.finrank_le (krausSupport (fun i => spinAtom (A i)))

theorem jet_compression {m s : Type*} [Fintype m] [DecidableEq m]
    [Fintype s] [DecidableEq s] (V : Matrix m s ℂ)
    {F : ℝ → Matrix m m ℂ} (hF : ContDiffAt ℝ 3 F 0)
    {j : ℕ} (hj : (j : WithTop ℕ∞) ≤ 3) :
    jet (fun t => Vᴴ * F t * V) j = Vᴴ * jet F j * V := by
  have hh := iteratedDeriv_clm (matrixExtensionCLM Vᴴ) hF hj
  simp only [matrixExtensionCLM_apply, Matrix.conjTranspose_conjTranspose] at hh
  rw [jet, hh]
  simp only [jet, Matrix.smul_mul, Matrix.mul_smul]

theorem compression_mono {m s : Type*} [Fintype m] [DecidableEq m]
    [Fintype s] [DecidableEq s] (V : Matrix m s ℂ) {U W : Matrix m m ℂ}
    (h : U ≤ W) : Vᴴ*U*V ≤ Vᴴ*W*V := by
  apply sub_nonneg.mp
  have hh := ((sub_nonneg.mpr h).posSemidef.conjTranspose_mul_mul_same V).nonneg
  simpa only [Matrix.mul_sub, Matrix.sub_mul] using hh

/-- Once the actual source has relative Taylor bounds, compression to its fixed
carrier and balancing produce the same bound for its scalar fidelity value. -/
theorem sourceFidelity_scalarJet_le
    (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).PosSemidef)
    (k : ℕ) (hk : 1 ≤ k)
    (c : ℝ → ι → ℝ) (hc : ContDiffAt ℝ 3 c 0) (hc0 : ∀ i, 0 < c 0 i)
    (S X : selfAdjoint (Matrix (FourSpin n) (FourSpin n) ℂ))
    (hS : (S : Matrix (FourSpin n) (FourSpin n) ℂ).PosDef)
    {d L C0 : ℝ} (hd : 1 ≤ d)
    (hdn : Real.sqrt (Fintype.card (FourSpin n) : ℝ) ≤ d) (hL : 0 ≤ L)
    (hlo : -L • (S : Matrix (FourSpin n) (FourSpin n) ℂ) ≤ X)
    (hhi : (X : Matrix (FourSpin n) (FourSpin n) ℂ) ≤ L • (S : Matrix (FourSpin n) (FourSpin n) ℂ))
    (hbudget : fidelity (S : Matrix (FourSpin n) (FourSpin n) ℂ)
      (source A ((1 : ℝ)/2^k) (c 0) S) ≤ C0)
    (hsource : ∀ j : ℕ, 1 ≤ j → j ≤ 3 →
      -(L^j) • source A ((1 : ℝ)/2^k) (c 0) S ≤
        jet (fun t => source A ((1 : ℝ)/2^k) (c t) (S + t • X)) j ∧
      jet (fun t => source A ((1 : ℝ)/2^k) (c t) (S + t • X)) j ≤
        L^j • source A ((1 : ℝ)/2^k) (c 0) S) :
    ∀ j : ℕ, 1 ≤ j → j ≤ 3 →
      |scalarJet (fun t : ℝ => 2*fidelity (S + t • X : Matrix (FourSpin n) (FourSpin n) ℂ)
        (source A ((1 : ℝ)/2^k) (c t) (S + t • X))) j| ≤
        2*C0*(100*d*L)^j := by
  let β := (1 : ℝ)/2^k
  let D : ℝ → selfAdjoint (Matrix (FourSpin n) (FourSpin n) ℂ) := fun t => S+t•X
  let J : ℝ → selfAdjoint (Matrix (SourceCarrierIndex A) (SourceCarrierIndex A) ℂ) ×
      selfAdjoint (Matrix (SourceCarrierIndex A) (SourceCarrierIndex A) ℂ) :=
    fun t => jointReducedSourcePair A β (c t, D t)
  let V := sourceEmbedding A
  let S0 := Vᴴ*(S : Matrix (FourSpin n) (FourSpin n) ℂ)*V
  let X0 := Vᴴ*(X : Matrix (FourSpin n) (FourSpin n) ℂ)*V
  have hD : ContDiffAt ℝ 3 D 0 := contDiffAt_const.add (contDiffAt_id.smul contDiffAt_const)
  have hD0 : D 0 = S := by simp [D]
  have hJ : ContDiffAt ℝ 3 J 0 := by
    have hh : ContDiffAt ℝ 3 (jointReducedSourcePair A β) (c 0, D 0) := by
      rw [hD0]
      exact (contDiffAt_jointReducedSourcePair A k hk (c 0) S hS).of_le
        (WithTop.coe_le_coe.mpr (show (3 : ℕ∞) ≤ ⊤ from le_top))
    exact ContDiffAt.comp (g := jointReducedSourcePair A β)
      (f := fun t => (c t, D t)) 0 hh (hc.prodMk hD)
  have hW : ContDiffAt ℝ 3 (fun t => source A β (c t) (D t)) 0 := by
    have hh : ContDiffAt ℝ 3 (fun P : (ι → ℝ) × selfAdjoint
        (Matrix (FourSpin n) (FourSpin n) ℂ) => source A β P.1 P.2) (c 0, D 0) := by
      rw [hD0]
      exact (contDiffAt_jointSource A k hk (c 0) S hS).of_le
        (WithTop.coe_le_coe.mpr (show (3 : ℕ∞) ≤ ⊤ from le_top))
    exact ContDiffAt.comp (g := fun P : (ι → ℝ) × selfAdjoint
      (Matrix (FourSpin n) (FourSpin n) ℂ) => source A β P.1 P.2)
      (f := fun t => (c t, D t)) 0 hh (hc.prodMk hD)
  have hS0 : S0.PosDef := posDef_isometry_compression V (krausSupportEmbedding_isometry _) hS
  have hJ10 : ((J 0).1 : Matrix (SourceCarrierIndex A) (SourceCarrierIndex A) ℂ) = S0 := by
    simp only [J, D, zero_smul, add_zero, jointReducedSourcePair,
      hermitianRectangularCompressionCLM_coe, S0, V]
  have hJ20 : ((J 0).2 : Matrix (SourceCarrierIndex A) (SourceCarrierIndex A) ℂ) = compressedSource A β (c 0) S := by
    change ((jointReducedSourcePair A β (c 0, D 0)).2 :
      Matrix (SourceCarrierIndex A) (SourceCarrierIndex A) ℂ) = _
    rw [hD0]
    exact jointReducedSourcePair_snd_coe A β (c 0, S) (fun i => (hc0 i).le) hS.posSemidef
  have hJ1 : ((J 0).1 : Matrix (SourceCarrierIndex A) (SourceCarrierIndex A) ℂ).PosDef := hJ10.symm ▸ hS0
  have hJ2 : ((J 0).2 : Matrix (SourceCarrierIndex A) (SourceCarrierIndex A) ℂ).PosDef := hJ20.symm ▸
    compressedSource_posDef A hA hc0 hS k hk
  have hnear : ∀ᶠ t in 𝓝 (0 : ℝ), (D t : Matrix (FourSpin n) (FourSpin n) ℂ).PosDef ∧ ∀ i, 0 < c t i := by
    have hpos := hD.continuousAt.eventually
      (eventually_posDef_of_posDef (D 0) (by simpa [D] using hS))
    have hcs : ∀ᶠ t in 𝓝 (0 : ℝ), ∀ i, 0 < c t i := by
      apply Filter.eventually_all.mpr
      intro i
      exact ((continuous_apply i).continuousAt.comp hc.continuousAt).eventually
        (isOpen_Ioi.mem_nhds (hc0 i))
    exact hpos.and hcs
  have hleft : (fun t => ((J t).1 : Matrix (SourceCarrierIndex A) (SourceCarrierIndex A) ℂ)) = fun t => S0+t•X0 := by
    funext t
    change Vᴴ * ((S : Matrix (FourSpin n) (FourSpin n) ℂ) +
      t • (X : Matrix (FourSpin n) (FourSpin n) ℂ)) * V = S0+t•X0
    simp only [S0, X0, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul]
  have hright : (fun t => ((J t).2 : Matrix (SourceCarrierIndex A) (SourceCarrierIndex A) ℂ)) =ᶠ[𝓝 0]
      (fun t => Vᴴ * source A β (c t) (D t) * V) := by
    filter_upwards [hnear] with t ht
    exact jointReducedSourcePair_snd_coe A β (c t, D t) (fun i => (ht.2 i).le) ht.1.posSemidef
  have hjetLeft : ∀ j : ℕ, 1 ≤ j → j ≤ 3 →
      -(L^j) • ((J 0).1 : Matrix (SourceCarrierIndex A) (SourceCarrierIndex A) ℂ) ≤ jet (fun t => ((J t).1 : Matrix (SourceCarrierIndex A) (SourceCarrierIndex A) ℂ)) j ∧
      jet (fun t => ((J t).1 : Matrix (SourceCarrierIndex A) (SourceCarrierIndex A) ℂ)) j ≤ L^j • ((J 0).1 : Matrix (SourceCarrierIndex A) (SourceCarrierIndex A) ℂ) := by
    intro j hj1 hj3
    rw [hleft, hJ10]
    apply jet_affine_order hS0.posSemidef hL _ _ j hj1 hj3
    · simpa only [Matrix.mul_smul, Matrix.smul_mul, S0, X0] using
        compression_mono V hlo
    · simpa only [Matrix.mul_smul, Matrix.smul_mul, S0, X0] using
        compression_mono V hhi
  have hjetRight : ∀ j : ℕ, 1 ≤ j → j ≤ 3 →
      -(L^j) • ((J 0).2 : Matrix (SourceCarrierIndex A) (SourceCarrierIndex A) ℂ) ≤ jet (fun t => ((J t).2 : Matrix (SourceCarrierIndex A) (SourceCarrierIndex A) ℂ)) j ∧
      jet (fun t => ((J t).2 : Matrix (SourceCarrierIndex A) (SourceCarrierIndex A) ℂ)) j ≤ L^j • ((J 0).2 : Matrix (SourceCarrierIndex A) (SourceCarrierIndex A) ℂ) := by
    intro j hj1 hj3
    rw [jet_congr hright j, jet_compression V hW (by exact_mod_cast hj3), hJ20]
    exact ⟨by simpa only [compressedSource, Matrix.mul_smul, Matrix.smul_mul] using
        compression_mono V (hsource j hj1 hj3).1,
      by simpa only [compressedSource, Matrix.mul_smul, Matrix.smul_mul] using
        compression_mono V (hsource j hj1 hj3).2⟩
  have hdcarrier : Real.sqrt (Fintype.card (SourceCarrierIndex A) : ℝ) ≤ d :=
    (Real.sqrt_le_sqrt (by exact_mod_cast sourceCarrier_card_le A)).trans hdn
  have hjets := fidelity_jet_le_of_order hJ.fst hJ.snd hJ1 hJ2 hd hdcarrier hL hjetLeft hjetRight
  have he : (fun t => 2*fidelity ((J t).1 : Matrix (SourceCarrierIndex A) (SourceCarrierIndex A) ℂ) ((J t).2 : Matrix (SourceCarrierIndex A) (SourceCarrierIndex A) ℂ)) =ᶠ[𝓝 0]
      (fun t => 2*fidelity (D t : Matrix (FourSpin n) (FourSpin n) ℂ) (source A β (c t) (D t))) := by
    filter_upwards [hnear] with t ht
    exact (jointSourceFidelity_eq_reduced A hA k hk (c t, D t) ht.2 ht.1).symm
  have hval : fidelity ((J 0).1 : Matrix (SourceCarrierIndex A) (SourceCarrierIndex A) ℂ) ((J 0).2 : Matrix (SourceCarrierIndex A) (SourceCarrierIndex A) ℂ) ≤ C0 := by
    have h := he.eq_of_nhds
    have hbase : fidelity ((J 0).1 : Matrix (SourceCarrierIndex A) (SourceCarrierIndex A) ℂ) ((J 0).2 : Matrix (SourceCarrierIndex A) (SourceCarrierIndex A) ℂ) =
      fidelity (S : Matrix (FourSpin n) (FourSpin n) ℂ) (source A β (c 0) S) := by
      dsimp [D] at h
      simpa only [zero_smul, add_zero] using (mul_left_cancel₀ (by norm_num : (2:ℝ) ≠ 0) h)
    rw [hbase]
    exact hbudget
  intro j hj1 hj3
  have hj := hjets j hj1 hj3
  rw [scalarJet, he.iteratedDeriv_eq j] at hj
  exact hj.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hval (by norm_num))
    (pow_nonneg (by positivity) j))

end AugmentedHigherRankKS
