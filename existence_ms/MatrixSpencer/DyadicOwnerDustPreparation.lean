import MatrixSpencer.DyadicPreparedOwnerResponse
import MatrixSpencer.CovarianceDust

/-!
# Finite preparation with an actual spectral floor

Compact minimization is repeated only after dust strictly decreases rank.
All removed trace is accounted for as paid trace or spectral dust.
-/

open scoped BigOperators Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
open Matrix Set
noncomputable section
namespace MatrixSpencer
namespace DyadicOwnerDustPreparation
open DyadicPreparedOwnerResponse

variable {ι n : Type*} [Fintype ι] [Fintype n] [DecidableEq ι] [DecidableEq n] [Nonempty n]
local instance ownerDustCStar : CStarAlgebra (Matrix n n ℂ) := {}
local instance ownerDustSpace : NormedSpace ℝ (selfAdjoint (Matrix n n ℂ)) := inferInstance

/-- Every field refers to the actual potential, response, covariance, and support. -/
structure DustPreparedOwner
    (H : selfAdjoint (Matrix n n ℂ)) (A : ι → Matrix n n ℂ)
    (hA : ∀ i, (A i).IsHermitian) (m : ℕ) (θ L δ : ℝ)
    (C K : Matrix ι ι ℝ) (paid dust : ℝ) : Prop where
  covariance : K ∈ Icc 0 C
  paid_nonneg : 0 ≤ paid
  dust_nonneg : 0 ≤ dust
  trace_account : realTrace (C - K) = paid + dust
  payment : regularizedOwnerPotential (H : Matrix n n ℂ) A K (dyadicTsallisRegularizer m θ) +
    (L / Real.sqrt (Fintype.card ι : ℝ)) * paid ≤ regularizedOwnerPotential (H : Matrix n n ℂ) A C (dyadicTsallisRegularizer m θ)
  dust_budget : dust ≤ δ * ((C.rank : ℝ) - (K.rank : ℝ))
  floor : ∀ u : EuclideanSpace ℝ ι,
    u ∈ LinearMap.range (Matrix.toEuclideanCLM (𝕜 := ℝ) K).toLinearMap →
    δ * ‖u‖ ^ 2 ≤ inner ℝ u (Matrix.toEuclideanCLM (𝕜 := ℝ) K u)
  cap : ∀ u : EuclideanSpace ℝ ι,
    u ∈ LinearMap.range (Matrix.toEuclideanCLM (𝕜 := ℝ) K).toLinearMap →
    WithLp.ofLp u ⬝ᵥ (DyadicOwnerFrame.observedOwnedGram H A K m θ *ᵥ WithLp.ofLp u) ≤
      (L / Real.sqrt (Fintype.card ι : ℝ)) * (WithLp.ofLp u ⬝ᵥ WithLp.ofLp u)
  response : realTrace (K * dyadicOwnerCoefficientResponse A hA K m θ H) ≤
    responseBound m θ L (Fintype.card ι : ℝ)

theorem exists_dust_prepared_owner_of_rank_bound
    (H : selfAdjoint (Matrix n n ℂ)) (A : ι → Matrix n n ℂ)
    (hA : ∀ i, (A i).IsHermitian) (hN : ∀ i, ‖A i‖ ≤ 1)
    (m : ℕ) (hm : 1 ≤ m) {θ L δ : ℝ} (hθ : 0 < θ) (hL : 0 < L) (hδ : 0 < δ)
    (hk : 0 < Fintype.card ι) (r : ℕ) :
    ∀ C : Matrix ι ι ℝ, C.PosSemidef → C ≤ 1 → C.rank ≤ r →
      ∃ K paid dust, DustPreparedOwner H A hA m θ L δ C K paid dust := by
  induction r using Nat.strong_induction_on with
  | h r ih =>
    intro C hC0 hC1 hr
    obtain ⟨M, hM, hpaid, _, hcap, hresponse⟩ :=
      exists_prepared_owner_response H A hA hN hC0 hC1 m hm hθ hL hk
    have hM0 := hM.1.posSemidef
    have hMrank : M.rank ≤ C.rank := CovarianceDust.rank_le_of_posSemidef_le hM0 hM.2
    let D := CovarianceDust.dust hM0.isHermitian δ
    have hD0 : D.PosSemidef := CovarianceDust.dust_posSemidef hM0 δ
    have hDM : D ≤ M := CovarianceDust.dust_le hM0 δ
    have hDC : D ≤ C := hDM.trans hM.2
    by_cases hd : D = M
    · refine ⟨M, realTrace (C - M), 0, ?_⟩
      refine ⟨hM, realTrace_nonneg (sub_nonneg.mpr hM.2).posSemidef,
        le_rfl, by simp, hpaid, ?_, ?_, hcap, hresponse⟩
      · exact mul_nonneg hδ.le (sub_nonneg.mpr (Nat.cast_le.mpr hMrank))
      · intro u hu
        have huD : u ∈ LinearMap.range (Matrix.toEuclideanCLM (𝕜 := ℝ) D).toLinearMap := by
          rw [hd]; exact hu
        have hf := CovarianceDust.dust_euclidean_floor hM0.isHermitian δ huD
        change δ * ‖u‖ ^ 2 ≤ inner ℝ u (Matrix.toEuclideanCLM (𝕜 := ℝ) D u) at hf
        rwa [hd] at hf
    · have hDrank : D.rank < M.rank := CovarianceDust.dust_rank_lt_of_ne hM0.isHermitian hδ hd
      obtain ⟨K, p, d, hK⟩ := ih D.rank (hDrank.trans_le (hMrank.trans hr))
        D hD0 (hDC.trans hC1) le_rfl
      refine ⟨K, realTrace (C - M) + p, realTrace (M - D) + d, ?_⟩
      refine ⟨⟨hK.covariance.1, hK.covariance.2.trans hDC⟩,
        add_nonneg (realTrace_nonneg (sub_nonneg.mpr hM.2).posSemidef) hK.paid_nonneg,
        add_nonneg (realTrace_nonneg (sub_nonneg.mpr hDM).posSemidef) hK.dust_nonneg,
        ?_, ?_, ?_, hK.floor, hK.cap, hK.response⟩
      · have he := hK.trace_account
        simp only [realTrace_sub] at he ⊢
        linarith
      · have hm := regularizedOwnerPotential_mono_covariance (H : Matrix n n ℂ) A hA hD0 hM0 hDM
          (dyadicTsallisRegularizer m θ) (continuousOn_density_dyadicTsallisRegularizer m θ)
        have hp := hK.payment
        nlinarith
      · have hb := CovarianceDust.dust_trace_loss_le_rank_drop hM0 hδ
        change realTrace (M - D) ≤ δ * (M.rank - D.rank : ℕ) at hb
        rw [Nat.cast_sub hDrank.le] at hb
        have hb' := hK.dust_budget
        have hr' : (M.rank : ℝ) ≤ C.rank := Nat.cast_le.mpr hMrank
        nlinarith

/-- An actual prepared covariance with a positive floor exists after finitely many rank losses. -/
theorem exists_dust_prepared_owner
    (H : selfAdjoint (Matrix n n ℂ)) (A : ι → Matrix n n ℂ)
    (hA : ∀ i, (A i).IsHermitian) (hN : ∀ i, ‖A i‖ ≤ 1)
    {C : Matrix ι ι ℝ} (hC0 : C.PosSemidef) (hC1 : C ≤ 1)
    (m : ℕ) (hm : 1 ≤ m) {θ L δ : ℝ} (hθ : 0 < θ) (hL : 0 < L) (hδ : 0 < δ)
    (hk : 0 < Fintype.card ι) :
    ∃ K paid dust, DustPreparedOwner H A hA m θ L δ C K paid dust :=
  exists_dust_prepared_owner_of_rank_bound H A hA hN m hm hθ hL hδ hk C.rank C hC0 hC1 le_rfl

theorem DustPreparedOwner.dust_le_card
    {H : selfAdjoint (Matrix n n ℂ)} {A : ι → Matrix n n ℂ}
    {hA : ∀ i, (A i).IsHermitian} {m : ℕ} {θ L δ paid dust : ℝ}
    {C K : Matrix ι ι ℝ} (h : DustPreparedOwner H A hA m θ L δ C K paid dust)
    (hδ : 0 ≤ δ) : dust ≤ δ * (Fintype.card ι : ℝ) := by
  have hr : (C.rank : ℝ) ≤ Fintype.card ι := Nat.cast_le.mpr C.rank_le_card_width
  have hk : (0 : ℝ) ≤ K.rank := Nat.cast_nonneg _
  exact h.dust_budget.trans (mul_le_mul_of_nonneg_left (by linarith) hδ)

/-- Paid cleaning remains bounded even when it is interleaved with dust and reoptimization. -/
theorem DustPreparedOwner.paid_le
    {H : selfAdjoint (Matrix n n ℂ)} {A : ι → Matrix n n ℂ}
    {hA : ∀ i, (A i).IsHermitian} {m : ℕ} {θ L δ paid dust : ℝ}
    {C K : Matrix ι ι ℝ} (h : DustPreparedOwner H A hA m θ L δ C K paid dust)
    (hN : ∀ i, ‖A i‖ ≤ 1) (hC0 : C.PosSemidef) (hC1 : C ≤ 1)
    (hL : 0 < L) (hk : 0 < Fintype.card ι) :
    paid ≤ 2 * (Fintype.card ι : ℝ) / L := by
  have hs : 0 < Real.sqrt (Fintype.card ι : ℝ) := Real.sqrt_pos.mpr (Nat.cast_pos.mpr hk)
  have hbase := regularizedBasePotential_le_owner (H : Matrix n n ℂ) A hA h.covariance.1.posSemidef
    (dyadicTsallisRegularizer m θ) (continuousOn_density_dyadicTsallisRegularizer m θ)
  have hupper := regularizedOwnerPotential_le_base_add (H : Matrix n n ℂ) A hA hN hC0 hC1
    (dyadicTsallisRegularizer m θ) (continuousOn_density_dyadicTsallisRegularizer m θ)
  have hp := h.payment
  have hb : (L / Real.sqrt (Fintype.card ι : ℝ)) * paid ≤
      2 * Real.sqrt (Fintype.card ι : ℝ) := by linarith
  have hm := (mul_le_mul_of_nonneg_right hb hs.le)
  have he : (L / Real.sqrt (Fintype.card ι : ℝ)) * paid *
      Real.sqrt (Fintype.card ι : ℝ) = paid * L := by field_simp
  rw [he] at hm
  have hsq := Real.sq_sqrt (Nat.cast_nonneg (Fintype.card ι) : (0 : ℝ) ≤ Fintype.card ι)
  apply (le_div_iff₀ hL).mpr
  nlinarith

end DyadicOwnerDustPreparation
end MatrixSpencer
