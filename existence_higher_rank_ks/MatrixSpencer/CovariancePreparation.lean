import MatrixSpencer.SupportShaving
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Topology.Order.Compact

/-!
# Covariance preparation by compact minimization

All matrices in this file use the real positive-semidefinite order. Compactness
uses the finite product topology on their entries and introduces no norm choice.
-/

open scoped BigOperators MatrixOrder Topology
open Matrix Set Filter

namespace MatrixSpencer

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
theorem isClosed_posSemidef_real :
    IsClosed {A : Matrix ι ι ℝ | A.PosSemidef} := by
  have hh : IsClosed {A : Matrix ι ι ℝ | A.IsHermitian} :=
    isClosed_eq (by fun_prop) continuous_id
  have hq (x : ι → ℝ) : IsClosed {A : Matrix ι ι ℝ | 0 ≤ x ⬝ᵥ (A *ᵥ x)} := by
    apply isClosed_le continuous_const
    simp only [dotProduct, Matrix.mulVec]
    fun_prop
  simpa only [Matrix.PosSemidef, star_trivial, Set.setOf_and, Set.setOf_forall] using
    hh.inter (isClosed_iInter hq)

/-- A positive real matrix has each off-diagonal entry bounded by its two diagonal entries. -/
theorem posSemidef_abs_entry_le_diag {A : Matrix ι ι ℝ} (hA : A.PosSemidef) (i j : ι) :
    |A i j| ≤ (A i i + A j j) / 2 := by
  have hp := hA.2 (Pi.single i 1 + Pi.single j 1)
  have hm := hA.2 (Pi.single i 1 - Pi.single j 1)
  have hs : A j i = A i j := by simpa only [star_trivial] using (hA.isHermitian.apply j i).symm
  simp only [star_trivial, Matrix.mulVec_add, Matrix.mulVec_sub, dotProduct_add,
    dotProduct_sub, add_dotProduct, sub_dotProduct, Matrix.mulVec_single_one,
    single_dotProduct, one_mul, Matrix.col_apply, hs] at hp hm
  exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem covarianceInterval_entry_bound (C : Matrix ι ι ℝ)
    {K : Matrix ι ι ℝ} (hK : K ∈ Icc 0 C) (i j : ι) :
    |K i j| ≤ ∑ l, |C l l| := by
  have hdiag (l : ι) : K l l ≤ C l l := by
    have h := (Matrix.le_iff.mp hK.2).2 (Pi.single l 1)
    simpa only [star_trivial, Matrix.mulVec_single_one, single_dotProduct, one_mul, Matrix.col_apply,
      Matrix.sub_apply, sub_nonneg] using h
  have hb (l : ι) : C l l ≤ ∑ k, |C k k| :=
    (le_abs_self _).trans (Finset.single_le_sum (fun k _ => abs_nonneg (C k k))
      (Finset.mem_univ l))
  have he := posSemidef_abs_entry_le_diag hK.1.posSemidef i j
  have hi := (hdiag i).trans (hb i)
  have hj := (hdiag j).trans (hb j)
  linarith

/-- A closed Loewner interval is compact, including when its upper endpoint is singular. -/
theorem isCompact_covarianceInterval (C : Matrix ι ι ℝ) : IsCompact (Icc 0 C) := by
  have hc : IsClosed (Icc (0 : Matrix ι ι ℝ) C) := by
    have hc2 : IsClosed {K : Matrix ι ι ℝ | (C - K).PosSemidef} :=
      isClosed_posSemidef_real.preimage (continuous_const.sub continuous_id)
    have h := isClosed_posSemidef_real.inter hc2
    convert h using 1
    ext K
    simp only [Set.mem_Icc, Set.mem_inter_iff, Set.mem_setOf_eq, Matrix.le_iff, sub_zero]
  let r : ℝ := ∑ l, |C l l|
  apply (isCompact_Icc : IsCompact (Icc (-r) r)).matrix.of_isClosed_subset hc
  intro K hK i j
  exact abs_le.mp (covarianceInterval_entry_bound C hK i j)

/-- Objective after paying for the owner's removed trace. -/
noncomputable def covarianceObjective (C : Matrix ι ι ℝ) (f : Matrix ι ι ℝ → ℝ) (t : ℝ)
    (K : Matrix ι ι ℝ) : ℝ := f K + t * realTrace (C - K)

omit [DecidableEq ι] in
theorem continuous_covarianceObjective (C : Matrix ι ι ℝ)
    {f : Matrix ι ι ℝ → ℝ} (hf : Continuous f) (t : ℝ) :
    Continuous (covarianceObjective C f t) := by
  unfold covarianceObjective realTrace Matrix.trace
  fun_prop

omit [DecidableEq ι] in
theorem continuousOn_covarianceObjective (C : Matrix ι ι ℝ)
    {f : Matrix ι ι ℝ → ℝ} (hf : ContinuousOn f (Icc 0 C)) (t : ℝ) :
    ContinuousOn (covarianceObjective C f t) (Icc 0 C) := by
  apply hf.add
  apply Continuous.continuousOn
  unfold realTrace Matrix.trace
  fun_prop

/-- Continuity on the feasible interval alone suffices for covariance preparation. -/
theorem exists_covariance_minimizer_of_continuousOn {C : Matrix ι ι ℝ}
    (hC : C.PosSemidef) {f : Matrix ι ι ℝ → ℝ} (hf : ContinuousOn f (Icc 0 C)) (t : ℝ) :
    ∃ K ∈ Icc 0 C, IsMinOn (covarianceObjective C f t) (Icc 0 C) K ∧
      covarianceObjective C f t K ≤ f C := by
  obtain ⟨K, hK, hm⟩ := (isCompact_covarianceInterval C).exists_isMinOn
    ⟨C, hC.nonneg, le_rfl⟩ (continuousOn_covarianceObjective C hf t)
  refine ⟨K, hK, hm, ?_⟩
  have h : covarianceObjective C f t K ≤ covarianceObjective C f t C :=
    hm (show C ∈ Icc 0 C from ⟨hC.nonneg, le_rfl⟩)
  simpa only [covarianceObjective, sub_self, realTrace_zero, mul_zero, add_zero] using h

/-- Compact covariance preparation attains a minimum and pays no more than `f C`. -/
theorem exists_covariance_minimizer {C : Matrix ι ι ℝ} (hC : C.PosSemidef)
    {f : Matrix ι ι ℝ → ℝ} (hf : Continuous f) (t : ℝ) :
    ∃ K ∈ Icc 0 C, IsMinOn (covarianceObjective C f t) (Icc 0 C) K ∧
      covarianceObjective C f t K ≤ f C := by
  exact exists_covariance_minimizer_of_continuousOn hC hf.continuousOn t

omit [DecidableEq ι] in
theorem realTrace_rankOne_eq_norm_sq (u : EuclideanSpace ℝ ι) :
    realTrace (realRankOne (WithLp.ofLp u)) = ‖u‖ ^ 2 := by
  change (∑ i, u i * u i) = ‖u‖ ^ 2
  rw [EuclideanSpace.norm_sq_eq]
  simp only [Real.norm_eq_abs, ← pow_two, sq_abs]

omit [Fintype ι] [DecidableEq ι] in
/-- The derivative at a right-hand local minimum is nonnegative. -/
theorem hasDerivAt_nonneg_of_right_min {g : ℝ → ℝ} {g' δ : ℝ}
    (hg : HasDerivAt g g' 0) (hδ : 0 < δ)
    (hmin : ∀ h : ℝ, 0 ≤ h → h < δ → g 0 ≤ g h) : 0 ≤ g' := by
  apply ge_of_tendsto hg.tendsto_slope_zero_right
  have hsmall : ∀ᶠ h : ℝ in 𝓝[>] 0, h < δ :=
    (eventually_lt_nhds hδ).filter_mono nhdsWithin_le_nhds
  filter_upwards [self_mem_nhdsWithin, hsmall] with h hh0 hhδ
  simpa only [zero_add, smul_eq_mul] using
    mul_nonneg (inv_nonneg.mpr (le_of_lt hh0)) (sub_nonneg.mpr (hmin h hh0.le hhδ))

omit [DecidableEq ι] in
/-- Along shaving, the trace penalty has the exact positive derivative `t Tr R`. -/
theorem hasDerivAt_covarianceObjective_shaving (C K R : Matrix ι ι ℝ)
    (f : Matrix ι ι ℝ → ℝ) (t q : ℝ)
    (hf : HasDerivAt (fun h : ℝ => f (K - h • R)) (-q) 0) :
    HasDerivAt (fun h : ℝ => covarianceObjective C f t (K - h • R))
      (-q + t * realTrace R) 0 := by
  have hd := (hf.add_const (t * realTrace (C - K))).add
    ((hasDerivAt_id (0 : ℝ)).mul_const (t * realTrace R))
  convert hd using 1
  · ext h
    have heq : C - (K - h • R) = (C - K) + h • R := by module
    simp only [covarianceObjective, heq, realTrace_add, realTrace_smul, Pi.add_apply, id_eq]
    ring
  · ring

/-- A minimizer's supported rank-one derivatives obey the paid trace cap. -/
theorem covariance_minimizer_directional_cap {C K : Matrix ι ι ℝ}
    {f : Matrix ι ι ℝ → ℝ} {t : ℝ}
    (hK : K ∈ Icc 0 C)
    (hm : IsMinOn (covarianceObjective C f t) (Icc 0 C) K)
    {u : EuclideanSpace ℝ ι}
    (hu : u ∈ LinearMap.range
      (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℝ) K).toLinearMap)
    {q : ℝ}
    (hf : HasDerivAt (fun h : ℝ => f (K - h • realRankOne (WithLp.ofLp u))) (-q) 0) :
    q ≤ t * ‖u‖ ^ 2 := by
  obtain ⟨δ, hd, hδ⟩ := exists_pos_smul_rankOne_le_of_mem_range hK.1.posSemidef hu
  have hderiv := hasDerivAt_covarianceObjective_shaving C K
    (realRankOne (WithLp.ofLp u)) f t q hf
  have hnonneg : 0 ≤ -q + t * realTrace (realRankOne (WithLp.ofLp u)) := by
    apply hasDerivAt_nonneg_of_right_min hderiv (show 0 < δ / 2 by positivity)
    intro h hh0 hhδ
    have hshave := (shaving_posSemidef_and_range hK.1.posSemidef
      (realRankOne_posSemidef _) hδ hh0 hhδ.le).1
    have hupper : K - h • realRankOne (WithLp.ofLp u) ≤ C :=
      (sub_le_self K ((realRankOne_posSemidef _).smul hh0).nonneg).trans hK.2
    have h := hm (show K - h • realRankOne (WithLp.ofLp u) ∈ Icc 0 C from
      ⟨hshave.nonneg, hupper⟩)
    simpa only [zero_smul, sub_zero] using h
  rw [realTrace_rankOne_eq_norm_sq] at hnonneg
  linarith

/-- The derivative matrix is capped on the minimizer's actual range. -/
theorem covariance_minimizer_matrix_cap {C K Γ : Matrix ι ι ℝ}
    {f : Matrix ι ι ℝ → ℝ} {t : ℝ}
    (hK : K ∈ Icc 0 C)
    (hm : IsMinOn (covarianceObjective C f t) (Icc 0 C) K)
    (hderiv : ∀ u : EuclideanSpace ℝ ι,
      u ∈ LinearMap.range (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℝ) K).toLinearMap →
      HasDerivAt (fun h : ℝ => f (K - h • realRankOne (WithLp.ofLp u)))
        (-(WithLp.ofLp u ⬝ᵥ (Γ *ᵥ WithLp.ofLp u))) 0) :
    ∀ u : EuclideanSpace ℝ ι,
      u ∈ LinearMap.range (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℝ) K).toLinearMap →
      WithLp.ofLp u ⬝ᵥ (Γ *ᵥ WithLp.ofLp u) ≤ t * ‖u‖ ^ 2 := by
  intro u hu
  exact covariance_minimizer_directional_cap hK hm hu (hderiv u hu)

end MatrixSpencer
