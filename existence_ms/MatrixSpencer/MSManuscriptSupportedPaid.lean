import MatrixSpencer.MSManuscriptSupportedGamma

/-!
# Uniform arithmetic paid-step size for changing numerical owner frames

A finite sum over all possible stored dimensions supplies one input-derived
curvature bound. The resulting positive scalar step is preserved through rank
changes. Its true potential decrease is proved using the actual covariance
curve and the input-derived second derivative estimate.
-/
open Matrix Set
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section
namespace MatrixSpencer.MSManuscriptSupportedPaid
open MSManuscriptSupportedOwner MSManuscriptSupportedGamma
open MSManuscriptPaidStep MSManuscriptGammaDifference MSManuscriptGammaSmoothness
variable {N d : ℕ}
local instance : CStarAlgebra (Matrix (Fin d) (Fin d) ℂ) := {}
set_option maxHeartbeats 1200000
attribute [local irreducible] ownerPotential observedOwnedGram

def curvatureBudget (P : Parameters N d) : ℝ :=
  1+∑j : Fin (N+1),MSManuscriptGammaInputBoundScaled.secondCap j d P.centerCap
    P.regularizer P.floor N

def paidSize (P : Parameters N d) : ℝ := min (P.floor/4) (P.threshold/(4*curvatureBudget P))
def paidGain (P : Parameters N d) : ℝ := 5*P.threshold*paidSize P/8

def potential (P : Parameters N d) (O : Owner N) : ℝ :=
  ownerPotential P.center P.atoms O.physical P.regularizer

theorem curvatureBudget_pos (P : Parameters N d) (hP : P.Valid) : 0<curvatureBudget P := by
  have hn : 0≤∑j : Fin (N+1),MSManuscriptGammaInputBoundScaled.secondCap j d
      P.centerCap P.regularizer P.floor N := by
    apply Finset.sum_nonneg
    intro j _
    exact MSManuscriptGammaInputBoundScaled.secondCap_nonneg
      ((norm_nonneg _).trans hP.2.2.2.2.2.2) hP.2.2.1
  unfold curvatureBudget
  linarith

theorem curvatureCap_le (P : Parameters N d) (hP : P.Valid) (k : ℕ) (hk : k≤N) :
    MSManuscriptGammaInputBoundScaled.secondCap k d P.centerCap P.regularizer P.floor N≤
      curvatureBudget P := by
  have h := Finset.single_le_sum (f:=fun j : Fin (N+1) =>
      MSManuscriptGammaInputBoundScaled.secondCap j d P.centerCap P.regularizer P.floor N)
    (fun j (_ : j∈Finset.univ) => MSManuscriptGammaInputBoundScaled.secondCap_nonneg
      ((norm_nonneg _).trans hP.2.2.2.2.2.2) hP.2.2.1)
    (Finset.mem_univ (⟨k,by omega⟩ : Fin (N+1)))
  unfold curvatureBudget
  exact h.trans (by linarith)

theorem paidSize_pos (P : Parameters N d) (hP : P.Valid) : 0<paidSize P := by
  unfold paidSize
  exact lt_min (by linarith [hP.2.2.2.1])
    (div_pos hP.2.2.2.2.2.1 (mul_pos (by norm_num) (curvatureBudget_pos P hP)))

theorem paidSize_le (P : Parameters N d) : paidSize P≤P.floor/4 := min_le_left _ _

theorem paidSize_curvature (P : Parameters N d) (hP : P.Valid) :
    curvatureBudget P*paidSize P≤P.threshold/4 := by
  have hb := curvatureBudget_pos P hP
  have h : paidSize P≤P.threshold/(4*curvatureBudget P) := min_le_right _ _
  have hm := (le_div_iff₀ (mul_pos (by norm_num : (0:ℝ)<4) hb)).mp h
  nlinarith

theorem valid_mono (O : Owner N) {a b : ℝ} (hO : O.Valid b) (hab : a≤b) : O.Valid a := by
  refine ⟨hO.1,le_trans ?_ hO.2⟩
  apply Matrix.le_iff.mpr
  rw [←sub_smul]
  exact Matrix.PosSemidef.one.smul (sub_nonneg.mpr hab)

theorem clean_potential_le (P : Parameters N d) (hP : P.Valid) (O : Owner N)
    (hO : O.Valid P.floor) : potential P (clean O P.floor)≤potential P O := by
  letI : Nonempty (Fin d) := Fin.pos_iff_nonempty.mp P.physicalDimension_pos
  exact ownerPotential_mono_covariance P.center P.atoms hP.1
    ((clean_valid O hP.2.2.2.1 hO).physical_posSemidef _ (by linarith [hP.2.2.2.1]))
    (hO.physical_posSemidef O hP.2.2.2.1.le) (clean_le O hP.2.2.2.1.le hO) P.regularizer

/-- A continuation's true Rayleigh bound implies a fixed paid decrease. All
smoothness and curvature conditions are proved from the stated input bounds. -/
theorem paid_potential_drop (P : Parameters N d) (hP : P.Valid) (O : Owner N)
    (hO : O.Valid (2*P.floor)) (hO1 : O.physical≤1) (hON : O.dim≤N)
    (u : EuclideanSpace ℝ (Fin O.dim)) (hu : ‖u‖=1)
    (hq : 7*P.threshold/8≤KSRayleighAccuracy.realRayleigh (gram P O) u) :
    potential P (paid O (paidSize P) (WithLp.ofLp u))+paidGain P≤potential P O := by
  letI : Nonempty (Fin d) := Fin.pos_iff_nonempty.mp P.physicalDimension_pos
  have hδ := hP.2.2.2.1
  have hOδ := valid_mono O hO (by linarith : P.floor≤2*P.floor)
  have hC := posDef_of_floor hδ hOδ.2
  have hA := family_isHermitian P hP O
  have hα := paidSize_pos P hP
  have hαδ : paidSize P<P.floor := (paidSize_le P).trans_lt (by linarith)
  let f := curve (P.center : Matrix (Fin d) (Fin d) ℂ) (family P O) O.matrix P.regularizer u
  have hdiff : ContDiffOn ℝ 2 f (Icc 0 (paidSize P)) :=
    query_contDiffOn _ _ hA hP.2.2.1 hδ hOδ.2 hαδ u hu
  have hder : HasDerivAt f (-KSRayleighAccuracy.realRayleigh (gram P O) u) 0 := by
    rw [KSRayleighAccuracy.realRayleigh_eq_quadratic]
    exact hasDerivAt_ownerPotential_supported_shave P.center (family P O) hA hC.posSemidef u
      (range_mem_of_posDef hC u) hP.2.2.1
  have hsecond : ∀a∈Ioo 0 (paidSize P),iteratedDeriv 2 f a≤curvatureBudget P := by
    intro a ha
    have hc := MSManuscriptGammaInputBoundScaled.query_second_le P.center (family P O) hA
      (Nat.cast_nonneg N) (MSManuscriptFrameFamily.stored_family_norm_le P.atoms hP.2.1 O hOδ)
      hP.2.2.1 hδ hP.2.2.2.2.1 hP.2.2.2.2.2.2 hOδ.2
      (MSManuscriptFrameFamily.stored_matrix_le_one O hOδ hO1) u hu
      (a:=a) ⟨ha.1,ha.2.trans_le ((paidSize_le P).trans (by linarith : P.floor/4≤P.floor/2))⟩
    exact (le_abs_self _).trans (hc.trans (curvatureCap_le P hP O.dim hON))
  have hdrop := paid_drop f hα hdiff hder hsecond hq
    ((paidSize_curvature P hP).trans (by linarith [hP.2.2.2.2.2.1] : P.threshold/4≤P.threshold/2))
  have hzero : f 0=potential P O := by
    simp only [f,curve,zero_smul,sub_zero,potential,MSManuscriptFrameFamily.stored_potential_eq]
    rfl
  have hend : f (paidSize P)=potential P (paid O (paidSize P) (WithLp.ofLp u)) := by
    simp only [potential,MSManuscriptFrameFamily.stored_potential_eq,f,curve,
      paid,cut,unitRank_of_norm_one u hu,family]
  rw [hzero,hend] at hdrop
  unfold paidGain
  linarith

end MatrixSpencer.MSManuscriptSupportedPaid
