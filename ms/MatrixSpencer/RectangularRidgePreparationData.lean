import MatrixSpencer.RectangularRidgeStoredGamma
import MatrixSpencer.RectangularRidgeOwnerBounds
import MatrixSpencer.MSManuscriptSupportedOwner
import MatrixSpencer.MSManuscriptPreparationRun

/-! Concrete owner cleanup and paid cuts for the ridged rectangular potential.
The numerical report interface asks only for its matrix error and symmetry;
the true favorable direction and potential decrease are proved internally.
Finite-accuracy value-solver reports are instantiated separately. -/

open Matrix
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section
namespace MatrixSpencer.RectangularRidgePreparationData
open MSManuscriptSupportedOwner RectangularRidgePrimitiveParameters
open RectangularRidgeNumericalOptimizerFloor
variable {N d : ℕ} [Nonempty (Fin d)]
local instance ridgePreparationDataCStar : CStarAlgebra (Matrix (Fin d) (Fin d) ℂ) := {}
local instance ridgePreparationDataSpace : NormedSpace ℝ (selfAdjoint (Matrix (Fin d) (Fin d) ℂ)) := inferInstance
set_option maxHeartbeats 600000
attribute [local irreducible] RectangularRidgePotential.optimizer
  RectangularRidgeCovarianceCalculus.ownerPotential regularizedOwnerPotential

structure Parameters (N d : ℕ) where
  center : selfAdjoint (Matrix (Fin d) (Fin d) ℂ)
  atoms : Fin N → Matrix (Fin d) (Fin d) ℂ
  threshold : ℝ
  count_pos : 1 ≤ N
  rectangular : N ≤ d

def Parameters.Valid (P : Parameters N d) : Prop :=
  (∀ i, (P.atoms i).IsHermitian) ∧ (∀ i, ‖P.atoms i‖ ≤ 1) ∧
  ‖(P.center : Matrix (Fin d) (Fin d) ℂ)‖ ≤ N ∧ 1/size d N ≤ P.threshold

def floor : ℝ := 1/8192
def paidSize (_P : Parameters N d) : ℝ := RectangularRidgeNumericalParameters.paidStep (size d N)
def paidGain (P : Parameters N d) : ℝ := 5*P.threshold*paidSize P/8
def depth (P : Parameters N d) : ℕ := RectangularRidgeTuning.depth N d P.count_pos
def theta (P : Parameters N d) : ℝ := weight N d P.count_pos
def ridge (_P : Parameters N d) : ℝ := 1/(d : ℝ)

def potential (P : Parameters N d) (O : Owner N) : ℝ :=
  RectangularRidgeCovarianceCalculus.ownerPotential (depth P) P.center P.atoms O.physical (theta P) (ridge P)

def gram (P : Parameters N d) (O : Owner N) : Matrix (Fin O.dim) (Fin O.dim) ℝ :=
  RectangularRidgePaidQueries.gram P.center (mixFamily P.atoms O.frame) O.matrix (depth P) (theta P) (ridge P)

def State (O : Owner N) : Prop := O.Valid floor ∧ O.physical≤1 ∧ O.dim≤N
def Cap (P : Parameters N d) (O : Owner N) : Prop :=
  gram P O ≤ P.threshold • (1 : Matrix (Fin O.dim) (Fin O.dim) ℝ)

structure Report (P : Parameters N d) where
  value : (O : Owner N) → Matrix (Fin O.dim) (Fin O.dim) ℝ
  symmetric : ∀ O, (value O).IsSymm
  accuracy : ∀ O, State O →
    ‖Matrix.toEuclideanCLM (𝕜:=ℝ) (gram P O-value O)‖≤P.threshold/64

def direction (P : Parameters N d) (R : Report P) (O : Owner N) :
    Option (EuclideanSpace ℝ (Fin O.dim)) :=
  if hk : 0<O.dim then
    if MSManuscriptGammaTop.stop (R.value O) P.threshold hk then none
    else some (MSManuscriptGammaTop.vector (R.value O) P.threshold hk)
  else none

theorem size_one_le (P : Parameters N d) : 1 ≤ size d N := by
  have hn : (1:ℝ)≤N := by exact_mod_cast P.count_pos
  have hd : (1:ℝ)≤d := by exact_mod_cast (P.count_pos.trans P.rectangular)
  dsimp [size]
  linarith

theorem threshold_pos (P : Parameters N d) (hP : P.Valid) : 0<P.threshold :=
  lt_of_lt_of_le (one_div_pos.mpr (by linarith [size_one_le P])) hP.2.2.2

theorem paidSize_pos (P : Parameters N d) : 0<paidSize P :=
  RectangularRidgeNumericalParameters.small_pos (by linarith [size_one_le P]) 320 62

theorem paidSize_le (P : Parameters N d) : paidSize P ≤ floor := by
  have h := RectangularRidgeNumericalParameters.paidStep_le_floor (size_one_le P)
  change paidSize P ≤ (1/8192:ℝ)/2 at h
  unfold floor
  linarith

theorem valid_mono (O : Owner N) {a b : ℝ} (hO : O.Valid b) (hab : a≤b) : O.Valid a := by
  refine ⟨hO.1,le_trans ?_ hO.2⟩
  apply Matrix.le_iff.mpr
  rw [←sub_smul]
  exact Matrix.PosSemidef.one.smul (sub_nonneg.mpr hab)

theorem clean_state (O : Owner N) (hO : State O) :
    (clean O floor).Valid (2*floor) ∧ (clean O floor).physical≤1 ∧ (clean O floor).dim≤N :=
  ⟨clean_valid O (by norm_num [floor]) hO.1,
    (clean_le O (by norm_num [floor]) hO.1).trans hO.2.1,
    (clean_dim_le O floor).trans hO.2.2⟩

theorem gram_isSymm (P : Parameters N d) (hP : P.Valid) (O : Owner N) : (gram P O).IsSymm := by
  have hd : (0:ℝ)<d := by exact_mod_cast (show 0<d from lt_of_lt_of_le (by omega) (P.count_pos.trans P.rectangular))
  exact RectangularRidgeStoredGamma.gram_isSymm P.center (mixFamily P.atoms O.frame)
    (mixFamily_isHermitian P.atoms O.frame hP.1) O.matrix (depth P)
    (RectangularRidgeTuning.depth_positive N d P.count_pos) (theta P) (ridge P)
    (weight_positive P.count_pos P.rectangular) (by dsimp [ridge]; positivity)

theorem direction_none (P : Parameters N d) (hP : P.Valid) (R : Report P) (O : Owner N)
    (hO : State O) (ho : direction P R O=none) : Cap P O := by
  unfold direction at ho
  split at ho
  · rename_i hk
    split_ifs at ho with hs
    · exact MSManuscriptGammaTop.stop_sound _ _ (gram_isSymm P hP O) (R.symmetric O)
        (threshold_pos P hP) hk (R.accuracy O hO) hs
  · rename_i hk
    haveI : IsEmpty (Fin O.dim) := ⟨fun j => by have hj := j.isLt; omega⟩
    exact le_of_eq (Subsingleton.elim _ _)

theorem direction_some (P : Parameters N d) (hP : P.Valid) (R : Report P) (O : Owner N)
    (hO : State O) {u : EuclideanSpace ℝ (Fin O.dim)} (ho : direction P R O=some u) :
    ‖u‖=1 ∧ 7*P.threshold/8<KSRayleighAccuracy.realRayleigh (gram P O) u := by
  unfold direction at ho
  split at ho
  · rename_i hk
    split_ifs at ho with hs
    rw [←Option.some.inj ho]
    exact MSManuscriptGammaTop.continue_sound _ _ (threshold_pos P hP) hk
      (R.accuracy O hO) (Bool.eq_false_iff.mpr hs)
  · simp at ho

theorem stored_potential_eq (P : Parameters N d) (O : Owner N) :
    potential P O = RectangularRidgeCovarianceCalculus.ownerPotential (depth P) P.center
      (mixFamily P.atoms O.frame) O.matrix (theta P) (ridge P) := by
  unfold potential RectangularRidgeCovarianceCalculus.ownerPotential regularizedOwnerPotential
  congr 2
  funext S
  unfold regularizedOwnerObjective
  rw [←covarianceSource_rectangular_mixing]
  rfl

theorem clean_potential_le (P : Parameters N d) (hP : P.Valid) (O : Owner N)
    (hO : O.Valid floor) : potential P (clean O floor)≤potential P O := by
  exact RectangularRidgeOwnerBounds.mono_covariance (depth P) P.center P.atoms hP.1
    ((clean_valid O (by norm_num [floor]) hO).physical_posSemidef _ (by norm_num [floor]))
    (hO.physical_posSemidef O (by norm_num [floor]))
    (clean_le O (by norm_num [floor]) hO) (theta P) (ridge P)

theorem paid_potential_drop (P : Parameters N d) (hP : P.Valid) (O : Owner N)
    (hO : O.Valid (2*floor)) (hO1 : O.physical≤1) (hON : O.dim≤N)
    (u : EuclideanSpace ℝ (Fin O.dim)) (hu : ‖u‖=1)
    (hq : 7*P.threshold/8≤KSRayleighAccuracy.realRayleigh (gram P O) u) :
    potential P (paid O (paidSize P) (WithLp.ofLp u))+paidGain P≤potential P O := by
  have hOδ := valid_mono O hO (by norm_num [floor] : floor≤2*floor)
  have hq' : 7*P.threshold/8≤WithLp.ofLp u ⬝ᵥ (gram P O *ᵥ WithLp.ofLp u) := by
    simpa only [KSRayleighAccuracy.realRayleigh_eq_quadratic] using hq
  have hh := RectangularRidgeStoredPaid.numerical_paid_drop P.center P.atoms hP.1 hP.2.1
    O.frame hO.1 P.count_pos P.rectangular hON hP.2.2.1
    (δ:=floor) (by norm_num [floor]) (by norm_num [floor]) hOδ.2
    (MSManuscriptFrameFamily.stored_matrix_le_one O hOδ hO1) hO1 u hu hP.2.2.2 hq'
  rw [stored_potential_eq P O, stored_potential_eq P (paid O (paidSize P) (WithLp.ofLp u))]
  simpa only [paidGain, paidSize, depth, theta, ridge, paid, MSManuscriptPaidStep.cut,
    MSManuscriptPaidStep.unitRank_of_norm_one u hu] using hh

theorem continuation (P : Parameters N d) (hP : P.Valid) (R : Report P) (K : Owner N)
    (hK : K.Valid (2*floor)) (hK1 : K.physical≤1) (hKN : K.dim≤N)
    {u : EuclideanSpace ℝ (Fin K.dim)} (hu : direction P R K=some u) :
    State (paid K (paidSize P) (WithLp.ofLp u)) ∧ WithLp.ofLp u≠0 ∧
    potential P (paid K (paidSize P) (WithLp.ofLp u))+paidGain P≤potential P K := by
  have hKδ := valid_mono K hK (by norm_num [floor] : floor≤2*floor)
  have hh := direction_some P hP R K ⟨hKδ,hK1,hKN⟩ hu
  have hne : WithLp.ofLp u≠0 := by
    intro hz
    have he : u=0 := WithLp.ofLp_injective 2 hz
    rw [he,norm_zero] at hh
    norm_num at hh
  exact ⟨⟨paid_valid K (by norm_num [floor]) hK (paidSize_pos P).le (paidSize_le P) u hh.1,
    (paid_le K (paidSize_pos P).le _).trans hK1,hKN⟩,hne,
    paid_potential_drop P hP K hK hK1 hKN u hh.1 hh.2.le⟩

end MatrixSpencer.RectangularRidgePreparationData
