import MatrixSpencer.MSManuscriptNumericalMovement
import MatrixSpencer.EpochCoordinateStep


open Matrix
open scoped BigOperators MatrixOrder
noncomputable section
namespace MatrixSpencer.MSManuscriptNumericalCoordinateStep
variable {N : ℕ}
abbrev Draws (C : Matrix (Fin N) (Fin N) ℝ) (x : EuclideanSpace ℝ (Fin N)) :=
  MSManuscriptNumericalMovement.Draws C (frozenCoordinates x) x

def covariance (C : Matrix (Fin N) (Fin N) ℝ) (x : EuclideanSpace ℝ (Fin N)) :=
  MSManuscriptNumericalMovement.covariance C (frozenCoordinates x) x

def increment (C : Matrix (Fin N) (Fin N) ℝ) (x : EuclideanSpace ℝ (Fin N)) (s : Draws C x) :=
  MSManuscriptNumericalMovement.increment C (frozenCoordinates x) x s

def moved (C : Matrix (Fin N) (Fin N) ℝ) (x : EuclideanSpace ℝ (Fin N)) (h : ℝ) (s : Draws C x) :=
  MSManuscriptNumericalMovement.nextPoint C (frozenCoordinates x) x h s

def rounded (ε : ℝ) (C : Matrix (Fin N) (Fin N) ℝ) (x : EuclideanSpace ℝ (Fin N))
    (h : ℝ) (s : Draws C x) : EuclideanSpace ℝ (Fin N) :=
  WithLp.toLp 2 (ThresholdRounding.roundVector ε (WithLp.ofLp (moved C x h s)))

theorem covariance_posSemidef (C : Matrix (Fin N) (Fin N) ℝ) (hC : C.PosSemidef)
    (x : EuclideanSpace ℝ (Fin N)) : (covariance C x).PosSemidef :=
  SimpleMS.Movement.covariance_posSemidef C _ _
theorem covariance_le (C : Matrix (Fin N) (Fin N) ℝ) (hC : C.PosSemidef)
    (x : EuclideanSpace ℝ (Fin N)) : covariance C x≤C :=
  SimpleMS.Movement.covariance_le C hC _ _

theorem covariance_trace_le {C : Matrix (Fin N) (Fin N) ℝ} (hC : C.PosSemidef)
    (hC1 : C≤1) (x : EuclideanSpace ℝ (Fin N)) : realTrace (covariance C x)≤N := by
  simpa only [Fintype.card_fin] using realTrace_le_card_of_le_one ((covariance_le C hC x).trans hC1)

theorem increment_norm_le {C : Matrix (Fin N) (Fin N) ℝ} (hC : C.PosSemidef) (hC1 : C≤1)
    (x : EuclideanSpace ℝ (Fin N)) (s : Draws C x) : ‖increment C x s‖≤Real.sqrt (N:ℝ) := by
  have he : ‖increment C x s‖^2=realTrace (covariance C x) :=
    MSManuscriptNumericalMovement.increment_norm_sq C hC _ _ s
  rw [←Real.sqrt_sq (norm_nonneg (increment C x s)),he]
  exact Real.sqrt_le_sqrt (covariance_trace_le hC hC1 x)

theorem moved_cube {C : Matrix (Fin N) (Fin N) ℝ} (hC : C.PosSemidef) (hC1 : C≤1)
    {ε : ℝ} {x : EuclideanSpace ℝ (Fin N)} (hx : CubeRegular ε x)
    {h : ℝ} (hh : 0≤h) (hsmall : h*Real.sqrt (N:ℝ)≤ε) (s : Draws C x) :
    ∀i,|moved C x h s i|≤1 := by
  apply MSManuscriptNumericalMovement.nextPoint_mem_cube C hC _ x hx.1
  · intro i hi
    exact (hx.2 i).resolve_left (fun hsign => hi ((mem_frozenCoordinates x i).mpr hsign)) |>.le
  · rw [abs_of_nonneg hh]
    exact (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (covariance_trace_le hC hC1 x)) hh).trans hsmall

theorem rounded_regular {C : Matrix (Fin N) (Fin N) ℝ} (hC : C.PosSemidef) (hC1 : C≤1)
    {ε : ℝ} {x : EuclideanSpace ℝ (Fin N)} (hx : CubeRegular ε x)
    {h : ℝ} (hh : 0≤h) (hsmall : h*Real.sqrt (N:ℝ)≤ε) (s : Draws C x) :
    CubeRegular ε (rounded ε C x h s) := by
  have hm := moved_cube hC hC1 hx hh hsmall s
  exact ⟨fun i => ThresholdRounding.roundScalar_abs_le (hm i),
    fun i => ThresholdRounding.roundScalar_sign_or_interior ε _⟩

theorem rounded_preserves_frozen {C : Matrix (Fin N) (Fin N) ℝ} (hC : C.PosSemidef)
    (ε : ℝ) (x : EuclideanSpace ℝ (Fin N)) (h : ℝ) (s : Draws C x)
    {i : Fin N} (hi : i∈frozenCoordinates x) : rounded ε C x h s i=x i := by
  have hm := MSManuscriptNumericalMovement.frozen_preserved C hC _ x h s i hi
  change ThresholdRounding.roundScalar ε (moved C x h s i)=x i
  rw [show moved C x h s i=x i from hm]
  exact ThresholdRounding.roundScalar_of_isSign ε ((mem_frozenCoordinates x i).mp hi)

theorem frozen_subset {C : Matrix (Fin N) (Fin N) ℝ} (hC : C.PosSemidef)
    (ε : ℝ) (x : EuclideanSpace ℝ (Fin N)) (h : ℝ) (s : Draws C x) :
    frozenCoordinates x⊆frozenCoordinates (rounded ε C x h s) := by
  intro i hi
  rw [mem_frozenCoordinates,rounded_preserves_frozen hC ε x h s hi]
  exact (mem_frozenCoordinates x i).mp hi

theorem rounded_norm_gain {C : Matrix (Fin N) (Fin N) ℝ} (hC : C.PosSemidef) (hC1 : C≤1)
    {ε : ℝ} {x : EuclideanSpace ℝ (Fin N)} (hx : CubeRegular ε x)
    {h : ℝ} (hh : 0≤h) (hsmall : h*Real.sqrt (N:ℝ)≤ε) (s : Draws C x) :
    ‖x‖^2+h^2*realTrace (covariance C x)≤‖rounded ε C x h s‖^2 := by
  have hm := MSManuscriptNumericalMovement.norm_gain C hC (frozenCoordinates x) x h s
  change ‖moved C x h s‖^2=‖x‖^2+h^2*realTrace (covariance C x) at hm
  rw [←hm]
  exact ThresholdRounding.roundVector_euclidean_norm_sq_ge (moved_cube hC hC1 hx hh hsmall s)

theorem rounding_cost_le_new_frozen {C : Matrix (Fin N) (Fin N) ℝ} (hC : C.PosSemidef) (hC1 : C≤1)
    {ε : ℝ} (hε : 0≤ε) {x : EuclideanSpace ℝ (Fin N)} (hx : CubeRegular ε x)
    {h : ℝ} (hh : 0≤h) (hsmall : h*Real.sqrt (N:ℝ)≤ε) (s : Draws C x) :
    (∑i,|rounded ε C x h s i-moved C x h s i|)≤
      ε*((frozenCoordinates (rounded ε C x h s)).card-(frozenCoordinates x).card:ℕ) := by
  let y := rounded ε C x h s
  let z := moved C x h s
  let G := frozenCoordinates y \ frozenCoordinates x
  let cost := fun i => |y i-z i|
  have hsub : frozenCoordinates x⊆frozenCoordinates y := frozen_subset hC ε x h s
  have hc (i : Fin N) : cost i≤ε := ThresholdRounding.roundScalar_cost_le hε (moved_cube hC hC1 hx hh hsmall s i)
  have hz (i : Fin N) (hi : i∉G) : cost i=0 := by
    by_cases hf : i∈frozenCoordinates x
    · have hy : y i=x i := rounded_preserves_frozen hC ε x h s hf
      have hz' : z i=x i := MSManuscriptNumericalMovement.frozen_preserved C hC _ x h s i hf
      simp only [cost,hy,hz',sub_self,abs_zero]
    · have hnf : i∉frozenCoordinates y := fun hy => hi (Finset.mem_sdiff.mpr ⟨hy,hf⟩)
      have he : y i=z i := by
        by_contra hne
        exact hnf ((mem_frozenCoordinates y i).mpr (ThresholdRounding.roundScalar_isSign_of_changed hne))
      simp only [cost,he,sub_self,abs_zero]
  have he : (∑i∈G,cost i)=∑i,cost i :=
    Finset.sum_subset (Finset.subset_univ G) (fun i _ hi => hz i hi)
  change (∑i,cost i)≤_
  rw [←he]
  calc
    _ ≤ ∑_i∈G,ε := Finset.sum_le_sum (fun i _ => hc i)
    _ = ε*((frozenCoordinates y).card-(frozenCoordinates x).card:ℕ) := by
      simp only [Finset.sum_const,nsmul_eq_mul]
      rw [show G.card=(frozenCoordinates y).card-(frozenCoordinates x).card from Finset.card_sdiff_of_subset hsub]
      ring

end MatrixSpencer.MSManuscriptNumericalCoordinateStep
