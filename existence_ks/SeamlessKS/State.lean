import SeamlessKS.Source
import SeamlessKS.Progress
import MatrixSpencer.KSCubePreparation

/-! Actual boundary preparation and local geometric states.
The only computational state is the coefficient array. Cube membership and
the nonnegative rounding threshold are proof fields; no rounding account is stored. -/
open Set
open scoped BigOperators
noncomputable section
namespace SeamlessKS.State
open MatrixSpencer

structure CubeState (N : ℕ) (ρ : ℝ) where
  coeff : Fin N → ℝ
  cube : coeff ∈ ksCube 1
  rho_nonneg : 0 ≤ ρ

structure PreparedState (N : ℕ) (ρ : ℝ) extends CubeState N ρ where
  margin : ∀ i, |coeff i| < 1 → ρ < 1-|coeff i|

variable {N : ℕ} {ρ : ℝ}

theorem coeff_abs_le (s : CubeState N ρ) (i : Fin N) : |s.coeff i| ≤ 1 :=
  abs_le.mpr ⟨s.cube.1 i,s.cube.2 i⟩

def snapDistance (s : CubeState N ρ) (i : Fin N) : ℝ :=
  |KSCubePreparation.snap 1 ρ s.coeff i-s.coeff i|

theorem snapDistance_nonneg (s : CubeState N ρ) (i : Fin N) : 0 ≤ snapDistance s i :=
  abs_nonneg _

theorem snapDistance_le (hρ : 0 ≤ ρ) (s : CubeState N ρ) (i : Fin N) :
    snapDistance s i ≤ ρ := KSCubePreparation.snap_distance_le hρ s.cube i

theorem snapDistance_frozen (s : CubeState N ρ) (i : Fin N) (hi : |s.coeff i|=1) :
    snapDistance s i=0 := by
  simp [snapDistance,KSCubePreparation.snap_preserves_frozen s.coeff i hi]

theorem snapDistance_live (s : CubeState N ρ) (i : Fin N)
    (hi : |KSCubePreparation.snap 1 ρ s.coeff i|<1) :
    KSCubePreparation.snap 1 ρ s.coeff i=s.coeff i ∧ snapDistance s i=0 := by
  by_cases hb : 1-|s.coeff i|≤ρ
  · have he : |KSCubePreparation.snap 1 ρ s.coeff i|=1 := by
      simp only [KSCubePreparation.snap,if_pos hb,KSCubePreparation.endpoint_abs (by norm_num : (0:ℝ)≤1)]
    exact False.elim ((ne_of_lt hi) he)
  · have he : KSCubePreparation.snap 1 ρ s.coeff i=s.coeff i := by
      simp only [KSCubePreparation.snap,if_neg hb]
    exact ⟨he,by simp [snapDistance,he]⟩

def prepare (hρ : 0 ≤ ρ) (s : CubeState N ρ) : PreparedState N ρ where
  coeff := KSCubePreparation.snap 1 ρ s.coeff
  cube := KSCubePreparation.snap_mem_cube (by norm_num) s.cube
  rho_nonneg := hρ
  margin := fun i hi => KSCubePreparation.snap_live_margin (by norm_num) s.coeff i hi

theorem prepare_coeff (hρ : 0 ≤ ρ) (s : CubeState N ρ) :
    (prepare hρ s).coeff=KSCubePreparation.snap 1 ρ s.coeff := rfl

theorem prepare_preserves_frozen (hρ : 0 ≤ ρ) (s : CubeState N ρ)
    (i : Fin N) (hi : |s.coeff i|=1) : (prepare hρ s).coeff i=s.coeff i :=
  KSCubePreparation.snap_preserves_frozen s.coeff i hi

theorem prepare_displacement (hρ : 0 ≤ ρ) (s : CubeState N ρ) (i : Fin N) :
    |(prepare hρ s).coeff i-s.coeff i|≤ρ := snapDistance_le hρ s i

theorem prepare_rounds_only_near (hρ : 0 ≤ ρ) (s : CubeState N ρ) (i : Fin N)
    (hi : (prepare hρ s).coeff i ≠ s.coeff i) : 1-|s.coeff i|≤ρ := by
  by_contra hb
  apply hi
  simp only [prepare,KSCubePreparation.snap,if_neg hb]

theorem prepare_entropy (hρ : 0 ≤ ρ) (s : CubeState N ρ) :
    Progress.entropy (prepare hρ s).coeff≤Progress.entropy s.coeff := by
  apply Progress.rounding_entropy_nonincreasing s.coeff _ (coeff_abs_le s)
  intro i
  by_cases hb : 1-|s.coeff i|≤ρ
  · have he := KSCubePreparation.endpoint_eq 1 (s.coeff i)
    rcases he with he|he
    · exact Or.inr (Or.inr (by simpa only [prepare,KSCubePreparation.snap,if_pos hb] using he))
    · exact Or.inr (Or.inl (by simpa only [prepare,KSCubePreparation.snap,if_pos hb] using he))
  · exact Or.inl (by simp only [prepare,KSCubePreparation.snap,if_neg hb])

/-- An interior movement updates only the coefficient array. -/
def move (s : CubeState N ρ) (y : Fin N → ℝ) (hy : y ∈ ksCube 1)
    (_hfrozen : ∀ i, |s.coeff i|=1 → y i=s.coeff i) : CubeState N ρ where
  coeff := y
  cube := hy
  rho_nonneg := s.rho_nonneg

def initial (hρ : 0 ≤ ρ) : CubeState N ρ where
  coeff := 0
  cube := ksCube_zero (by norm_num)
  rho_nonneg := hρ

def terminal (s : CubeState N ρ) : Prop := ∀ i, |s.coeff i|=1

theorem terminal_iff_signing (s : CubeState N ρ) :
    terminal s ↔ ∀ i, IsSign (s.coeff i) := by
  constructor
  · intro hs i
    have he := hs i
    rcases le_total 0 (s.coeff i) with hp|hn
    · left; simpa only [abs_of_nonneg hp] using he
    · right; rw [abs_of_nonpos hn] at he; linarith
  · intro hs i
    rcases hs i with he|he <;> rw [he] <;> norm_num

def weights (ζ : ℝ) (x : Fin N → ℝ) : Fin N → ℝ := fun i => Source.weight 64 ζ (x i)/64

theorem weights_nonneg (ζ : ℝ) (s : CubeState N ρ) (i : Fin N) :
    0≤weights ζ s.coeff i := div_nonneg
      (Source.weight_nonneg (by norm_num) (coeff_abs_le s i)) (by norm_num)

theorem weights_lower (ζ : ℝ) (s : CubeState N ρ) (i : Fin N) :
    1-s.coeff i^2≤weights ζ s.coeff i := by
  have hh := Source.weight_lower (ζ:=ζ) (by norm_num : (0:ℝ)≤64) (coeff_abs_le s i)
  dsimp only [weights]
  linarith

theorem weights_upper {ζ : ℝ} (hζ : 0 ≤ ζ) (s : CubeState N ρ) (i : Fin N) :
    weights ζ s.coeff i≤2 := by
  have hh := Source.weight_upper (by norm_num : (0:ℝ)≤64) hζ (s.coeff i)
  dsimp only [weights]
  linarith

theorem weights_frozen (ζ : ℝ) (s : CubeState N ρ) (i : Fin N) (hi : |s.coeff i|=1) :
    weights ζ s.coeff i=0 := by
  rcases le_total 0 (s.coeff i) with hp|hn
  · have he : s.coeff i=1 := by simpa only [abs_of_nonneg hp] using hi
    simp [weights,he,Source.weight]
  · have he : s.coeff i= -1 := by rw [abs_of_nonpos hn] at hi; linarith
    simp [weights,he,Source.weight]

end SeamlessKS.State
