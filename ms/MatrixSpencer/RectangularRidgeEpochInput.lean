import MatrixSpencer.RectangularRidgeLiveOwnerBounds
import MatrixSpencer.RectangularRidgePreparation
import MatrixSpencer.RectangularRidgeUniformResponse

/-!
# Primitive data and explicit parameters for a fixed-universe live epoch

All original coordinates and atoms remain in the center. The exponent,
regularizer strength, conditioning scales and mesh depend on the original
input size. The paid threshold uses the current live count, and the duration
uses the actual uniform response coefficient, preserving the logarithmic
aspect-ratio bound rather than substituting a polynomial upper bound.
-/
open Matrix
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section
namespace MatrixSpencer.RectangularRidgeEpochInput
open RectangularRidgeNumericalOptimizerFloor (size)
open RectangularRidgeNumericalParameters
variable {N d : ℕ} [Nonempty (Fin d)]
local instance ridgeEpochInputCStar : CStarAlgebra (Matrix (Fin d) (Fin d) ℂ) := {}
local instance ridgeEpochInputSpace : NormedSpace ℝ (selfAdjoint (Matrix (Fin d) (Fin d) ℂ)) := inferInstance
set_option exponentiation.threshold 2048
set_option maxRecDepth 4096

def margin (N : ℕ) : ℝ := 1 / (16384 * (N : ℝ))

structure Config (N d : ℕ) where
  atoms : Fin N → Matrix (Fin d) (Fin d) ℂ
  hermitian : ∀ i, (atoms i).IsHermitian
  contractions : ∀ i, ‖atoms i‖ ≤ 1
  count_pos : 1 ≤ N
  rectangular : N ≤ d
  start : EuclideanSpace ℝ (Fin N)
  start_regular : CubeRegular (margin N) start
  live_large : 32 ≤ RectangularRidgeLiveOwner.count (frozenCoordinates start)

def oldFrozen (c : Config N d) := frozenCoordinates c.start
def live (c : Config N d) := RectangularRidgeLiveOwner.count (oldFrozen c)
def center (c : Config N d) (x : EuclideanSpace ℝ (Fin N)) := epochCenter 0 c.atoms c.hermitian x

def threshold (c : Config N d) : ℝ := 4096 / Real.sqrt (live c : ℝ)
def duration (c : Config N d) : ℝ := RectangularRidgeUniformResponse.duration N d c.count_pos
def mesh (_c : Config N d) : ℝ := RectangularRidgeNumericalParameters.mesh (size d N)

def params (c : Config N d) (x : EuclideanSpace ℝ (Fin N)) : RectangularRidgePreparationData.Parameters N d where
  center := center c x
  atoms := c.atoms
  threshold := threshold c
  count_pos := c.count_pos
  rectangular := c.rectangular

theorem live_large (c : Config N d) : 32 ≤ live c := c.live_large
theorem live_le (c : Config N d) : live c ≤ N := RectangularRidgeLiveOwner.count_le _
theorem live_pos (c : Config N d) : (0 : ℝ) < live c := by exact_mod_cast (by have := live_large c; omega : 0 < live c)

theorem size_one_le (c : Config N d) : 1 ≤ size d N := by
  have hn : (1 : ℝ) ≤ N := by exact_mod_cast c.count_pos
  dsimp [size]
  linarith [Nat.cast_nonneg (α := ℝ) d]

theorem margin_pos (c : Config N d) : 0 < margin N := by
  have hn : (0 : ℝ) < N := by exact_mod_cast (by have := c.count_pos; omega : 0 < N)
  unfold margin
  positivity

theorem center_norm_le (c : Config N d) (x : EuclideanSpace ℝ (Fin N)) (hx : ∀ i, |x i| ≤ 1) :
    ‖(center c x : Matrix (Fin d) (Fin d) ℂ)‖ ≤ N := by
  have hh := epochCenter_norm_le 0 c.atoms c.hermitian c.contractions x hx
  simpa only [norm_zero, zero_add, Fintype.card_fin] using hh

theorem threshold_floor (c : Config N d) : 1 / size d N ≤ threshold c := by
  have hS : 0 < size d N := by linarith [size_one_le c]
  have hℓ : (1 : ℝ) ≤ live c := by exact_mod_cast (by have := live_large c; omega : 1 ≤ live c)
  have hℓN : (live c : ℝ) ≤ N := by exact_mod_cast live_le c
  have hNS : (N : ℝ) ≤ size d N := by dsimp [size]; linarith [Nat.cast_nonneg (α := ℝ) d]
  have hr : Real.sqrt (live c : ℝ) ≤ live c := by
    apply Real.sqrt_le_iff.mpr
    exact ⟨hℓ.trans' (by norm_num), by nlinarith⟩
  unfold threshold
  apply (div_le_div_iff₀ hS (Real.sqrt_pos.mpr (live_pos c))).mpr
  nlinarith

theorem params_valid (c : Config N d) (x : EuclideanSpace ℝ (Fin N)) (hx : ∀ i, |x i| ≤ 1) :
    (params c x).Valid := ⟨c.hermitian, c.contractions, center_norm_le c x hx, threshold_floor c⟩

theorem mesh_pos (c : Config N d) : 0 < mesh c := small_pos (by linarith [size_one_le c]) 540 104

theorem mesh_cube (c : Config N d) : mesh c * Real.sqrt (N : ℝ) ≤ margin N := by
  have hn : (1 : ℝ) ≤ N := by exact_mod_cast c.count_pos
  have hn0 : (0 : ℝ) < N := by linarith
  have hNS : (N : ℝ) ≤ size d N := by dsimp [size]; linarith [Nat.cast_nonneg (α := ℝ) d]
  have hr : Real.sqrt (N : ℝ) ≤ N := Real.sqrt_le_iff.mpr ⟨hn0.le, by nlinarith⟩
  have hm : mesh c ≤ 1 / (16384 * (N : ℝ) ^ 2) := by
    have hp : (N : ℝ) ^ 2 ≤ size d N ^ 2 := (sq_le_sq₀ hn0.le (by linarith)).mpr hNS
    calc
      mesh c ≤ small (size d N) 14 2 := small_mono (size_one_le c) (by omega) (by omega)
      _ = 1 / (16384 * size d N ^ 2) := by norm_num [small, big]
      _ ≤ 1 / (16384 * (N : ℝ) ^ 2) := one_div_le_one_div_of_le (by positivity) (by nlinarith)
  calc
    mesh c * Real.sqrt (N : ℝ) ≤ mesh c * N := mul_le_mul_of_nonneg_left hr (mesh_pos c).le
    _ ≤ (1 / (16384 * (N : ℝ) ^ 2)) * N := mul_le_mul_of_nonneg_right hm hn0.le
    _ = margin N := by unfold margin; field_simp

theorem mesh_square (c : Config N d) : mesh c ^ 2 ≤ 1 / 2 := by
  have hh : mesh c ≤ (1 / 2 : ℝ) := by
    have hm := small_mono (size_one_le c) (show 1 ≤ 540 by omega) (show 0 ≤ 104 by omega)
    simpa [mesh, RectangularRidgeNumericalParameters.mesh, small, big] using hm
  nlinarith [mesh_pos c]

theorem duration_pos (c : Config N d) : 0 < duration c :=
  RectangularRidgeUniformResponse.duration_positive c.count_pos c.rectangular

theorem duration_le_third (c : Config N d) : duration c ≤ 1 / 3 :=
  RectangularRidgeUniformResponse.duration_le_third c.count_pos c.rectangular

theorem mesh_time (c : Config N d) : mesh c ^ 2 ≤ duration c / 2 :=
  RectangularRidgeUniformResponse.mesh_time_le c.count_pos c.rectangular

end MatrixSpencer.RectangularRidgeEpochInput
