import HigherRankKS.PotentialSmoothness
import HigherRankKS.ZeroAtoms
import HigherRankKS.CompactVertex

/-! Passing between original cube coordinates and the live-face parameterization. -/

open Matrix MatrixSpencer Set Filter
open scoped BigOperators Topology ContDiff MatrixOrder ComplexOrder

noncomputable section
namespace HigherRankKS.FaceGeometry

variable {N : ℕ}

def live (x : Fin N → ℝ) : Finset (Fin N) := Finset.univ.filter (fun i => |x i| < 1)

def livePoint (x : Fin N → ℝ) : {i // i ∈ live x} → ℝ := fun i => x i

def liftDirection (x : Fin N → ℝ) (h : {i // i ∈ live x} → ℝ) : Fin N → ℝ :=
  fun i => if hi : i ∈ live x then h ⟨i, hi⟩ else 0

theorem mem_live (x : Fin N → ℝ) (i : Fin N) : i ∈ live x ↔ |x i| < 1 := by
  simp [live]

theorem livePoint_interior (x : Fin N → ℝ) (i : {i // i ∈ live x}) :
    livePoint x i ∈ Ioo (-1 : ℝ) 1 := by
  exact abs_lt.mp ((mem_live x i).mp i.property)

theorem frozen_endpoint {x : Fin N → ℝ} (hx : x ∈ ksCube 1) (i : Fin N)
    (hi : i ∉ live x) : x i = -1 ∨ x i = 1 := by
  have hi' : ¬ |x i| < 1 := by simpa only [mem_live] using hi
  have heq : |x i| = 1 := le_antisymm (abs_le.mpr ⟨hx.1 i, hx.2 i⟩) (le_of_not_gt hi')
  rcases (abs_eq (by norm_num : (0 : ℝ) ≤ 1)).mp heq with h | h
  · exact Or.inr h
  · exact Or.inl h

theorem live_nonempty {x : Fin N → ℝ} (hx : x ∈ ksCube 1) (hnot : ¬ ksVertex 1 x) :
    (live x).Nonempty := by
  by_contra he
  have hemp : live x = ∅ := Finset.not_nonempty_iff_eq_empty.mp he
  apply hnot
  intro i
  exact frozen_endpoint hx i (by simp [hemp])

theorem faceState_base (x : Fin N → ℝ) : faceState (live x) x (livePoint x) = x := by
  funext i
  simp only [faceState, livePoint]
  split <;> rfl

theorem faceState_line (x : Fin N → ℝ) (h : {i // i ∈ live x} → ℝ) (t : ℝ) :
    faceState (live x) x (livePoint x + t • h) = x + t • liftDirection x h := by
  funext i
  simp only [faceState, livePoint, liftDirection, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  split <;> simp_all

theorem liftDirection_frozen (x : Fin N → ℝ) (h : {i // i ∈ live x} → ℝ)
    (i : Fin N) (hi : |x i| = 1) : liftDirection x h i = 0 := by
  have hn : i ∉ live x := by simp [mem_live, hi]
  simp [liftDirection, hn]

theorem liftDirection_ne_zero (x : Fin N → ℝ) {h : {i // i ∈ live x} → ℝ}
    (hh : h ≠ 0) : liftDirection x h ≠ 0 := by
  intro hz
  apply hh
  funext i
  have hi := congrFun hz i
  simpa [liftDirection, i.property] using hi

variable {n : Type*} [Fintype n] [DecidableEq n]

theorem face_potential_eq (A : Fin N → Matrix n n ℂ) {β : ℝ} (hβ : 0 < β)
    (θ : ℝ) {x : Fin N → ℝ} (hx : x ∈ ksCube 1) (y : {i // i ∈ live x} → ℝ) :
    cubePotential A β θ (faceState (live x) x y) =
      potential (signedLift (KSPotentialModels.center A (faceState (live x) x y)))
        (fun i : {i // i ∈ live x} => A i) β (fun i => SourceProfile.owner β (y i)) θ := by
  unfold cubePotential potential
  congr 1
  congr 1
  funext S
  unfold objective
  rw [source_face_eq_live A hβ (live x) x (frozen_endpoint hx) y S]

theorem zero_live_endpoint (A : Fin N → Matrix n n ℂ) (β θ : ℝ)
    (x : Fin N → ℝ) (i : Fin N) (hi : i ∈ live x) (hA : A i = 0) :
    CompactVertex.EndpointOrDescent 1 (cubePotential A β θ) x := by
  left
  exact ⟨i, (mem_live x i).mp hi, 1, Or.inr rfl,
    (cubePotential_update_zero_atom A β θ x i 1 hA).le⟩

/-- At a cube minimum the actual potential has nonnegative second derivative
in every direction of the live face. Frozen coordinates remain in the center. -/
theorem face_second_nonneg_at_minimum [Nonempty n]
    (A : Fin N → Matrix n n ℂ) (hA : ∀ i, (A i).PosSemidef)
    (k : ℕ) (hk : 1 ≤ k) (θ : ℝ) (hθ : 0 < θ)
    {x : Fin N → ℝ} (hx : x ∈ ksCube 1)
    (hmin : IsMinOn (cubePotential A ((1 : ℝ) / 2 ^ k) θ) (ksCube 1) x)
    (h : {i // i ∈ live x} → ℝ) :
    0 ≤ iteratedDeriv 2 (fun t : ℝ =>
      cubePotential A ((1 : ℝ) / 2 ^ k) θ
        (faceState (live x) x (livePoint x + t • h))) 0 := by
  have hs := contDiffAt_cubePotential_face A hA k hk θ hθ (live x) x
    (frozen_endpoint hx) (livePoint x) (livePoint_interior x)
  have hc : ContDiffAt ℝ ∞ (fun t : ℝ => livePoint x + t • h) 0 := by fun_prop
  have hs' : ContDiffAt ℝ 2 (fun t : ℝ =>
      cubePotential A ((1 : ℝ) / 2 ^ k) θ
        (faceState (live x) x (livePoint x + t • h))) 0 := by
    have hs0 : ContDiffAt ℝ ∞
        (fun y => cubePotential A ((1 : ℝ) / 2 ^ k) θ (faceState (live x) x y))
        (livePoint x + (0 : ℝ) • h) := by simpa using hs
    exact (hs0.comp 0 hc).of_le
      (WithTop.coe_le_coe.mpr (show (2 : ℕ∞) ≤ ⊤ from le_top))
  by_contra hn
  have hneg := lt_of_not_ge hn
  obtain ⟨y, hy, hless⟩ := CompactVertex.exists_cube_descent_of_negative_second
    (a := (1 : ℝ)) (x := x) (cubePotential A ((1 : ℝ) / 2 ^ k) θ)
    (fun t : ℝ => faceState (live x) x (livePoint x + t • h))
    (by simp only [zero_smul, add_zero, faceState_base])
    (by simpa only [faceState_line] using
      (CompactVertex.eventually_mem_cube_along_live_direction hx (liftDirection x h)
        (liftDirection_frozen x h))) hs' hneg
  exact (not_lt_of_ge (hmin hy)) hless

end HigherRankKS.FaceGeometry
