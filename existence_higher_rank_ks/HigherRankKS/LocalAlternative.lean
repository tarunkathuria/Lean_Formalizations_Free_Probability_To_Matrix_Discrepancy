import HigherRankKS.NormalizedHessian
import HigherRankKS.LiveAlternative
import HigherRankKS.FaceCurves
import HigherRankKS.ExistenceReduction

/-! The local alternative for the actual nonlinear potential, with all
analytic premises discharged from the PSD input matrices. -/

open Matrix MatrixSpencer Set
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator

noncomputable section
namespace HigherRankKS

open FaceGeometry SupportedFrames
variable {N : ℕ} {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]

theorem local_alternative_at_minima
    (A : Fin N → Matrix n n ℂ) (hA : ∀ i, (A i).PosSemidef)
    (k : ℕ) (hk : 1 ≤ k) :
    LocalAlternativeAtMinima A ((1 : ℝ) / 2 ^ k) := by
  intro θ hθ x hx hmin hnot
  rcases endpoint_or_negative_frame A hA k hk θ hθ hx hnot with hgood | hbad
  · exact hgood
  rcases hbad with ⟨hne, S, hS, ht, hmax, hfixed, _, ω, y, _, hlegal, hnegative⟩
  let B := fun i : {i // i ∈ live x} => A i
  let β := (1 : ℝ) / 2 ^ k
  let h := coefficientDirection β (livePoint x) y
  have hβ : 0 < β := by dsimp [β]; positivity
  have hupper := NormalizedHessian.normalized_potential_second_le
    (A := B) (hA := fun i => hA i) (hne := hne) (k := k) (hk := hk)
    (x := livePoint x) (hx := livePoint_interior x)
    (H := signedLift (KSPotentialModels.center A x)) (θ := θ) (hθ := hθ)
    (S := S) (hS := hS) (ht := ht) (hmax := hmax) (hfixed := hfixed)
    (w := ω) (y := y) (hlegal := hlegal)
  have hnonneg := face_second_nonneg_at_minimum A hA k hk θ hθ hx hmin h
  have he : (fun t : ℝ => cubePotential A β θ
      (faceState (live x) x (livePoint x + t • h))) =
      (fun t : ℝ => potential (signedLift (KSPotentialModels.center A x) +
        t • (∑ i : {i // i ∈ live x}, h i • signedLift (A i)))
        B β (OwnerCurves.weights β (livePoint x) h t) θ) := by
    funext t
    exact face_potential_line_eq A hβ θ hx h t
  change 0 ≤ iteratedDeriv 2 (fun t : ℝ => cubePotential A β θ
    (faceState (live x) x (livePoint x + t • h))) 0 at hnonneg
  rw [he] at hnonneg
  dsimp only at hupper
  have hstrict := lt_of_le_of_lt hupper (by
    simpa only [SourceProfile.ownerScale] using hnegative)
  exact False.elim (by
    change iteratedDeriv 2 (fun t : ℝ => potential
      (signedLift (KSPotentialModels.center A x) +
        t • (∑ i : {i // i ∈ live x}, h i • signedLift (A i)))
      B β (OwnerCurves.weights β (livePoint x) h t) θ) 0 / 2 < 0 at hstrict
    linarith)

end HigherRankKS
