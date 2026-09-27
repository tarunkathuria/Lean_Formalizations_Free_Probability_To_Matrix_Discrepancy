import HigherRankKS.InitialPotential
import HigherRankKS.InputBounds
import HigherRankKS.RegularizationLimit

/-!
# Closing the existence proof once the local alternative is established

This is an internal reduction, not the unconditional signing
theorem. Its local-alternative hypothesis must still be discharged for the
concrete nonlinear potential. No solver, runtime, or approximation
hypothesis occurs even in this reduction.
-/

open Matrix MatrixSpencer Set
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator

noncomputable section
namespace HigherRankKS

variable {N : ℕ} {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]

/-- The remaining local analytic obligation, needed only at global minima. -/
def LocalAlternativeAtMinima (A : Fin N → Matrix n n ℂ) (β : ℝ) : Prop :=
  ∀ θ : ℝ, 0 < θ → ∀ x ∈ ksCube 1,
    IsMinOn (cubePotential A β θ) (ksCube 1) x →
      ¬ ksVertex 1 x →
        CompactVertex.EndpointOrDescent 1 (cubePotential A β θ) x

theorem exists_signing_of_local_alternative
    (A : Fin N → Matrix n n ℂ) (hA : ∀ i, (A i).PosSemidef)
    (hsum : ∑ i, A i ≤ 1)
    {ε : ℝ} (hε : 0 ≤ ε) (hN : ∀ i, ‖A i‖ ≤ ε)
    {r q : ℕ} (hr : 1 ≤ r) (hrank : ∀ i, (A i).rank ≤ r)
    (hq : 2 ≤ q) (hqlog : logRank r ≤ q)
    (hqupper : (q : ℝ) ≤ 2 * logRank r)
    (halternative : LocalAlternativeAtMinima A ((1 : ℝ) / q)) :
    ∃ s : Fin N → ℝ, (∀ i, s i = 1 ∨ s i = -1) ∧
      ‖KSPotentialModels.center A s‖ ≤
        min 1 (250 * Real.sqrt ε * Real.log (2 * (r : ℝ))) := by
  have hb := reciprocal_scale_bounds hq
  obtain ⟨s, hs, hcost⟩ :=
    RegularizationLimit.exists_real_signing_le_of_regularized_bounds
      (fun s => ‖KSPotentialModels.center A s‖)
      (250 * Real.sqrt ε * Real.log (2 * (r : ℝ)))
      (2 * Real.sqrt (Fintype.card (n ⊕ n) : ℝ)) (by
        intro θ hθ
        obtain ⟨s, hs, _, hvalue⟩ := CompactVertex.exists_full_signing_minimum
          (cubePotential A ((1 : ℝ) / q) θ)
          (continuousOn_cubePotential A hb.1 (by linarith [hb.2]) θ)
          (halternative θ hθ)
        refine ⟨s, hs, ?_⟩
        have hnorm := center_norm_le_cubePotential A
          (fun i => (hA i).isHermitian) hb.1 (by linarith [hb.2]) hθ.le
          (real_signing_mem_cube hs)
        have hbudget := cubePotential_zero_le_logarithmic A hA hsum hε hN
          hr hrank hq hqlog hqupper hθ.le
        calc
          ‖KSPotentialModels.center A s‖ ≤
              cubePotential A ((1 : ℝ) / q) θ 0 := hnorm.trans hvalue
          _ ≤ _ := by simpa only [mul_assoc, mul_left_comm θ 2] using hbudget)
  exact ⟨s, hs, le_min (center_norm_le_one A hA hsum (real_signing_mem_cube hs)) hcost⟩

end HigherRankKS
