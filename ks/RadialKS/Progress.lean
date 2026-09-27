import SeamlessKS.Proposals

/-! Squared Euclidean progress for the unweighted radial walk. -/
open scoped BigOperators
noncomputable section
namespace RadialKS.Progress
open SeamlessKS.State SeamlessKS.Proposals
variable {N : ℕ} {ρ : ℝ}

def energy (x : Fin N → ℝ) : ℝ := ∑ i, x i ^ 2

def deficit (x : Fin N → ℝ) : ℝ := (N : ℝ) - energy x

theorem energy_nonneg (x : Fin N → ℝ) : 0 ≤ energy x :=
  Finset.sum_nonneg (fun i _ => sq_nonneg (x i))

theorem energy_le (s : CubeState N ρ) : energy s.coeff ≤ N := by
  calc
    energy s.coeff ≤ ∑ _i : Fin N, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro i _
      have h := coeff_abs_le s i
      have ha := abs_nonneg (s.coeff i)
      nlinarith [sq_abs (s.coeff i)]
    _ = N := by simp

theorem deficit_nonneg (s : CubeState N ρ) : 0 ≤ deficit s.coeff :=
  sub_nonneg.mpr (energy_le s)

def proposal (x : Fin N → ℝ) (g : EuclideanSpace ℝ (Fin N)) (t : ℝ) :
    Fin N → ℝ := fun i => x i + t * g i

theorem proposal_energy (x : Fin N → ℝ) (g : EuclideanSpace ℝ (Fin N))
    (hg : ‖g‖ = 1) (horth : ∑ i, x i * g i = 0) (t : ℝ) :
    energy (proposal x g t) = energy x + t ^ 2 := by
  have hn : (∑ i, (g i) ^ 2) = 1 := by
    have h := EuclideanSpace.norm_sq_eq g
    rw [hg] at h
    simpa only [one_pow, Real.norm_eq_abs, sq_abs] using h.symm
  calc
    energy (proposal x g t) =
        (∑ i, x i ^ 2) + 2 * t * (∑ i, x i * g i) + t ^ 2 * (∑ i, g i ^ 2) := by
      simp only [energy, proposal, Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = energy x + t ^ 2 := by rw [horth, hn]; simp [energy]

theorem proposal_displacement (x : Fin N → ℝ) (g : EuclideanSpace ℝ (Fin N))
    (hg : ‖g‖ = 1) (t : ℝ) (i : Fin N) : |proposal x g t i - x i| ≤ |t| := by
  have hi : |g i| ≤ 1 := by simpa only [Real.norm_eq_abs, hg] using PiLp.norm_apply_le g i
  simpa only [proposal, add_sub_cancel_left, abs_mul, mul_one] using
    mul_le_mul_of_nonneg_left hi (abs_nonneg t)

theorem proposal_frozen (s : PreparedState N ρ) (g : EuclideanSpace ℝ (Fin N))
    (hg : ∀ i, |s.coeff i| = 1 → g i = 0) (t : ℝ) (i : Fin N)
    (hi : |s.coeff i| = 1) : proposal s.coeff g t i = s.coeff i := by
  simp [proposal, hg i hi]

def radialMove (hρ : 0 < ρ) (s : PreparedState N ρ)
    (g : EuclideanSpace ℝ (Fin N)) (hg : ‖g‖ = 1)
    (hgf : ∀ i, |s.coeff i| = 1 → g i = 0)
    (t : ℝ) (ht : |t| ≤ ρ / 16) : CubeState N ρ :=
  move s.toCubeState (proposal s.coeff g t)
    (stays_in_cube hρ s _ (proposal_frozen s g hgf t)
      (fun i => (proposal_displacement s.coeff g hg t i).trans (by linarith))).1
    (proposal_frozen s g hgf t)

theorem radialMove_energy (hρ : 0 < ρ) (s : PreparedState N ρ)
    (g : EuclideanSpace ℝ (Fin N)) (hg : ‖g‖ = 1)
    (hgf : ∀ i, |s.coeff i| = 1 → g i = 0)
    (horth : ∑ i, s.coeff i * g i = 0) (t : ℝ) (ht : |t| ≤ ρ / 16) :
    energy (radialMove hρ s g hg hgf t ht).coeff = energy s.coeff + t ^ 2 :=
  proposal_energy s.coeff g hg horth t

theorem outward_energy (x : Fin N → ℝ) (i : Fin N) {a : ℝ} (ha : 0 ≤ a) :
    energy x + a ^ 2 ≤ energy (outwardVector x i a) := by
  have hi : x i ^ 2 + a ^ 2 ≤ SeamlessKS.Progress.outward (x i) a ^ 2 := by
    unfold SeamlessKS.Progress.outward
    split_ifs with hx
    · nlinarith [mul_nonneg hx ha]
    · nlinarith [mul_nonpos_of_nonpos_of_nonneg (le_of_lt (lt_of_not_ge hx)) ha]
  simp only [energy, outwardVector]
  simp_rw [Function.apply_update (fun _ (z : ℝ) => z ^ 2)]
  rw [Finset.sum_update_of_mem (Finset.mem_univ i)]
  rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ i)]
  simp only [Finset.sdiff_singleton_eq_erase]
  linarith

theorem prepare_energy (hρ : 0 ≤ ρ) (s : CubeState N ρ) :
    energy s.coeff ≤ energy (prepare hρ s).coeff := by
  apply Finset.sum_le_sum
  intro i _
  by_cases hb : 1 - |s.coeff i| ≤ ρ
  · have he : |(prepare hρ s).coeff i| = 1 := by
      simp only [prepare, MatrixSpencer.KSCubePreparation.snap, if_pos hb,
        MatrixSpencer.KSCubePreparation.endpoint_abs (by norm_num : (0 : ℝ) ≤ 1)]
    have hi := coeff_abs_le s i
    have ha := abs_nonneg (s.coeff i)
    nlinarith [sq_abs (s.coeff i), sq_abs ((prepare hρ s).coeff i)]
  · simp only [prepare, MatrixSpencer.KSCubePreparation.snap, if_neg hb, le_refl]

end RadialKS.Progress
