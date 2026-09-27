import RadialKS.Progress
import SeamlessKS.StatePotential

/-! Finite deterministic accounting. Local hypotheses in this module are
interfaces to be discharged by the concrete radial walk, not main-theorem assumptions. -/
open scoped BigOperators
noncomputable section
namespace RadialKS.DeterministicRun
open SeamlessKS.State SeamlessKS.StatePotential RadialKS.Progress
variable {N : ℕ} {ρ : ℝ}

def run {S : Type*} (step : S → S) (s : S) : ℕ → S
  | 0 => s
  | k + 1 => step (run step s k)

theorem run_energy (step : PreparedState N ρ → PreparedState N ρ)
    (habsorb : ∀ s, terminal s.toCubeState → step s = s)
    {c : ℝ} (hgain : ∀ s, ¬terminal s.toCubeState →
      energy s.coeff + c ≤ energy (step s).coeff)
    (s : PreparedState N ρ) (k : ℕ)
    (hk : ¬terminal (run step s k).toCubeState) :
    energy s.coeff + (k : ℝ) * c ≤ energy (run step s k).coeff := by
  induction k with
  | zero => simp [run]
  | succ k ih =>
    have hprev : ¬terminal (run step s k).toCubeState := by
      intro ht
      apply hk
      simpa only [run, habsorb _ ht] using ht
    have hg := hgain (run step s k) hprev
    have hi := ih hprev
    simp only [run, Nat.cast_add, Nat.cast_one]
    linarith

theorem run_terminal (step : PreparedState N ρ → PreparedState N ρ)
    (habsorb : ∀ s, terminal s.toCubeState → step s = s)
    {c : ℝ} (hgain : ∀ s, ¬terminal s.toCubeState →
      energy s.coeff + c ≤ energy (step s).coeff)
    (s : PreparedState N ρ) (T : ℕ) (hT : (N : ℝ) < (T : ℝ) * c) :
    terminal (run step s T).toCubeState := by
  by_contra ht
  have h := run_energy step habsorb hgain s T ht
  have h0 := energy_nonneg s.coeff
  have hN := energy_le (run step s T).toCubeState
  linarith

theorem run_monotone {S : Type*} (step : S → S) (W : S → ℝ)
    (hW : ∀ s, W (step s) ≤ W s) (s : S) (k : ℕ) :
    W (run step s k) ≤ W s := by
  induction k with
  | zero => exact le_rfl
  | succ k ih => exact (hW _).trans ih

def choosePlus (qp qm : ℝ) : Bool := decide (qp ≤ qm)

theorem chosen_value_le_average {fp fm qp qm ν : ℝ}
    (hp : |qp - fp| ≤ ν) (hm : |qm - fm| ≤ ν) :
    (if choosePlus qp qm then fp else fm) ≤ (fp + fm) / 2 + 2 * ν := by
  have hp' := abs_le.mp hp
  have hm' := abs_le.mp hm
  by_cases h : qp ≤ qm
  · simp only [choosePlus, h, decide_true, ↓reduceIte]
    linarith
  · simp only [choosePlus, h, decide_false, Bool.false_eq_true, ↓reduceIte]
    have hh : qm < qp := lt_of_not_ge h
    linarith

variable {d : ℕ}
open scoped Matrix.Norms.L2Operator

def budget (v : Fin N → Fin d → ℂ) (θ ζ β : ℝ) (s : CubeState N ρ) : ℝ :=
  account v θ ζ s + β * deficit s.coeff

theorem norm_le_budget [Nonempty (Fin d)]
    (v : Fin N → Fin d → ℂ) {θ β : ℝ} (hθ : 0 < θ) (ζ : ℝ)
    (hβ : 0 ≤ β) (s : CubeState N ρ) :
    ‖signedSum v s.coeff‖ ≤ budget v θ ζ β s :=
  (norm_le_account v hθ ζ s).trans
    (le_add_of_nonneg_right (mul_nonneg hβ (deficit_nonneg s)))

theorem prepare_budget [Nonempty (Fin d)]
    (hρ : 0 ≤ ρ) (v : Fin N → Fin d → ℂ) {θ β : ℝ}
    (hθ : 0 < θ) (ζ : ℝ) (hβ : 0 ≤ β) (s : CubeState N ρ) :
    budget v θ ζ β (prepare hρ s).toCubeState ≤ budget v θ ζ β s := by
  have ha := prepare_account_nonincreasing hρ v hθ ζ s
  have he := prepare_energy hρ s
  have hm := mul_le_mul_of_nonneg_left (sub_le_sub_left he (N : ℝ)) hβ
  exact add_le_add ha hm

theorem movement_budget (v : Fin N → Fin d → ℂ) (θ ζ : ℝ)
    {β c : ℝ} (hβ : 0 ≤ β) (s t : CubeState N ρ)
    (hfrozen : ∀ i, |s.coeff i| = 1 → t.coeff i = s.coeff i)
    (hpotential : potential v θ ζ t ≤ potential v θ ζ s + β * c)
    (hgain : energy s.coeff + c ≤ energy t.coeff) :
    budget v θ ζ β t ≤ budget v θ ζ β s := by
  have hr := reserve_mono v s t hfrozen
  have hm := mul_le_mul_of_nonneg_left hgain hβ
  dsimp only [budget, account, deficit]
  nlinarith

end RadialKS.DeterministicRun
