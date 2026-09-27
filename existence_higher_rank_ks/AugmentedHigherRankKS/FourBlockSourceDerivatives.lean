import AugmentedHigherRankKS.FourBlockSmoothness
import HigherRankKS.SourceScalarMetric
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

/-! First and second derivatives of the actual source along simultaneous
coefficient and full-density variations. -/

open Matrix MatrixSpencer HigherRankKS Filter Set
open scoped Topology BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator ContDiff

noncomputable section
namespace AugmentedHigherRankKS.SourceDerivatives

section ScalarProduct
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

theorem iteratedDeriv_two_smul (c : ℝ → ℝ) (f : ℝ → V)
    (hc : ContDiffAt ℝ 2 c 0) (hf : ContDiffAt ℝ 2 f 0) :
    iteratedDeriv 2 (fun t => c t • f t) 0 =
      iteratedDeriv 2 c 0 • f 0 + (2 * deriv c 0) • deriv f 0 + c 0 • iteratedDeriv 2 f 0 := by
  have hcd : DifferentiableAt ℝ (deriv c) 0 :=
    ((hc.fderiv_right (show (1 : WithTop ℕ∞) + 1 ≤ 2 by norm_num)).clm_apply
      contDiffAt_const).differentiableAt le_rfl
  have hfd : DifferentiableAt ℝ (deriv f) 0 :=
    ((hf.fderiv_right (show (1 : WithTop ℕ∞) + 1 ≤ 2 by norm_num)).clm_apply
      contDiffAt_const).differentiableAt le_rfl
  have heq : deriv (fun t => c t • f t) =ᶠ[𝓝 0]
      (fun t => deriv c t • f t + c t • deriv f t) := by
    filter_upwards [hc.eventually (by norm_num), hf.eventually (by norm_num)] with t hct hft
    simpa only [Pi.smul_apply, add_comm] using
      ((hct.differentiableAt (by norm_num)).hasDerivAt.smul
        (hft.differentiableAt (by norm_num)).hasDerivAt).deriv
  have hc₁ := (hc.differentiableAt (by norm_num)).hasDerivAt
  have hf₁ := (hf.differentiableAt (by norm_num)).hasDerivAt
  have hd := ((hcd.hasDerivAt.smul hf₁).add (hc₁.smul hfd.hasDerivAt)).deriv
  simp only [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_zero]
  rw [heq.deriv_eq]
  change deriv (deriv c • f + c • deriv f) 0 = _
  rw [hd]
  module

theorem iteratedDeriv_two_finset_sum {ι : Type*} (s : Finset ι) (f : ι → ℝ → V)
    (hf : ∀ i ∈ s, ContDiffAt ℝ 2 (f i) 0) :
    iteratedDeriv 2 (fun t => ∑ i ∈ s, f i t) 0 = ∑ i ∈ s, iteratedDeriv 2 (f i) 0 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [iteratedDeriv_succ, iteratedDeriv_zero]
  | @insert a s ha ih =>
    have hfa := hf a (Finset.mem_insert_self _ _)
    have hfs : ∀ i ∈ s, ContDiffAt ℝ 2 (f i) 0 := fun i hi => hf i (Finset.mem_insert_of_mem hi)
    have hsum : ContDiffAt ℝ 2 (fun t => ∑ i ∈ s, f i t) 0 := ContDiffAt.sum hfs
    simp only [Finset.sum_insert ha]
    change iteratedDeriv 2 (f a + fun t => ∑ i ∈ s, f i t) 0 = _
    rw [iteratedDeriv_add hfa hsum, ih hfs]

theorem iteratedDeriv_two_line_vector {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : E → V) (x v : E) (hf : ContDiffAt ℝ 2 f x) :
    iteratedDeriv 2 (fun t : ℝ => f (x + t • v)) 0 = fderiv ℝ (fderiv ℝ f) x v v := by
  let γ : ℝ → E := fun t => x + t • v
  have hγ : ContDiff ℝ 2 γ := contDiff_const.add (contDiff_id.smul contDiff_const)
  have hdγ : deriv γ = fun _ => v := by
    funext t
    simpa only [one_smul, zero_add] using
      ((hasDerivAt_const t x).add ((hasDerivAt_id t).smul_const v)).deriv
  have hddγ : iteratedDeriv 2 γ 0 = 0 := by
    rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one, hdγ]
    simp
  have hfγ : ContDiffAt ℝ 2 f (γ 0) := by simpa [γ] using hf
  have h := iteratedDeriv_vcomp_two hfγ hγ.contDiffAt
  simpa only [γ, Function.comp_def, zero_smul, add_zero, hdγ, hddγ,
    iteratedFDeriv_two_apply, map_zero, add_zero] using h

end ScalarProduct

section Source
variable {ι n : Type*} [Fintype ι] [Fintype n] [DecidableEq n]
local instance sourceDerivativesCStar : CStarAlgebra (Matrix (FourSpin n) (FourSpin n) ℂ) := {}
local instance sourceDerivativesSpace :
    NormedSpace ℝ (selfAdjoint (Matrix (FourSpin n) (FourSpin n) ℂ)) := inferInstance

def term (β : ℝ) (A : Matrix n n ℂ)
    (S : selfAdjoint (Matrix (FourSpin n) (FourSpin n) ℂ)) : Matrix (FourSpin n) (FourSpin n) ℂ :=
  sourceTerm β A (S : Matrix (FourSpin n) (FourSpin n) ℂ)

/-- The actual source velocity splits into external coefficient forcing
and the derivative in the full ambient density direction. -/
theorem source_first_affine_density
    (A : ι → Matrix n n ℂ) (k : ℕ) (hk : 1 ≤ k)
    (c : ℝ → ι → ℝ) (hc : DifferentiableAt ℝ c 0)
    (S X : selfAdjoint (Matrix (FourSpin n) (FourSpin n) ℂ))
    (hS : (S : Matrix (FourSpin n) (FourSpin n) ℂ).PosDef) :
    deriv
      (fun t => source A ((1 : ℝ) / 2 ^ k) (c t) ((S + t • X) : Matrix (FourSpin n) (FourSpin n) ℂ)) 0 =
      ∑ i, (deriv (fun t => c t i) 0 • term ((1 : ℝ) / 2 ^ k) (A i) S +
        c 0 i • fderiv ℝ (term ((1 : ℝ) / 2 ^ k) (A i)) S X) := by
  have hci (i : ι) : HasDerivAt (fun t => c t i) (deriv (fun t => c t i) 0) 0 :=
    (differentiableAt_pi.mp hc i).hasDerivAt
  have hline (i : ι) : HasDerivAt
      (fun t : ℝ => term ((1 : ℝ) / 2 ^ k) (A i) (S + t • X))
      (fderiv ℝ (term ((1 : ℝ) / 2 ^ k) (A i)) S X) 0 := by
    have hd : HasFDerivAt (term ((1 : ℝ) / 2 ^ k) (A i))
        (fderiv ℝ (term ((1 : ℝ) / 2 ^ k) (A i)) S) (S + (0 : ℝ) • X) := by
      simpa using ((contDiffAt_sourceTerm (A i) k hk S hS).differentiableAt (by simp)).hasFDerivAt
    simpa only [one_smul, zero_add] using
      hd.comp_hasDerivAt (0 : ℝ)
        ((hasDerivAt_const (0 : ℝ) S).add ((hasDerivAt_id (0 : ℝ)).smul_const X))
  have h := (HasDerivAt.fun_sum (u := Finset.univ) (fun i _ => (hci i).smul (hline i))).deriv
  simpa only [source, term, zero_smul, add_zero, Pi.smul_apply, add_comm] using h

/-- Simultaneous coefficient and density acceleration of the actual
source, with all mixed terms and nonlinear density curvature retained. -/
theorem source_second_affine_density
    (A : ι → Matrix n n ℂ) (k : ℕ) (hk : 1 ≤ k)
    (c : ℝ → ι → ℝ) (hc : ContDiffAt ℝ 2 c 0)
    (S X : selfAdjoint (Matrix (FourSpin n) (FourSpin n) ℂ))
    (hS : (S : Matrix (FourSpin n) (FourSpin n) ℂ).PosDef) :
    iteratedDeriv 2
      (fun t => source A ((1 : ℝ) / 2 ^ k) (c t) ((S + t • X) : Matrix (FourSpin n) (FourSpin n) ℂ)) 0 =
      ∑ i, (iteratedDeriv 2 (fun t => c t i) 0 • term ((1 : ℝ) / 2 ^ k) (A i) S +
        (2 * deriv (fun t => c t i) 0) • fderiv ℝ (term ((1 : ℝ) / 2 ^ k) (A i)) S X +
        c 0 i • fderiv ℝ (fderiv ℝ (term ((1 : ℝ) / 2 ^ k) (A i))) S X X) := by
  have hterm (i : ι) : ContDiffAt ℝ 2 (term ((1 : ℝ) / 2 ^ k) (A i)) S :=
    (contDiffAt_sourceTerm (A i) k hk S hS).of_le
      (WithTop.coe_le_coe.mpr (show (2 : ℕ∞) ≤ ⊤ from le_top))
  have hci (i : ι) : ContDiffAt ℝ 2 (fun t => c t i) 0 :=
    (contDiff_apply ℝ ℝ i).contDiffAt.comp 0 hc
  have hline (i : ι) : ContDiffAt ℝ 2
      (fun t : ℝ => term ((1 : ℝ) / 2 ^ k) (A i) (S + t • X)) 0 := by
    have hf : ContDiffAt ℝ 2 (term ((1 : ℝ) / 2 ^ k) (A i)) (S + (0 : ℝ) • X) := by
      simpa using hterm i
    exact hf.comp 0 (f := fun t : ℝ => S + t • X)
      (contDiffAt_const.add (contDiffAt_id.smul contDiffAt_const))
  rw [show (fun t => source A ((1 : ℝ) / 2 ^ k) (c t)
      ((S + t • X) : Matrix (FourSpin n) (FourSpin n) ℂ)) =
      (fun t => ∑ i, c t i • term ((1 : ℝ) / 2 ^ k) (A i) (S + t • X)) from rfl]
  rw [iteratedDeriv_two_finset_sum Finset.univ _ (fun i _ => (hci i).smul (hline i))]
  apply Finset.sum_congr rfl
  intro i _
  rw [iteratedDeriv_two_smul _ _ (hci i) (hline i),
    iteratedDeriv_two_line_vector _ S X (hterm i)]
  have hder : deriv (fun t : ℝ => term ((1 : ℝ) / 2 ^ k) (A i) (S + t • X)) 0 =
      fderiv ℝ (term ((1 : ℝ) / 2 ^ k) (A i)) S X := by
    have hd : HasFDerivAt (term ((1 : ℝ) / 2 ^ k) (A i))
        (fderiv ℝ (term ((1 : ℝ) / 2 ^ k) (A i)) S) (S + (0 : ℝ) • X) := by
      simpa using (hterm i).differentiableAt (by norm_num) |>.hasFDerivAt
    simpa only [one_smul, zero_add] using
      (hd.comp_hasDerivAt (0 : ℝ)
        ((hasDerivAt_const (0 : ℝ) S).add ((hasDerivAt_id (0 : ℝ)).smul_const X))).deriv
  rw [hder]
  simp only [zero_smul, add_zero]

end Source

end AugmentedHigherRankKS.SourceDerivatives
