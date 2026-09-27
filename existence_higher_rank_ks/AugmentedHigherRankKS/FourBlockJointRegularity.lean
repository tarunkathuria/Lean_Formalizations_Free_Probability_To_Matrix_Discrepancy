import AugmentedHigherRankKS.FourBlockFidelityRegularity
import AugmentedHigherRankKS.RuntimeRegularity.SourceRelativeDerivatives
import AugmentedHigherRankKS.GenericJointPolarization
import AugmentedHigherRankKS.FourBlockEnvelopeThird

/-! Concrete joint objective bounds from relative scalar reserve jets. -/
open Matrix MatrixSpencer HigherRankKS Filter
open scoped BigOperators Topology ContDiff MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section
set_option maxHeartbeats 1800000
namespace AugmentedHigherRankKS
open BalancedTransportJets BalancedRegularity
variable {ι n : Type*} [Fintype ι] [Fintype n] [DecidableEq n]
local instance jointRegCStar {m : Type*} [Fintype m] [DecidableEq m] :
    CStarAlgebra (Matrix m m ℂ) := {}

/-- A density floor converts an absolute tangent bound into relative order. -/
theorem density_relative_order {S X : Matrix n n ℂ} (hX : X.IsHermitian)
    {s r : ℝ} (hs : 0 < s) (hr : 0 ≤ r) (hfloor : s • (1 : Matrix n n ℂ) ≤ S)
    (hXr : ‖X‖ ≤ r) : -(r/s) • S ≤ X ∧ X ≤ (r/s) • S := by
  have hxhi := hX.isSelfAdjoint.le_algebraMap_norm_self
  have hxlo := hX.isSelfAdjoint.neg_algebraMap_norm_le_self
  simp only [Algebra.algebraMap_eq_smul_one] at hxhi hxlo
  have hnr : ‖X‖ • (1 : Matrix n n ℂ) ≤ r • (1 : Matrix n n ℂ) :=
    smul_le_smul_of_nonneg_right hXr Matrix.PosSemidef.one.nonneg
  have hf := smul_le_smul_of_nonneg_left hfloor (div_nonneg hr hs.le)
  rw [smul_smul, div_mul_cancel₀ r hs.ne'] at hf
  exact ⟨by simpa only [neg_smul] using (neg_le_neg (hnr.trans hf)).trans hxlo,
    hxhi.trans (hnr.trans hf)⟩

/-- Divide the proved raw source derivatives by their factorial. -/
theorem source_scalarJet_relative
    (A : ι → Matrix n n ℂ) (k : ℕ) (hk : 1 ≤ k)
    (S X : selfAdjoint (Matrix (FourSpin n) (FourSpin n) ℂ))
    (hS : (S : Matrix (FourSpin n) (FourSpin n) ℂ).PosDef)
    {b dc : ℝ} (hb : 0 ≤ b) (hdc : 0 ≤ dc)
    (hlo : -b • (S : Matrix (FourSpin n) (FourSpin n) ℂ) ≤ X)
    (hhi : (X : Matrix (FourSpin n) (FourSpin n) ℂ) ≤ b • (S : Matrix (FourSpin n) (FourSpin n) ℂ))
    (c : ℝ → ι → ℝ) (hc : ContDiffAt ℝ 3 c 0) (hc0 : ∀ i, 0 ≤ c 0 i)
    (hcoeff : ∀ i j, j ≤ 3 →
      ‖iteratedDeriv j (fun t => c t i) 0‖ ≤ (j.factorial : ℝ)*dc^j*c 0 i) :
    ∀ j : ℕ, 1 ≤ j → j ≤ 3 →
      -((dc+2*b)^j) • source A ((1 : ℝ)/2^k) (c 0) S ≤
        jet (fun t => source A ((1 : ℝ)/2^k) (c t) (S+t•X)) j ∧
      jet (fun t => source A ((1 : ℝ)/2^k) (c t) (S+t•X)) j ≤
        (dc+2*b)^j • source A ((1 : ℝ)/2^k) (c 0) S := by
  intro j hj1 hj3
  have hj : (j : WithTop ℕ∞) ≤ 3 := by exact_mod_cast hj3
  have hf : ∀ i, ContDiffAt ℝ j (fun t => c t i) 0 := fun i =>
    ((contDiff_apply ℝ ℝ i).contDiffAt.comp 0 hc).of_le hj
  have hh := HigherRankKSRuntime.SourceRelativeDerivatives.four_source_derivative_relative
    A k hk hS hb hlo hhi hf hc0 hdc (fun i l hl => hcoeff i l (hl.trans hj3))
  have hp : 0 < (j.factorial : ℝ) := Nat.cast_pos.mpr (Nat.factorial_pos j)
  have hl := smul_le_smul_of_nonneg_left hh.1 (inv_nonneg.mpr hp.le)
  have hu := smul_le_smul_of_nonneg_left hh.2 (inv_nonneg.mpr hp.le)
  have hlo' : (j.factorial : ℝ)⁻¹ * (-((j.factorial : ℝ)*(dc+2*b)^j)) = -((dc+2*b)^j) := by
    field_simp
  have hhi' : (j.factorial : ℝ)⁻¹ * ((j.factorial : ℝ)*(dc+2*b)^j) = (dc+2*b)^j := by
    rw [← mul_assoc, inv_mul_cancel₀ hp.ne', one_mul]
  simp only [smul_smul, hlo', hhi'] at hl hu
  exact ⟨hl, hu⟩

/-- All three terms of the concrete objective have controlled actual line jets.
The reserve hypotheses concern scalar input data only. -/
theorem objective_scalarJet_le
    (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).PosSemidef)
    (k : ℕ) (hk : 1 ≤ k)
    (H K : Matrix (FourSpin n) (FourSpin n) ℂ)
    (S X : selfAdjoint (Matrix (FourSpin n) (FourSpin n) ℂ))
    (hS : (S : Matrix (FourSpin n) (FourSpin n) ℂ).PosDef)
    (ht : realTrace (S : Matrix (FourSpin n) (FourSpin n) ℂ) = 1)
    (c : ℝ → ι → ℝ) (hc : ContDiffAt ℝ 3 c 0) (hc0 : ∀ i, 0 < c 0 i)
    {θ b dc d L r C0 : ℝ} (hθ : 0 ≤ θ) (hb : 0 ≤ b) (hdc : 0 ≤ dc)
    (hd : 1 ≤ d) (hdn : Real.sqrt (Fintype.card (FourSpin n) : ℝ) ≤ d)
    (hL : 1 ≤ L) (hr : 0 ≤ r) (hC0 : 0 ≤ C0)
    (hbudget : fidelity (S : Matrix (FourSpin n) (FourSpin n) ℂ)
      (source A ((1 : ℝ)/2^k) (c 0) S) ≤ C0)
    (hXlo : -b • (S : Matrix (FourSpin n) (FourSpin n) ℂ) ≤ X)
    (hXhi : (X : Matrix (FourSpin n) (FourSpin n) ℂ) ≤ b • (S : Matrix (FourSpin n) (FourSpin n) ℂ))
    (hK : ‖K‖ ≤ 2*r) (hX : ‖(X : Matrix (FourSpin n) (FourSpin n) ℂ)‖ ≤ r)
    (hscale : dc+2*b ≤ L*r)
    (hcoeff : ∀ i j, j ≤ 3 →
      ‖iteratedDeriv j (fun t => c t i) 0‖ ≤ (j.factorial : ℝ)*dc^j*c 0 i) :
    ∀ j : ℕ, 2 ≤ j → j ≤ 3 →
      |scalarJet (fun t : ℝ => objective (H+t•K) A ((1 : ℝ)/2^k) (c t) θ (S+t•X)) j| ≤
        (1+2*C0+θ*d)*(100*d*L*r)^j := by
  let β := (1 : ℝ)/2^k
  let D : ℝ → selfAdjoint (Matrix (FourSpin n) (FourSpin n) ℂ) := fun t => S+t•X
  let fc := fun t : ℝ => realTrace ((H+t•K)*(S+t•X : Matrix (FourSpin n) (FourSpin n) ℂ))
  let ff := fun t : ℝ => 2*fidelity (D t : Matrix (FourSpin n) (FourSpin n) ℂ)
    (source A β (c t) (D t))
  let fr := fun t : ℝ => 2*realTrace (CFC.sqrt (D t : Matrix (FourSpin n) (FourSpin n) ℂ))
  have hD : ContDiffAt ℝ 3 D 0 := contDiffAt_const.add (contDiffAt_id.smul contDiffAt_const)
  have hD0 : D 0 = S := by simp [D]
  have hfc : ContDiffAt ℝ 3 fc 0 := by
    have hh : ContDiffAt ℝ 3 (fun t : ℝ => H+t•K) 0 :=
      contDiffAt_const.add (contDiffAt_id.smul contDiffAt_const)
    have hs := (hermitianInclusion (n := FourSpin n)).contDiff.contDiffAt.comp 0 hD
    exact ContDiffAt.comp (g := realTraceCLM (n := FourSpin n))
      (f := fun t : ℝ => (H+t•K)*(D t : Matrix (FourSpin n) (FourSpin n) ℂ))
      0 (realTraceCLM (n := FourSpin n)).contDiff.contDiffAt (hh.mul hs)
  have hff : ContDiffAt ℝ 3 ff 0 := by
    have hh : ContDiffAt ℝ 3 (jointSourceFidelity A β) (c 0, D 0) := by
      rw [hD0]
      exact (contDiffAt_jointSourceFidelity A hA k hk (c 0) hc0 S hS).of_le
        (WithTop.coe_le_coe.mpr (show (3 : ℕ∞) ≤ ⊤ from le_top))
    exact ContDiffAt.comp (g := jointSourceFidelity A β)
      (f := fun t => (c t,D t)) 0 hh (hc.prodMk hD)
  have hfr : ContDiffAt ℝ 3 fr 0 := by
    have hh : ContDiffAt ℝ 3 (tsallisPotential (n := FourSpin n) 1) (D 0) := by
      rw [hD0]
      exact (contDiffAt_tsallisPotential 1 S hS).of_le
        (WithTop.coe_le_coe.mpr (show (3 : ℕ∞) ≤ ⊤ from le_top))
    simpa only [Function.comp_def, tsallisPotential, traceSqrt, mul_one] using hh.comp 0 hD
  have hSnonneg := hS.posSemidef.nonneg
  have hbL : b ≤ dc+2*b := by linarith
  have hbLo : -(dc+2*b) • (S : Matrix (FourSpin n) (FourSpin n) ℂ) ≤ X :=
    (smul_le_smul_of_nonneg_right (neg_le_neg hbL) hSnonneg).trans hXlo
  have hbHi : (X : Matrix (FourSpin n) (FourSpin n) ℂ) ≤
      (dc+2*b) • (S : Matrix (FourSpin n) (FourSpin n) ℂ) :=
    hXhi.trans (smul_le_smul_of_nonneg_right hbL hSnonneg)
  have hsource := source_scalarJet_relative A k hk S X hS hb hdc hXlo hXhi c hc
    (fun i => (hc0 i).le) hcoeff
  have hfbound := sourceFidelity_scalarJet_le A hA k hk c hc hc0 S X hS hd hdn
    (show 0 ≤ dc+2*b by positivity) hbLo hbHi hbudget hsource
  have hrbound := root_affine_scalarJet_le S X hS ht hd hdn hb hXlo hXhi
  have hd0 : 0 ≤ d := by linarith
  have hL0 : 0 ≤ L := by linarith
  have hH0 : 0 ≤ 100*d*L*r := by positivity
  have hdim : (Fintype.card (FourSpin n) : ℝ) ≤ d^2 := by
    nlinarith [Real.sq_sqrt (Nat.cast_nonneg (Fintype.card (FourSpin n))),
      Real.sqrt_nonneg (Fintype.card (FourSpin n) : ℝ)]
  have h2dr : 2*d*r ≤ 100*d*L*r := by
    nlinarith [mul_le_mul_of_nonneg_left hL (show 0 ≤ 100*d*r by positivity)]
  have hcenter : 2*(Fintype.card (FourSpin n) : ℝ)*r^2 ≤ (100*d*L*r)^2 := by
    have hs := mul_self_le_mul_self (show 0 ≤ 2*d*r by positivity) h2dr
    have hm := mul_le_mul_of_nonneg_right hdim (sq_nonneg r)
    nlinarith [sq_nonneg (d*r)]
  intro j hj2 hj3
  have hj1 : 1 ≤ j := by omega
  have hj : (j : WithTop ℕ∞) ≤ 3 := by exact_mod_cast hj3
  have hFj : |scalarJet ff j| ≤ 2*C0*(100*d*L*r)^j := by
    apply (hfbound j hj1 hj3).trans
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply pow_le_pow_left₀ (by positivity)
    nlinarith [mul_le_mul_of_nonneg_left hscale (show 0 ≤ 100*d by positivity)]
  have hRj : |scalarJet (fun t => θ*fr t) j| ≤ θ*d*(100*d*L*r)^j := by
    rw [scalarJet_const_mul hfr hj, abs_mul, abs_of_nonneg hθ]
    have hpow : 2*(100*d*b)^j ≤ (100*d*L*r)^j := by
      have hx : 0 ≤ 100*d*b := by positivity
      have hh : 2*(100*d*b) ≤ 100*d*L*r := by
        nlinarith [mul_le_mul_of_nonneg_left hscale (show 0 ≤ 100*d by positivity),
          mul_nonneg (show 0 ≤ 100*d by positivity) hdc]
      have hp : (2*(100*d*b))^j ≤ (100*d*L*r)^j := pow_le_pow_left₀ (by positivity) hh j
      interval_cases j <;> nlinarith [pow_nonneg hx 2, pow_nonneg hx 3]
    calc
      θ*|scalarJet fr j| ≤ θ*(2*Real.sqrt (Fintype.card (FourSpin n) : ℝ)*(100*d*b)^j) :=
        mul_le_mul_of_nonneg_left (hrbound j hj1 hj3) hθ
      _ ≤ θ*(d*(100*d*L*r)^j) := by
        apply mul_le_mul_of_nonneg_left _ hθ
        calc
          _ ≤ d*(2*(100*d*b)^j) := by
            nlinarith [mul_le_mul_of_nonneg_right hdn (show 0 ≤ 2*(100*d*b)^j by positivity)]
          _ ≤ _ := mul_le_mul_of_nonneg_left hpow hd0
      _ = _ := by ring
  have hCj : |scalarJet fc j| ≤ (100*d*L*r)^j := by
    interval_cases j
    · rw [show fc = fun t : ℝ => realTrace ((H+t•K)*
        ((S : Matrix (FourSpin n) (FourSpin n) ℂ)+t•(X : Matrix (FourSpin n) (FourSpin n) ℂ))) from rfl,
        affine_center_scalarJet_two]
      apply (KSObjectiveValueBound.abs_realTrace_mul_le K (X : Matrix _ _ ℂ)).trans
      apply le_trans _ hcenter
      have hmul := mul_le_mul hK hX (norm_nonneg _) (show 0 ≤ 2*r by positivity)
      nlinarith [mul_le_mul_of_nonneg_left hmul
        (Nat.cast_nonneg (Fintype.card (FourSpin n)) : (0:ℝ) ≤ _)]
    · rw [show fc = fun t : ℝ => realTrace ((H+t•K)*
        ((S : Matrix (FourSpin n) (FourSpin n) ℂ)+t•(X : Matrix (FourSpin n) (FourSpin n) ℂ))) from rfl,
        affine_center_scalarJet_three, abs_zero]
      positivity
  have heq : (fun t : ℝ => objective (H+t•K) A β (c t) θ (S+t•X)) =
      fun t => (fc t + ff t) + θ*fr t := by
    funext t
    simp only [objective, fc, ff, fr, D,
      HigherRankKSRuntime.SourceRelativeDerivatives.selfAdjoint_add, selfAdjoint.val_smul]
    ring
  rw [show ((1:ℝ)/2^k) = β from rfl, heq,
    scalarJet_add (hfc.add hff) (contDiffAt_const.mul hfr) hj,
    scalarJet_add hfc hff hj]
  calc
    _ ≤ (|scalarJet fc j|+|scalarJet ff j|)+|scalarJet (fun t => θ*fr t) j| :=
      (abs_add_le _ _).trans (add_le_add_right (abs_add_le _ _) _)
    _ ≤ ((100*d*L*r)^j+2*C0*(100*d*L*r)^j)+θ*d*(100*d*L*r)^j :=
      add_le_add (add_le_add hCj hFj) hRj
    _ = _ := by ring

end AugmentedHigherRankKS
