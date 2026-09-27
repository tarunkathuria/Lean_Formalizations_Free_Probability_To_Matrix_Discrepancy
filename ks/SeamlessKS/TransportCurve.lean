import MatrixSpencer.KSSupportedCenterCurve
import MatrixSpencer.KSHessianContact

/-! Moving supported transport centers for arbitrary scalar source curves.
The coefficient values and their first two derivatives are kept separate;
no quadratic-source schedule is imposed. -/

open Matrix Filter Topology
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator ContDiff
noncomputable section
namespace SeamlessKS.TransportCurve

open MatrixSpencer MatrixSpencer.KSMovingOwnerHessian MatrixSpencer.KSSupportedCenterCurve

section Scalar

def probe (c : ℝ → ℝ) (q r t : ℝ) : ℝ := c t*(q+t*r)
def probeVelocity (c cv : ℝ → ℝ) (q r t : ℝ) : ℝ :=
  cv t*(q+t*r)+c t*r

theorem hasDerivAt_probe (c cv : ℝ → ℝ) (q r t : ℝ)
    (hc : HasDerivAt c (cv t) t) :
    HasDerivAt (probe c q r) (probeVelocity c cv q r t) t := by
  have hh := hc.mul ((hasDerivAt_const t q).add ((hasDerivAt_id t).mul_const r))
  simpa [probe, probeVelocity] using hh

theorem hasDerivAt_probeVelocity_zero (c cv : ℝ → ℝ) (q r ca : ℝ)
    (hc : HasDerivAt c (cv 0) 0) (hv : HasDerivAt cv ca 0) :
    HasDerivAt (probeVelocity c cv q r) (ca*q+2*cv 0*r) 0 := by
  have hh := (hv.mul ((hasDerivAt_const (0:ℝ) q).add
    ((hasDerivAt_id (0:ℝ)).mul_const r))).add (hc.mul_const r)
  convert hh using 1
  dsimp [probeVelocity] at *
  ring

end Scalar

section Center
variable {ι n E : Type*} [Fintype ι] [Fintype n] [DecidableEq n]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
local instance centerCStar : CStarAlgebra (Matrix n n ℂ) := {}

def centerCurve (embed : Matrix n n ℂ →L[ℝ] E) (H K : E) (A : ι → E)
    (Z U : Matrix n n ℂ) (c : ι → ℝ → ℝ) (q r : ι → ℝ) (t : ℝ) : E :=
  H+t • K+embed (inverseLine Z U t)+∑ i, probe (c i) (q i) (r i) t • A i

def centerVelocity (embed : Matrix n n ℂ →L[ℝ] E) (K : E) (A : ι → E)
    (Z U : Matrix n n ℂ) (c cv : ι → ℝ → ℝ) (q r : ι → ℝ) (t : ℝ) : E :=
  K+embed (inverseVelocity Z U t)+∑ i, probeVelocity (c i) (cv i) (q i) (r i) t • A i

def centerAcceleration (embed : Matrix n n ℂ →L[ℝ] E) (A : ι → E)
    (Z U : Matrix n n ℂ) (cv ca q r : ι → ℝ) : E :=
  (2:ℝ) • embed (Z⁻¹*U*Z⁻¹*U*Z⁻¹)+∑ i, (ca i*q i+2*cv i*r i) • A i

theorem hasDerivAt_centerCurve (embed : Matrix n n ℂ →L[ℝ] E)
    (H K : E) (A : ι → E) (Z U : Matrix n n ℂ)
    (c cv : ι → ℝ → ℝ) (q r : ι → ℝ) (t : ℝ)
    (hZ : IsUnit (transportLine Z U t)) (hc : ∀ i, HasDerivAt (c i) (cv i t) t) :
    HasDerivAt (centerCurve embed H K A Z U c q r)
      (centerVelocity embed K A Z U c cv q r t) t := by
  have hl := (hasDerivAt_const t H).add ((hasDerivAt_id t).smul_const K)
  have hi := embed.hasFDerivAt.comp_hasDerivAt t
    (MatrixSpencer.KSMovingOwnerHessian.hasDerivAt_inverseLine Z U t hZ)
  have hs := HasDerivAt.fun_sum (u:=Finset.univ) (fun i _ =>
    (hasDerivAt_probe (c i) (cv i) (q i) (r i) t (hc i)).smul_const (A i))
  simpa only [centerCurve, centerVelocity, inverseVelocity, one_smul, zero_add] using
    (hl.add hi).add hs

theorem hasDerivAt_centerVelocity_zero (embed : Matrix n n ℂ →L[ℝ] E)
    (K : E) (A : ι → E) (Z U : Matrix n n ℂ) (hZ : IsUnit Z)
    (c cv : ι → ℝ → ℝ) (ca q r : ι → ℝ)
    (hc : ∀ i, HasDerivAt (c i) (cv i 0) 0)
    (hv : ∀ i, HasDerivAt (cv i) (ca i) 0) :
    HasDerivAt (centerVelocity embed K A Z U c cv q r)
      (centerAcceleration embed A Z U (fun i => cv i 0) ca q r) 0 := by
  have hi := embed.hasFDerivAt.comp_hasDerivAt 0
    (MatrixSpencer.KSMovingOwnerHessian.hasDerivAt_inverseVelocity_zero Z U hZ)
  have hs := HasDerivAt.fun_sum (u:=Finset.univ) (fun i _ =>
    (hasDerivAt_probeVelocity_zero (c i) (cv i) (q i) (r i) (ca i) (hc i) (hv i)).smul_const (A i))
  simpa only [centerVelocity, centerAcceleration, map_smul, zero_add] using
    ((hasDerivAt_const (0:ℝ) K).add hi).add hs

theorem iteratedDeriv_two_centerCurve (embed : Matrix n n ℂ →L[ℝ] E)
    (H K : E) (A : ι → E) (Z U : Matrix n n ℂ) (hZ : IsUnit Z)
    (c cv : ι → ℝ → ℝ) (ca q r : ι → ℝ)
    (hc : ∀ i t, HasDerivAt (c i) (cv i t) t)
    (hv : ∀ i, HasDerivAt (cv i) (ca i) 0) :
    iteratedDeriv 2 (centerCurve embed H K A Z U c q r) 0 =
      centerAcceleration embed A Z U (fun i => cv i 0) ca q r := by
  have hevent : ∀ᶠ t in 𝓝 (0:ℝ), IsUnit (transportLine Z U t) :=
    (hasDerivAt_transportLine Z U 0).continuousAt.eventually
      (Units.isOpen.mem_nhds (by simpa [transportLine] using hZ))
  have heq : deriv (centerCurve embed H K A Z U c q r) =ᶠ[𝓝 (0:ℝ)]
      centerVelocity embed K A Z U c cv q r := by
    filter_upwards [hevent] with t ht
    exact (hasDerivAt_centerCurve embed H K A Z U c cv q r t ht (fun i => hc i t)).deriv
  rw [show (2:ℕ)=1+1 from rfl, iteratedDeriv_succ, iteratedDeriv_one,
    heq.deriv_eq]
  exact (hasDerivAt_centerVelocity_zero embed K A Z U hZ c cv ca q r
    (fun i => hc i 0) hv).deriv

theorem contDiffAt_centerCurve (embed : Matrix n n ℂ →L[ℝ] E)
    (H K : E) (A : ι → E) (Z U : Matrix n n ℂ) (hZ : IsUnit Z)
    (c : ι → ℝ → ℝ) (q r : ι → ℝ)
    (hc : ∀ i, ContDiffAt ℝ 2 (c i) 0) :
    ContDiffAt ℝ 2 (centerCurve embed H K A Z U c q r) 0 := by
  have hinv : ContDiffAt ℝ 2 (inverseLine Z U) 0 :=
    (contDiffAt_inverseLine Z U hZ).of_le
      (WithTop.coe_le_coe.mpr (show (2 : ℕ∞) ≤ ⊤ from le_top))
  have hi : ContDiffAt ℝ 2 (fun t => embed (inverseLine Z U t)) 0 :=
    (embed.contDiff.contDiffAt).comp 0 hinv
  have hs : ContDiffAt ℝ 2 (fun t => ∑ i, probe (c i) (q i) (r i) t • A i) 0 := by
    apply ContDiffAt.sum
    intro i _
    exact ((hc i).mul (contDiffAt_const.add (contDiffAt_id.mul contDiffAt_const))).smul contDiffAt_const
  exact ((contDiffAt_const.add (contDiffAt_id.smul contDiffAt_const)).add hi).add hs

end Center

end SeamlessKS.TransportCurve
