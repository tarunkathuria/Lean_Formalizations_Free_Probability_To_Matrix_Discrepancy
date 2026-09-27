import MatrixSpencer.KSSafeRetirement
import MatrixSpencer.KSLocalDescent

/-! Exact contact for any isometric source frame and its positive solving transport. -/

open Matrix Filter Topology
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator ContDiff

noncomputable section
namespace MatrixSpencer.KSArbitraryTransportContact

variable {ι n m : Type*} [Fintype ι] [Fintype n] [Fintype m] [DecidableEq n] [DecidableEq m]

local instance arbitraryContactCStar {s : Type*} [Fintype s] [DecidableEq s] :
    CStarAlgebra (Matrix s s ℂ) := {}
local instance arbitraryContactNormedSpace : NormedSpace ℝ (selfAdjoint (Matrix n n ℂ)) := inferInstance

set_option maxHeartbeats 1000000

theorem transport_unique {S M Z : Matrix n n ℂ} (hS : S.PosDef) (hM : M.PosDef)
    (hZ : Z.PosDef) (hsolve : Z * M * Z = S) : Z = transportOptimizer S M := by
  let Q := CFC.sqrt M
  have hQ : Q.IsHermitian := (CFC.sqrt_nonneg M).posSemidef.isHermitian
  have hQQ : Q * Q = M := CFC.sqrt_mul_sqrt_self M hM.posSemidef.nonneg
  let T := transportOptimizer S M
  have hT : T.PosDef := transportOptimizer_posDef hS hM
  have hsolveT : T * M * T = S := transportOptimizer_solve hS hM
  have hroot (W : Matrix n n ℂ) (hW : W.PosDef) (hw : W * M * W = S) :
      CFC.sqrt (Q * S * Q) = Q * W * Q := by
    apply CFC.sqrt_unique
    · calc
        (Q * W * Q) * (Q * W * Q) = Q * (W * (Q * Q) * W) * Q := by simp only [Matrix.mul_assoc]
        _ = Q * S * Q := by rw [hQQ, hw]
    · simpa only [hQ.eq] using (hW.posSemidef.mul_mul_conjTranspose_same Q).nonneg
  have he := (hroot Z hZ hsolve).symm.trans (hroot T hT hsolveT)
  letI : Invertible Q := hM.posDef_sqrt.isUnit.invertible
  have hh := congrArg (fun R : Matrix n n ℂ => Q⁻¹ * R * Q⁻¹) he
  simpa only [Matrix.mul_assoc, Matrix.inv_mul_cancel_left_of_invertible,
    Matrix.mul_inv_cancel_right_of_invertible, Matrix.mul_inv_of_invertible,
    Matrix.mul_one] using hh

open KSSafeRetirement

theorem supportedGradient_contact (B : ι → Matrix n n ℂ) (V : Matrix n m ℂ)
    (hV : Vᴴ * V = 1) {S : Matrix n n ℂ} (hS : S.PosDef)
    {Z : Matrix m m ℂ} (hZ : Z.PosDef)
    (hM : (Vᴴ * krausChannel B S * V).PosDef)
    (hsolve : Z * (Vᴴ * krausChannel B S * V) * Z = Vᴴ * S * V)
    (hsupport : V * (Vᴴ * krausChannel B S * V) * Vᴴ = krausChannel B S) :
    realTrace (supportedGradient B V Z * S) = 2 * fidelity S (krausChannel B S) := by
  have hS0 := posDef_isometry_compression V hV hS
  have hz := transport_unique hS0 hM hZ hsolve
  rw [supportedGradient_pairing]
  have hf : fidelity S (krausChannel B S) = fidelity (Vᴴ * S * V) (Vᴴ * krausChannel B S * V) := by
    conv_lhs => rw [← hsupport]
    exact fidelity_isometry_compression V hV hS.posSemidef hM.posSemidef
  rw [hf, hz]
  have hc := transportCost_at_transport (transportOptimizer_posDef hS0 hM) (transportOptimizer_solve hS0 hM)
  rw [trace_transportOptimizer_eq_fidelity hS0 hM] at hc
  simpa only [transportCost, realTrace_mul_comm] using hc

theorem fderiv_eq_of_touching_majorant
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f g : E → ℝ} {x : E} (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x)
    (htouch : g x = f x) (hmajorant : ∀ᶠ y in 𝓝 x, f y ≤ g y) :
    fderiv ℝ g x = fderiv ℝ f x := by
  have hm : IsLocalMin (fun y => g y - f y) x := by
    filter_upwards [hmajorant] with y hy
    simpa only [htouch, sub_self] using sub_nonneg.mpr hy
  exact sub_eq_zero.mp (hm.hasFDerivAt_eq_zero (hg.hasFDerivAt.sub hf.hasFDerivAt))

theorem fderiv_base_eq_actual (H : Matrix n n ℂ) (B : ι → Matrix n n ℂ)
    (V : Matrix n m ℂ) (hV : Vᴴ * V = 1) (θ : ℝ)
    (S : selfAdjoint (Matrix n n ℂ)) (hS : (S : Matrix n n ℂ).PosDef)
    {Z : Matrix m m ℂ} (hZ : Z.PosDef)
    (hM : (Vᴴ * krausChannel B S * V).PosDef)
    (hsolve : Z * (Vᴴ * krausChannel B S * V) * Z = Vᴴ * (S : Matrix n n ℂ) * V)
    (hsupport : ∀ X : Matrix n n ℂ, X.PosSemidef →
      V * (Vᴴ * krausChannel B X * V) * Vᴴ = krausChannel B X) :
    fderiv ℝ (hermitianDensityObjective (H + supportedGradient B V Z) (fun _ : Empty => 0) θ) S =
      fderiv ℝ (hermitianDensityObjective H B θ) S := by
  apply fderiv_eq_of_touching_majorant
    ((contDiffAt_hermitianDensityObjective_source_unrestricted H B θ S hS).differentiableAt (by simp))
    ((contDiffAt_hermitianDensityObjective_source_unrestricted (H + supportedGradient B V Z)
      (fun _ : Empty => (0 : Matrix n n ℂ)) θ S hS).differentiableAt (by simp))
  · change densityObjective (H + supportedGradient B V Z) (fun _ : Empty => (0 : Matrix n n ℂ))
      θ (S : Matrix n n ℂ) = densityObjective H B θ S
    rw [densityObjective_empty]
    simp only [Matrix.add_mul, realTrace_add, densityObjective,
      supportedGradient_contact B V hV hS hZ hM hsolve (hsupport S hS.posSemidef)]
  · filter_upwards [eventually_posDef_of_posDef S hS] with X hX
    have hf := fidelity_le_supportedGradient B V hV hZ hX.posSemidef (hsupport X hX.posSemidef)
    change densityObjective H B θ (X : Matrix n n ℂ) ≤
      densityObjective (H + supportedGradient B V Z) (fun _ : Empty => (0 : Matrix n n ℂ)) θ X
    rw [densityObjective_empty]
    simp only [Matrix.add_mul, realTrace_add, densityObjective]
    linarith

theorem base_isMaxOn_of_actual (H : Matrix n n ℂ) (B : ι → Matrix n n ℂ)
    (V : Matrix n m ℂ) (hV : Vᴴ * V = 1) {θ : ℝ} (hθ : 0 < θ)
    (S : selfAdjoint (Matrix n n ℂ)) (hS : (S : Matrix n n ℂ).PosDef)
    (ht : realTrace (S : Matrix n n ℂ) = 1)
    (hmax : ∀ T ∈ densitySet, densityObjective H B θ T ≤ densityObjective H B θ S)
    {Z : Matrix m m ℂ} (hZ : Z.PosDef)
    (hM : (Vᴴ * krausChannel B S * V).PosDef)
    (hsolve : Z * (Vᴴ * krausChannel B S * V) * Z = Vᴴ * (S : Matrix n n ℂ) * V)
    (hsupport : ∀ X : Matrix n n ℂ, X.PosSemidef →
      V * (Vᴴ * krausChannel B X * V) * Vᴴ = krausChannel B X) :
    ∀ T ∈ densitySet, densityObjective (H + supportedGradient B V Z) (fun _ : Empty => 0) θ T ≤
      densityObjective (H + supportedGradient B V Z) (fun _ : Empty => 0) θ S := by
  apply density_stationary_isMaxOn_source_unrestricted _ _ hθ S hS ht
  rw [fderiv_base_eq_actual H B V hV θ S hS hZ hM hsolve hsupport]
  exact density_maximizer_stationary_source_unrestricted H B θ S hS ht hmax

theorem basePotential_contact (H : Matrix n n ℂ) (B : ι → Matrix n n ℂ)
    (V : Matrix n m ℂ) (hV : Vᴴ * V = 1) {θ : ℝ} (hθ : 0 < θ)
    (S : selfAdjoint (Matrix n n ℂ)) (hS : (S : Matrix n n ℂ).PosDef)
    (ht : realTrace (S : Matrix n n ℂ) = 1)
    (hmax : ∀ T ∈ densitySet, densityObjective H B θ T ≤ densityObjective H B θ S)
    {Z : Matrix m m ℂ} (hZ : Z.PosDef)
    (hM : (Vᴴ * krausChannel B S * V).PosDef)
    (hsolve : Z * (Vᴴ * krausChannel B S * V) * Z = Vᴴ * (S : Matrix n n ℂ) * V)
    (hsupport : ∀ X : Matrix n n ℂ, X.PosSemidef →
      V * (Vᴴ * krausChannel B X * V) * Vᴴ = krausChannel B X) :
    baseDensityPotential (H + supportedGradient B V Z) θ = densityPotential H B θ := by
  rw [baseDensityPotential,
    densityPotential_eq_of_maximizer _ _ _ ⟨hS.posSemidef, ht⟩
      (base_isMaxOn_of_actual H B V hV hθ S hS ht hmax hZ hM hsolve hsupport),
    densityPotential_eq_of_maximizer H B θ ⟨hS.posSemidef, ht⟩ hmax, densityObjective_empty]
  simp only [Matrix.add_mul, realTrace_add, densityObjective,
    supportedGradient_contact B V hV hS hZ hM hsolve (hsupport S hS.posSemidef)]

theorem baseOptimizer_eq_actual [Nonempty n] (H : Matrix n n ℂ) (B : ι → Matrix n n ℂ)
    (V : Matrix n m ℂ) (hV : Vᴴ * V = 1) {θ : ℝ} (hθ : 0 < θ)
    (S : selfAdjoint (Matrix n n ℂ)) (hS : (S : Matrix n n ℂ).PosDef)
    (ht : realTrace (S : Matrix n n ℂ) = 1)
    (hmax : ∀ T ∈ densitySet, densityObjective H B θ T ≤ densityObjective H B θ S)
    {Z : Matrix m m ℂ} (hZ : Z.PosDef)
    (hM : (Vᴴ * krausChannel B S * V).PosDef)
    (hsolve : Z * (Vᴴ * krausChannel B S * V) * Z = Vᴴ * (S : Matrix n n ℂ) * V)
    (hsupport : ∀ X : Matrix n n ℂ, X.PosSemidef →
      V * (Vᴴ * krausChannel B X * V) * Vᴴ = krausChannel B X) :
    hermitianDensityOptimizer (H + supportedGradient B V Z) (fun _ : Empty => 0) θ = S := by
  apply density_stationary_eq_optimizer_source_unrestricted _ _ hθ S hS ht
  rw [fderiv_base_eq_actual H B V hV θ S hS hZ hM hsolve hsupport]
  exact density_maximizer_stationary_source_unrestricted H B θ S hS ht hmax

end MatrixSpencer.KSArbitraryTransportContact
