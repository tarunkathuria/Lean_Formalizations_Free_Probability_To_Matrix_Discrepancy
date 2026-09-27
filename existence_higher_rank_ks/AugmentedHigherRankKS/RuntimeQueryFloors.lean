import AugmentedHigherRankKS.FourBlockQueryDomain
import AugmentedHigherRankKS.RuntimeParameters

/-! The runtime's named scalar parameters instantiated in the actual optimizer bounds. -/
noncomputable section
open Matrix MatrixSpencer HigherRankKS Set
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator
namespace AugmentedHigherRankKS
variable {ι n : Type*} [Fintype ι] [Fintype n] [DecidableEq n]
local instance runtimeQueryCStar {j : Type*} [Fintype j] [DecidableEq j] :
  CStarAlgebra (Matrix j j ℂ) := {}
open RuntimeParameters

theorem runtime_query_floors (z : Dimensions) (hz : z ∈ Domain)
    (hd : (Fintype.card n : ℝ) ≤ z.D)
    (H : Matrix (FourSpin n) (FourSpin n) ℂ) (hH : H.IsHermitian) (hH8 : ‖H‖ ≤ 8)
    (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).PosSemidef) (hsum : ∑ i, A i ≤ 1)
    {ε : ℝ} (hε : 0 ≤ ε) (hε1 : ε ≤ 1) (hN : ∀ i, ‖A i‖ ≤ ε)
    {r : ℕ} (hr : ∀ i, (A i).rank ≤ r) (k : ℕ) (hk : 1 ≤ k)
    (hrβ : (r:ℝ)^((1:ℝ)/2^k) ≤ 2)
    (c : ι → ℝ) (hc : ∀ i, 0 < c i) (hccap : ∀ i, c i ≤ 8*a z)
    (S : selfAdjoint (Matrix (FourSpin n) (FourSpin n) ℂ))
    (hS : (S : Matrix (FourSpin n) (FourSpin n) ℂ).PosDef)
    (ht : realTrace (S : Matrix (FourSpin n) (FourSpin n) ℂ) = 1)
    (hmax : ∀ U ∈ densitySet, objective H A ((1:ℝ)/2^k) c (theta z) U ≤ objective H A ((1:ℝ)/2^k) c (theta z) S) :
    s0 z • (1 : Matrix (FourSpin n) (FourSpin n) ℂ) ≤ (S : Matrix (FourSpin n) (FourSpin n) ℂ) ∧
    (Bbar z)⁻¹ • (1 : Matrix (SourceCarrierIndex A) (SourceCarrierIndex A) ℂ) ≤
      SupportedSpin.transport A ((1:ℝ)/2^k) c S ∧
    (∀ i, s0 z*realTrace (A i) ≤ BalancedFrames.carrierMass
      (SupportedSpin.probe A) (SupportedSpin.density A S) i) ∧
    (∀ i, 4*s0 z*realTrace (A i*A i)/(Bbar z) ≤ BalancedFrames.transportMass
      (SupportedSpin.term A ((1:ℝ)/2^k) S) (SupportedSpin.transport A ((1:ℝ)/2^k) c S) i) := by
  have ha : 1 ≤ a z := by linarith [a_ge z hz]
  have hsize : z.D ≤ size z := by
    have hN := hz.1
    have hq := hz.2.2
    dsimp only [size]
    linarith
  exact query_optimizer_floors H hH hH8 A hA hsum hε hε1 hN hr k hk hrβ
    ha (size_one z hz) (hd.trans hsize) (theta_poly.positive z hz) (theta_le_one z hz)
    c hc hccap S hS ht hmax

theorem runtime_query_probe_floors (z : Dimensions) (hz : z ∈ Domain)
    (hd : (Fintype.card n : ℝ) ≤ z.D)
    (H : Matrix (FourSpin n) (FourSpin n) ℂ) (hH : H.IsHermitian) (hH8 : ‖H‖ ≤ 8)
    (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).PosSemidef) (hsum : ∑ i, A i ≤ 1)
    {ε : ℝ} (hε : 0 ≤ ε) (hε1 : ε ≤ 1) (hN : ∀ i, ‖A i‖ ≤ ε)
    {r : ℕ} (hr : ∀ i, (A i).rank ≤ r) (k : ℕ) (hk : 1 ≤ k)
    (hrβ : (r:ℝ)^((1:ℝ)/2^k) ≤ 2)
    (c : ι → ℝ) (hc : ∀ i, 0 < c i) (hccap : ∀ i, c i ≤ 8*a z)
    (S : selfAdjoint (Matrix (FourSpin n) (FourSpin n) ℂ))
    (hS : (S : Matrix (FourSpin n) (FourSpin n) ℂ).PosDef)
    (ht : realTrace (S : Matrix (FourSpin n) (FourSpin n) ℂ) = 1)
    (hmax : ∀ U ∈ densitySet, objective H A ((1:ℝ)/2^k) c (theta z) U ≤ objective H A ((1:ℝ)/2^k) c (theta z) S)
    (i : ι) (hi : eta z ≤ ‖A i‖) :
    p0 z ≤ BalancedFrames.carrierMass (SupportedSpin.probe A) (SupportedSpin.density A S) i ∧
    tau0 z ≤ BalancedFrames.transportMass (SupportedSpin.term A ((1:ℝ)/2^k) S)
      (SupportedSpin.transport A ((1:ℝ)/2^k) c S) i := by
  obtain ⟨hs,hZ,_,_⟩ := runtime_query_floors z hz hd H hH hH8 A hA hsum hε hε1 hN hr
    k hk hrβ c hc hccap S hS ht hmax
  exact ⟨carrierMass_floor_of_norm A hA (s0_poly.positive z hz).le hs i hi,
    transportMass_floor_of_norm A hA k hk c hS (s0_poly.positive z hz).le
      (Bbar_poly.positive z hz) (theta_poly.positive z hz).le hs hZ i hi⟩

/-- Positive optimizer and base-fidelity bounds are consequences of the input, not primitive reports. -/
theorem exists_runtime_query_optimizer [Nonempty n]
    (z : Dimensions) (hz : z ∈ Domain) (hd : (Fintype.card n : ℝ) ≤ z.D)
    (H : Matrix (FourSpin n) (FourSpin n) ℂ) (hH : H.IsHermitian) (hH8 : ‖H‖ ≤ 8)
    (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).PosSemidef) (hsum : ∑ i, A i ≤ 1)
    {ε : ℝ} (hε : 0 ≤ ε) (hε1 : ε ≤ 1) (hN : ∀ i, ‖A i‖ ≤ ε)
    {r : ℕ} (hr : ∀ i, (A i).rank ≤ r) (k : ℕ) (hk : 1 ≤ k)
    (hrβ : (r:ℝ)^((1:ℝ)/2^k) ≤ 2)
    (c : ι → ℝ) (hc : ∀ i, 0 < c i) (hccap : ∀ i, c i ≤ 8*a z) :
    ∃ S : selfAdjoint (Matrix (FourSpin n) (FourSpin n) ℂ),
      (S : Matrix (FourSpin n) (FourSpin n) ℂ).PosDef ∧ realTrace (S : Matrix (FourSpin n) (FourSpin n) ℂ) = 1 ∧
      (∀ U ∈ densitySet, objective H A ((1:ℝ)/2^k) c (theta z) U ≤ objective H A ((1:ℝ)/2^k) c (theta z) S) ∧
      s0 z • (1 : Matrix (FourSpin n) (FourSpin n) ℂ) ≤ (S : Matrix (FourSpin n) (FourSpin n) ℂ) ∧
      fidelity S (source A ((1:ℝ)/2^k) c S) ≤ C0 z := by
  have hb : (1:ℝ)/2^k < 1 := (div_lt_one (by positivity)).mpr
    (one_lt_pow₀ (by norm_num) (by omega))
  obtain ⟨M,⟨hM,hMp,hmax⟩,_⟩ := existsUnique_faithful_optimizer H A (by positivity) hb
    (fun i => (hc i).le) (theta_poly.positive z hz)
  let S : selfAdjoint (Matrix (FourSpin n) (FourSpin n) ℂ) := ⟨M,hMp.isHermitian⟩
  have hf := runtime_query_floors z hz hd H hH hH8 A hA hsum hε hε1 hN hr k hk hrβ
    c hc hccap S hMp hM.2 hmax
  exact ⟨S,hMp,hM.2,hmax,hf.1,fidelity_query_bound A hA hsum hε hε1 hN hr
    (by positivity) hb hrβ (a_poly.positive z hz).le (fun i => (hc i).le) hccap hM⟩
/-- Every centered value query lies in the proved input domain. -/
theorem runtime_quadratic_query_domain [DecidableEq ι] [Nonempty n]
    (z : Dimensions) (hz : z ∈ Domain)
    (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).PosSemidef) (hsum : ∑ i, A i ≤ 1)
    (H : Matrix (FourSpin n) (FourSpin n) ℂ) (hH : ‖H‖ ≤ 5)
    (x : ι → ℝ) (hx : ∀ i, |x i| ≤ 1)
    (c : ι → ℝ) (hc : ∀ i, 2*zeta z ≤ c i) (hcu : ∀ i, c i ≤ 4*a z)
    (u : EuclideanSpace ℝ ι) (hu : ‖u‖ ≤ radius z) :
    ‖H+∑ i, u i • forceAtom (x i) (A i)‖ ≤ 8 ∧
      (∀ i, zeta z ≤ c i-a z*(u i)^2 ∧ c i-a z*(u i)^2 ≤ 8*a z) :=
  quadratic_query_bounds A hA hsum H hH x hx (a_poly.positive z hz)
    (theta_poly.positive z hz).le (theta_le_one z hz) c hc hcu u hu

/-- Every forward preparation query lies in the same proved domain. -/
theorem runtime_preparation_query_domain [DecidableEq ι] [Nonempty n]
    (z : Dimensions) (hz : z ∈ Domain)
    (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).PosSemidef) (hN : ∀ i, ‖A i‖ ≤ 1)
    (H : Matrix (FourSpin n) (FourSpin n) ℂ) (hH : ‖H‖ ≤ 5)
    (c : ι → ℝ) (hc : ∀ i, 2*zeta z ≤ c i) (hcu : ∀ i, c i ≤ 4*a z)
    (i : ι) {t : ℝ} (ht : 0 ≤ t) (htu : t ≤ prep z) :
    ‖H+augmentedCenter 0 ((t/a z) • A i)‖ ≤ 8 ∧
      (∀ j, zeta z ≤ c j-(Pi.single i t : ι → ℝ) j ∧ c j-(Pi.single i t : ι → ℝ) j ≤ 8*a z) :=
  preparation_query_bounds A hA hN H hH (by linarith [a_ge z hz])
    (theta_poly.positive z hz).le (theta_le_one z hz) ht (htu.trans (prep_le_zeta z)) c hc hcu i

end AugmentedHigherRankKS
