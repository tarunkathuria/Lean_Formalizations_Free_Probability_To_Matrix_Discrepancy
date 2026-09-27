import MatrixSpencer.KSDebitPreparedMargin
import MatrixSpencer.KSDebitSmoothness
import MatrixSpencer.KSLiveCurve
import MatrixSpencer.KSObjectiveUpper

/-!
# Explicit relative bounds for the actual KS owner source

The live-face owner path is quadratic in the real step parameter. Its source
therefore admits exact polynomial derivatives and, on an explicit margin-based
interval, relative matrix bounds that do not depend on any source eigenvalue.
These bounds remain valid after exact whitening on a fixed support.

The prepared-state specialization uses the existing endpoint-test accuracy
hypothesis only to derive the live margin. This module does not claim a fourth
derivative bound for the optimized potential or complete its numerical mesh.
-/

open Matrix Filter Topology Set
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section
namespace MatrixSpencer.KSOwnerRelativeSource

/-- A margin below the endpoint also bounds the quadratic owner from below. -/
theorem margin_le_quadratic_owner {x δ : ℝ} (hx : |x| ≤ 1)
    (hmargin : δ ≤ 1 - |x|) : δ ≤ 1 - x ^ 2 := by
  nlinarith [sq_abs x, abs_nonneg x, mul_nonneg (sub_nonneg.mpr hx) (abs_nonneg x)]

theorem owner_displacement_error {x s : ℝ} (hx : |x| ≤ 1) (hs : |s| ≤ 1) :
    |(1 - (x + s) ^ 2) - (1 - x ^ 2)| ≤ 3 * |s| := by
  have he : (1 - (x + s) ^ 2) - (1 - x ^ 2) = -(2 * x * s) - s ^ 2 := by ring
  rw [he]
  calc
    |-(2 * x * s) - s ^ 2| ≤ |2 * x * s| + |s ^ 2| := by
      simpa only [sub_zero, zero_sub, abs_neg] using abs_sub_le (-(2 * x * s)) 0 (s ^ 2)
    _ = 2 * |x| * |s| + |s| ^ 2 := by rw [abs_mul, abs_mul, abs_pow]; norm_num
    _ ≤ 3 * |s| := by nlinarith [abs_nonneg s, mul_le_mul_of_nonneg_right hx (abs_nonneg s)]

/-- Fully explicit relative owner bound, before multiplying by the owner
scale. It is valid for all real perturbations in the displayed radius. -/
theorem quadratic_owner_relative {x s δ r : ℝ} (hx : |x| ≤ 1)
    (hδ : 0 ≤ δ) (hmargin : δ ≤ 1 - |x|) (hr : 0 ≤ r) (hrone : r ≤ 1)
    (hs : |s| ≤ δ * r / 4) :
    (1 - r) * (1 - x ^ 2) ≤ 1 - (x + s) ^ 2 ∧
      1 - (x + s) ^ 2 ≤ (1 + r) * (1 - x ^ 2) := by
  have hδone : δ ≤ 1 := by linarith [abs_nonneg x]
  have hdr : δ * r ≤ 1 := (mul_le_mul hδone hrone hr (by norm_num)).trans (by norm_num)
  have hsone : |s| ≤ 1 := hs.trans (by linarith)
  have herror := owner_displacement_error hx hsone
  have hbase := margin_le_quadratic_owner hx hmargin
  have hrbase := mul_le_mul_of_nonneg_left hbase hr
  have hs3 : 3 * |s| ≤ r * (1 - x ^ 2) := by nlinarith [mul_nonneg hδ hr]
  rcases abs_le.mp (herror.trans hs3) with ⟨hl, hu⟩
  constructor <;> nlinarith

/-- A rational-arithmetic radius, defined only from the margin, desired
relative error, and a coordinate bound on the direction. -/
def relativeRadius (δ r d : ℝ) : ℝ := δ * r / (4 * (d + 1))

theorem relativeRadius_pos {δ r d : ℝ} (hδ : 0 < δ) (hr : 0 < r) (hd : 0 ≤ d) :
    0 < relativeRadius δ r d := by unfold relativeRadius; positivity

theorem displacement_le_of_radius {t h δ r d : ℝ}
    (hδ : 0 ≤ δ) (hr : 0 ≤ r) (hd : 0 ≤ d) (hh : |h| ≤ d)
    (ht : |t| ≤ relativeRadius δ r d) : |t * h| ≤ δ * r / 4 := by
  rw [abs_mul]
  calc |t| * |h| ≤ relativeRadius δ r d * d :=
      mul_le_mul ht hh (abs_nonneg _) (by unfold relativeRadius; positivity)
    _ ≤ δ * r / 4 := by
      unfold relativeRadius
      have hd1 : 0 < d + 1 := by positivity
      have hratio : d / (d + 1) ≤ 1 := (div_le_one hd1).mpr (by linarith)
      have hh := mul_le_mul_of_nonneg_left hratio (show 0 ≤ δ * r / 4 by positivity)
      calc
        δ * r / (4 * (d + 1)) * d = δ * r / 4 * (d / (d + 1)) := by
          simp only [div_eq_mul_inv, _root_.mul_inv_rev]
          ring
        _ ≤ δ * r / 4 * 1 := hh
        _ = δ * r / 4 := mul_one _

variable {ι n : Type*} [Fintype ι] [DecidableEq ι] [Fintype n] [DecidableEq n]
local instance {k : Type*} [Fintype k] [DecidableEq k] : CStarAlgebra (Matrix k k ℂ) := {}

/-- The existing source from the actual augmented Pauli family. -/
def source (A : ι → Matrix n n ℂ) (c : ι → ℝ)
    (S : Matrix (n ⊕ n) (n ⊕ n) ℂ) : Matrix (n ⊕ n) (n ⊕ n) ℂ :=
  covarianceSource (KSSpinSource.family A) (KSSpinSource.coefficientCovariance c) S

theorem source_smul (A : ι → Matrix n n ℂ) (c : ι → ℝ)
    (S : Matrix (n ⊕ n) (n ⊕ n) ℂ) (r : ℝ) :
    source A (fun i => r * c i) S = r • source A c S := by
  simp only [source, KSSpinSource.source_eq_pauli_sum, Finset.smul_sum, smul_smul]
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  ring_nf

/-- Monotonicity in the actual owners, with no source rank assumption. -/
theorem source_mono (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).IsHermitian)
    {c e : ι → ℝ} (hce : ∀ i, c i ≤ e i)
    {S : Matrix (n ⊕ n) (n ⊕ n) ℂ} (hS : S.PosSemidef) :
    source A c S ≤ source A e S := by
  simp only [source, KSSpinSource.source_eq_pauli_sum]
  apply Finset.sum_le_sum
  intro i _
  apply smul_le_smul_of_nonneg_right (div_le_div_of_nonneg_right (hce i) (by norm_num))
  apply Finset.sum_nonneg
  intro a _
  have hp := hS.conjTranspose_mul_mul_same (KSSpinSource.pauli (A i) a)
  simpa only [(KSSpinSource.pauli_isHermitian (hA i) a).eq] using hp.nonneg

theorem source_posSemidef (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).IsHermitian)
    {c : ι → ℝ} (hc : ∀ i, 0 ≤ c i)
    {S : Matrix (n ⊕ n) (n ⊕ n) ℂ} (hS : S.PosSemidef) : (source A c S).PosSemidef :=
  covarianceSource_posSemidef _ (KSSpinSource.family_isHermitian A hA)
    (KSSpinSource.coefficientCovariance_posSemidef hc) hS

omit [DecidableEq n] in
/-- Exact whitening preserves the relative bound without introducing the
norm of the whitening matrix or a smallest-eigenvalue factor. -/
theorem whitened_norm_le_of_relative_order {m : Type*} [Fintype m] [DecidableEq m]
    {P Q : Matrix (n ⊕ n) (n ⊕ n) ℂ} (hP : P.IsHermitian) (hQ : Q.IsHermitian)
    (V : Matrix (n ⊕ n) m ℂ) (hV : Vᴴ * P * V = 1) {r : ℝ} (hr : 0 ≤ r)
    (hl : (1-r) • P ≤ Q) (hu : Q ≤ (1+r) • P) :
    ‖Vᴴ * (Q-P) * V‖ ≤ r := by
  have hherm : (Vᴴ * (Q-P) * V).IsHermitian := by
    simpa only [Matrix.conjTranspose_conjTranspose] using
      Matrix.isHermitian_mul_mul_conjTranspose Vᴴ (hQ.sub hP)
  apply KrausContraction.norm_le_of_order_interval hherm hr
  · have hl' : -r • P ≤ Q-P := by
      have hh := sub_le_sub_right hl P
      convert hh using 1; module
    have hh := KSFidelityUpper.compression_mono V hl'
    simpa only [Matrix.mul_smul, Matrix.smul_mul, hV] using hh
  · have hu' : Q-P ≤ r • P := by
      have hh := sub_le_sub_right hu P
      convert hh using 1; module
    have hh := KSFidelityUpper.compression_mono V hu'
    simpa only [Matrix.mul_smul, Matrix.smul_mul, hV] using hh

/-- Coefficientwise relative owner bounds give the same matrix relative
source bound, independently of all source eigenvalues. -/
theorem source_relative_of_owner_bounds (A : ι → Matrix n n ℂ)
    (hA : ∀ i, (A i).IsHermitian) {c e : ι → ℝ} {r : ℝ}
    (hc : ∀ i, (1-r) * c i ≤ e i ∧ e i ≤ (1+r) * c i)
    {S : Matrix (n ⊕ n) (n ⊕ n) ℂ} (hS : S.PosSemidef) :
    (1-r) • source A c S ≤ source A e S ∧ source A e S ≤ (1+r) • source A c S := by
  constructor
  · rw [← source_smul]
    exact source_mono A hA (fun i => (hc i).1) hS
  · rw [← source_smul]
    exact source_mono A hA (fun i => (hc i).2) hS

theorem source_add (A : ι → Matrix n n ℂ) (c e : ι → ℝ)
    (S : Matrix (n ⊕ n) (n ⊕ n) ℂ) :
    source A (fun i => c i + e i) S = source A c S + source A e S := by
  simp only [source, KSSpinSource.source_eq_pauli_sum, add_div, add_smul, Finset.sum_add_distrib]

theorem source_density_add (A : ι → Matrix n n ℂ) (c : ι → ℝ)
    (S T : Matrix (n ⊕ n) (n ⊕ n) ℂ) :
    source A c (S + T) = source A c S + source A c T := by
  simp only [source, KSSpinSource.source_eq_pauli_sum, Matrix.mul_add, Matrix.add_mul,
    Finset.sum_add_distrib, smul_add]

theorem source_density_smul (A : ι → Matrix n n ℂ) (c : ι → ℝ)
    (S : Matrix (n ⊕ n) (n ⊕ n) ℂ) (r : ℝ) :
    source A c (r • S) = r • source A c S := by
  simp only [source, KSSpinSource.source_eq_pauli_sum, Matrix.mul_smul, Matrix.smul_mul,
    Finset.smul_sum, smul_smul]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro a _
  congr 1
  ring

variable {N : ℕ}
open KSPotentialModels KSLiveCurve

def ownerLinear (u : ℝ) (x k : Fin N → ℝ) : Fin N → ℝ := fun i => -2 * u * x i * k i

def ownerQuadratic (u : ℝ) (k : Fin N → ℝ) : Fin N → ℝ := fun i => -u * (k i) ^ 2

/-- Exact polynomial expansion of the actual source, retaining all original
labels and the frozen zero directions. No remainder estimate is assumed. -/
theorem source_path_expansion (A : Fin N → Matrix n n ℂ) (u : ℝ)
    (x : Fin N → ℝ) (h : Live 1 x → ℝ) (t : ℝ)
    (S : Matrix (n ⊕ n) (n ⊕ n) ℂ) :
    source A (naturalOwners u (path 1 x h t)) S =
      source A (naturalOwners u x) S +
        t • source A (ownerLinear u x (extend 1 x h)) S +
        t ^ 2 • source A (ownerQuadratic u (extend 1 x h)) S := by
  have he : naturalOwners u (path 1 x h t) = fun i =>
      naturalOwners u x i + t * ownerLinear u x (extend 1 x h) i +
        t ^ 2 * ownerQuadratic u (extend 1 x h) i := by
    funext i
    simp only [naturalOwners, path, ownerLinear, ownerQuadratic]
    ring
  rw [he, source_add, source_add, source_smul, source_smul]

/-- The first source derivative is the derivative of the actual coefficient
path, not a supplied derivative oracle. -/
theorem hasDerivAt_source_path (A : Fin N → Matrix n n ℂ) (u : ℝ)
    (x : Fin N → ℝ) (h : Live 1 x → ℝ)
    (S : Matrix (n ⊕ n) (n ⊕ n) ℂ) (t : ℝ) :
    HasDerivAt (fun z => source A (naturalOwners u (path 1 x h z)) S)
      (source A (ownerLinear u x (extend 1 x h)) S +
        (2 * t) • source A (ownerQuadratic u (extend 1 x h)) S) t := by
  simp_rw [source_path_expansion]
  convert ((hasDerivAt_const t (source A (naturalOwners u x) S)).add
    ((hasDerivAt_id t).smul_const (source A (ownerLinear u x (extend 1 x h)) S))).add
    (((hasDerivAt_id t).pow 2).smul_const (source A (ownerQuadratic u (extend 1 x h)) S)) using 1; simp

theorem hasDerivAt_deriv_source_path (A : Fin N → Matrix n n ℂ) (u : ℝ)
    (x : Fin N → ℝ) (h : Live 1 x → ℝ)
    (S : Matrix (n ⊕ n) (n ⊕ n) ℂ) (t : ℝ) :
    HasDerivAt (deriv (fun z => source A (naturalOwners u (path 1 x h z)) S))
      ((2 : ℝ) • source A (ownerQuadratic u (extend 1 x h)) S) t := by
  rw [show deriv (fun z => source A (naturalOwners u (path 1 x h z)) S) =
    (fun z => source A (ownerLinear u x (extend 1 x h)) S +
      (2 * z) • source A (ownerQuadratic u (extend 1 x h)) S) from
        funext (fun z => (hasDerivAt_source_path A u x h S z).deriv)]
  convert (hasDerivAt_const t (source A (ownerLinear u x (extend 1 x h)) S)).add
    (((hasDerivAt_id t).const_mul 2).smul_const (source A (ownerQuadratic u (extend 1 x h)) S)) using 1; simp

/-- Exact second derivative; the quadratic coefficient already includes
its negative sign. -/
theorem iteratedDeriv_source_path_two (A : Fin N → Matrix n n ℂ) (u : ℝ)
    (x : Fin N → ℝ) (h : Live 1 x → ℝ)
    (S : Matrix (n ⊕ n) (n ⊕ n) ℂ) (t : ℝ) :
    iteratedDeriv 2 (fun z => source A (naturalOwners u (path 1 x h z)) S) t =
      (2 : ℝ) • source A (ownerQuadratic u (extend 1 x h)) S := by
  rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one]
  exact (hasDerivAt_deriv_source_path A u x h S t).deriv

/-- Every third derivative of the actual fixed-density source curve vanishes. -/
theorem iteratedDeriv_source_path_three (A : Fin N → Matrix n n ℂ) (u : ℝ)
    (x : Fin N → ℝ) (h : Live 1 x → ℝ)
    (S : Matrix (n ⊕ n) (n ⊕ n) ℂ) (t : ℝ) :
    iteratedDeriv 3 (fun z => source A (naturalOwners u (path 1 x h z)) S) t = 0 := by
  rw [show (3 : ℕ) = 2 + 1 from rfl, iteratedDeriv_succ]
  rw [show iteratedDeriv 2 (fun z => source A (naturalOwners u (path 1 x h z)) S) =
    (fun _ => (2 : ℝ) • source A (ownerQuadratic u (extend 1 x h)) S) from
      funext (fun z => iteratedDeriv_source_path_two A u x h S z)]
  exact deriv_const t _

/-- Exact cubic expansion when the physical density also moves affinely. -/
theorem source_path_densityLine_expansion (A : Fin N → Matrix n n ℂ) (u : ℝ)
    (x : Fin N → ℝ) (h : Live 1 x → ℝ) (t : ℝ)
    (S T : Matrix (n ⊕ n) (n ⊕ n) ℂ) :
    source A (naturalOwners u (path 1 x h t)) (S + t • T) =
      source A (naturalOwners u x) S +
      t • (source A (ownerLinear u x (extend 1 x h)) S + source A (naturalOwners u x) T) +
      t ^ 2 • (source A (ownerQuadratic u (extend 1 x h)) S +
        source A (ownerLinear u x (extend 1 x h)) T) +
      t ^ 3 • source A (ownerQuadratic u (extend 1 x h)) T := by
  rw [source_density_add, source_density_smul, source_path_expansion, source_path_expansion]
  module

/-- The actual owner weights along a live-face path obey the explicit
relative bound; every frozen zero owner is retained exactly. -/
theorem naturalOwners_path_relative {x : Fin N → ℝ} (hx : x ∈ ksCube 1)
    {u δ r d : ℝ} (hu : 0 ≤ u) (hδ : 0 ≤ δ) (hr : 0 ≤ r) (hrone : r ≤ 1) (hd : 0 ≤ d)
    (hmargin : ∀ i : Live 1 x, δ ≤ 1 - |x i|)
    (h : Live 1 x → ℝ) (hdir : ∀ i, |h i| ≤ d) {t : ℝ}
    (ht : |t| ≤ relativeRadius δ r d) (i : Fin N) :
    (1-r) * naturalOwners u x i ≤ naturalOwners u (path 1 x h t) i ∧
      naturalOwners u (path 1 x h t) i ≤ (1+r) * naturalOwners u x i := by
  by_cases hi : |x i| < 1
  · let j : Live 1 x := ⟨i, hi⟩
    have hs := displacement_le_of_radius hδ hr hd (hdir j) ht
    have hb := quadratic_owner_relative (abs_le.mpr ⟨hx.1 i, hx.2 i⟩)
      hδ (hmargin j) hr hrone hs
    have hp : path 1 x h t i = x i + t * h j := path_live 1 x h t j
    simp only [naturalOwners, hp]
    constructor
    · nlinarith [mul_le_mul_of_nonneg_left hb.1 hu]
    · nlinarith [mul_le_mul_of_nonneg_left hb.2 hu]
  · have hp := path_dead 1 x h t i hi
    rw [show naturalOwners u (path 1 x h t) i = naturalOwners u x i by simp only [naturalOwners, hp],
      naturalOwner_dead hx u i hi]
    simp

/-- Quantitative source continuity along the genuine live-face coefficient
path, at every PSD density and for an arbitrary Hermitian atom family. -/
theorem source_path_relative (A : Fin N → Matrix n n ℂ)
    (hA : ∀ i, (A i).IsHermitian) {x : Fin N → ℝ} (hx : x ∈ ksCube 1)
    {u δ r d : ℝ} (hu : 0 ≤ u) (hδ : 0 ≤ δ) (hr : 0 ≤ r) (hrone : r ≤ 1) (hd : 0 ≤ d)
    (hmargin : ∀ i : Live 1 x, δ ≤ 1 - |x i|)
    (h : Live 1 x → ℝ) (hdir : ∀ i, |h i| ≤ d) {t : ℝ}
    (ht : |t| ≤ relativeRadius δ r d)
    {S : Matrix (n ⊕ n) (n ⊕ n) ℂ} (hS : S.PosSemidef) :
    (1-r) • source A (naturalOwners u x) S ≤ source A (naturalOwners u (path 1 x h t)) S ∧
      source A (naturalOwners u (path 1 x h t)) S ≤ (1+r) • source A (naturalOwners u x) S :=
  source_relative_of_owner_bounds A hA
    (naturalOwners_path_relative hx hu hδ hr hrone hd hmargin h hdir ht) hS

/-- The actual changed source is within `r` after any exact whitening of
its base source on a fixed support. No source eigenvalue bound is assumed. -/
theorem whitened_source_path_norm_le {m : Type*} [Fintype m] [DecidableEq m]
    (A : Fin N → Matrix n n ℂ) (hA : ∀ i, (A i).IsHermitian)
    {x : Fin N → ℝ} (hx : x ∈ ksCube 1)
    {u δ r d : ℝ} (hu : 0 ≤ u) (hδ : 0 ≤ δ) (hr : 0 ≤ r) (hrone : r ≤ 1) (hd : 0 ≤ d)
    (hmargin : ∀ i : Live 1 x, δ ≤ 1 - |x i|)
    (h : Live 1 x → ℝ) (hdir : ∀ i, |h i| ≤ d) {t : ℝ}
    (ht : |t| ≤ relativeRadius δ r d)
    {S : Matrix (n ⊕ n) (n ⊕ n) ℂ} (hS : S.PosSemidef)
    (V : Matrix (n ⊕ n) m ℂ) (hV : Vᴴ * source A (naturalOwners u x) S * V = 1) :
    ‖Vᴴ * (source A (naturalOwners u (path 1 x h t)) S - source A (naturalOwners u x) S) * V‖ ≤ r := by
  have hc := naturalOwners_nonneg hu le_rfl hx
  have he : ∀ i, 0 ≤ naturalOwners u (path 1 x h t) i := by
    intro i
    exact (mul_nonneg (sub_nonneg.mpr hrone) (hc i)).trans
      (naturalOwners_path_relative hx hu hδ hr hrone hd hmargin h hdir ht i).1
  have hh := source_path_relative A hA hx hu hδ hr hrone hd hmargin h hdir ht hS
  exact whitened_norm_le_of_relative_order (source_posSemidef A hA hc hS).isHermitian
    (source_posSemidef A hA he hS).isHermitian V hV hr hh.1 hh.2

/-- The explicitly chosen radius also keeps each live point at a positive
margin. This is stronger than merely eventual face preservation. -/
theorem path_margin {x : Fin N → ℝ}
    {δ r d : ℝ} (hδ : 0 ≤ δ) (hr : 0 ≤ r) (hrone : r ≤ 1) (hd : 0 ≤ d)
    (hmargin : ∀ i : Live 1 x, δ ≤ 1 - |x i|)
    (h : Live 1 x → ℝ) (hdir : ∀ i, |h i| ≤ d) {t : ℝ}
    (ht : |t| ≤ relativeRadius δ r d) (i : Live 1 x) :
    δ / 2 ≤ 1 - |path 1 x h t i| := by
  have hs := displacement_le_of_radius hδ hr hd (hdir i) ht
  have ha := abs_add_le (x i) (t * h i)
  rw [path_live]
  have hm := hmargin i
  nlinarith [mul_le_mul_of_nonneg_left hrone hδ]

/-- The source estimate for the actual output of the finite preparation
loop. Its live margin is derived from the endpoint tests. -/
theorem prepared_source_relative [Nonempty n]
    (v : Fin N → n → ℂ) {δ η θ r d : ℝ} (hδ : 0 ≤ δ) (hη : 0 ≤ η) (hθ : 0 < θ)
    (hr : 0 ≤ r) (hrone : r ≤ 1) (hd : 0 ≤ d)
    (report : (Fin N → ℝ) → ℝ)
    (haccuracy : ∀ z ∈ ksCube 1, |report z - KSDebitPreparation.statePotential v δ η θ z| ≤ η / 8)
    {x : Fin N → ℝ} (hx : x ∈ ksCube 1)
    (h : Live 1 (KSDebitPreparation.prepare η report x) → ℝ) (hdir : ∀ i, |h i| ≤ d)
    {t : ℝ} (ht : |t| ≤ relativeRadius δ r d)
    {S : Matrix (n ⊕ n) (n ⊕ n) ℂ} (hS : S.PosSemidef) :
    let y := KSDebitPreparation.prepare η report x
    (1-r) • source (fun i => KSRankOne.atom (v i)) (naturalOwners 64 y) S ≤
      source (fun i => KSRankOne.atom (v i)) (naturalOwners 64 (path 1 y h t)) S ∧
    source (fun i => KSRankOne.atom (v i)) (naturalOwners 64 (path 1 y h t)) S ≤
      (1+r) • source (fun i => KSRankOne.atom (v i)) (naturalOwners 64 y) S := by
  apply source_path_relative _ (fun i => KSRankOne.atom_isHermitian (v i))
    (KSDebitPreparation.prepare_mem_cube η report hx) (by norm_num) hδ hr hrone hd _ h hdir ht hS
  intro i
  exact (KSDebitPreparedMargin.prepared_live_margin v hδ hη hθ report haccuracy hx i i.property).le

end MatrixSpencer.KSOwnerRelativeSource
