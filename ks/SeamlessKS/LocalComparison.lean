import SeamlessKS.SourceTransport
import MatrixSpencer.KSSpinChosenRetirement
import MatrixSpencer.KSDebitPotential

/-!
# Certified local movement with partial scalar-source reduction

Only one weight is reduced, to an arbitrary nonnegative value. No endpoint
assignment occurs in these theorems: the center moves by the supplied local
increment, paid for by exactly the source loss on that same increment.
-/

open Matrix
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section
namespace SeamlessKS.LocalComparison

open MatrixSpencer MatrixSpencer.KSRankOne MatrixSpencer.KSEndpointRetirement

variable {ι n m : Type*} [Fintype ι] [Fintype n] [Fintype m]
  [DecidableEq ι] [DecidableEq n] [DecidableEq m]
local instance {k : Type*} [Fintype k] [DecidableEq k] : CStarAlgebra (Matrix k k ℂ) := {}

omit [Fintype ι] in
theorem update_nonneg {c : ι → ℝ} (hc : ∀ j, 0 ≤ c j)
    (i : ι) {d : ℝ} (hd : 0 ≤ d) : ∀ j, 0 ≤ Function.update c i d j := by
  intro j
  by_cases hj : j = i
  · subst j
    simpa only [Function.update_self] using hd
  · simpa only [Function.update_of_ne hj] using hc j

theorem covariance_update_le (c : ι → ℝ) (i : ι) {d : ℝ} (hd : d ≤ c i) :
    KSSpinSource.coefficientCovariance (Function.update c i d) ≤
      KSSpinSource.coefficientCovariance c := by
  apply Matrix.le_iff.mpr
  rw [KSSpinSource.coefficientCovariance, KSSpinSource.coefficientCovariance,
    Matrix.diagonal_sub]
  apply Matrix.posSemidef_diagonal_iff.mpr
  intro j
  by_cases hj : j.1 = i
  · change 0 ≤ c j.1 / 2 - Function.update c i d j.1 / 2
    rw [hj, Function.update_self]
    linarith
  · simp [Function.update_of_ne hj]

theorem weighted_sum_update {E : Type*} [AddCommGroup E] [Module ℝ E]
    (c : ι → ℝ) (A : ι → E) (i : ι) (d : ℝ) :
    (∑ j, Function.update c i d j • A j) = ∑ j, c j • A j - (c i - d) • A i := by
  have he : (∑ j, Function.update c i d j • A j) - (∑ j, c j • A j) =
      (d - c i) • A i := by
    rw [← Finset.sum_sub_distrib, Finset.sum_eq_single i]
    · simp only [Function.update_self, sub_smul]
    · intro j _ hji
      simp only [Function.update_of_ne hji, sub_self]
    · simp
  have hneg : (d - c i) • A i = -((c i - d) • A i) := by
    rw [← neg_smul]
    congr 1
    ring
  rw [hneg] at he
  exact sub_eq_iff_eq_add.mp he |>.trans (by abel)

theorem source_update (v : ι → n → ℂ) (c : ι → ℝ) (i : ι) (d : ℝ)
    {W : Matrix (n ⊕ n) (n ⊕ n) ℂ} (hW : W.IsHermitian) :
    covarianceSource (KSSpinSource.family (fun j => atom (v j)))
      (KSSpinSource.coefficientCovariance (Function.update c i d)) W =
    covarianceSource (KSSpinSource.family (fun j => atom (v j)))
      (KSSpinSource.coefficientCovariance c) W -
      ((c i - d) * realTrace (KSSpinSource.doubled (atom (v i)) * W)) •
        KSSpinSource.doubled (atom (v i)) := by
  rw [KSSpinSource.source_eq_tracePrepare_real v _ hW,
    KSSpinSource.source_eq_tracePrepare_real v _ hW]
  simpa only [smul_smul] using weighted_sum_update c
    (fun j => realTrace (KSSpinSource.doubled (atom (v j)) * W) •
      KSSpinSource.doubled (atom (v j))) i d

/-- A finite local displacement is paid for by its own partial source loss. -/
theorem local_move_in_frame [Nonempty n]
    (H : Matrix (n ⊕ n) (n ⊕ n) ℂ) (v : ι → n → ℂ)
    (c : ι → ℝ) (hc : ∀ j, 0 ≤ c j) (V : Matrix (n ⊕ n) m ℂ)
    (hV : Vᴴ * V = 1) {θ : ℝ} (hθ : 0 < θ)
    (S : selfAdjoint (Matrix (n ⊕ n) (n ⊕ n) ℂ))
    (hS : (S : Matrix (n ⊕ n) (n ⊕ n) ℂ).PosDef)
    (ht : realTrace (S : Matrix (n ⊕ n) (n ⊕ n) ℂ) = 1)
    (hmax : ∀ T ∈ densitySet,
      densityObjective H (covarianceKraus (KSSpinSource.family (fun j => atom (v j)))
        (KSSpinSource.coefficientCovariance c)) θ T ≤
      densityObjective H (covarianceKraus (KSSpinSource.family (fun j => atom (v j)))
        (KSSpinSource.coefficientCovariance c)) θ S)
    {Z : Matrix m m ℂ} (hZ : Z.PosDef)
    (hM : (Vᴴ * covarianceSource (KSSpinSource.family (fun j => atom (v j)))
      (KSSpinSource.coefficientCovariance c) S * V).PosDef)
    (hsolve : Z * (Vᴴ * covarianceSource (KSSpinSource.family (fun j => atom (v j)))
      (KSSpinSource.coefficientCovariance c) S * V) * Z =
        Vᴴ * (S : Matrix (n ⊕ n) (n ⊕ n) ℂ) * V)
    (hsupport : ∀ X : Matrix (n ⊕ n) (n ⊕ n) ℂ, X.PosSemidef →
      V * (Vᴴ * covarianceSource (KSSpinSource.family (fun j => atom (v j)))
        (KSSpinSource.coefficientCovariance c) X * V) * Vᴴ =
        covarianceSource (KSSpinSource.family (fun j => atom (v j)))
          (KSSpinSource.coefficientCovariance c) X)
    (i : ι) (t d : ℝ) (hd : 0 ≤ d) (hdc : d ≤ c i)
    (hsafe : |t| ≤ (c i - d) *
      realTrace (KSSpinSource.doubled (atom (v i)) * (V * Z * Vᴴ))) :
    ownerPotential (H + t • signedLift (atom (v i)))
      (KSSpinSource.family (fun j => atom (v j)))
      (KSSpinSource.coefficientCovariance (Function.update c i d)) θ ≤
    ownerPotential H (KSSpinSource.family (fun j => atom (v j)))
      (KSSpinSource.coefficientCovariance c) θ := by
  have hA := KSSpinSource.family_isHermitian (fun j => atom (v j)) (fun j => atom_isHermitian _)
  have hC := KSSpinSource.coefficientCovariance_posSemidef hc
  have he (X : Matrix (n ⊕ n) (n ⊕ n) ℂ) := covarianceSource_eq_kraus _ hA hC X
  apply KSArbitraryRetirement.owner_retire_of_supported_matrix_le H _ _ hA hC
    (KSSpinSource.coefficientCovariance_posSemidef (update_nonneg hc i hd))
    (covariance_update_le c i hdc) V hV hθ S hS ht hmax hZ
  · simpa only [← he] using hM
  · simpa only [← he] using hsolve
  · intro X hX
    simpa only [← he] using hsupport X hX
  · rw [source_update v c i d (Matrix.isHermitian_mul_mul_conjTranspose V hZ.isHermitian)]
    have hstep := spin_step_le (atom_posSemidef (v i)) hsafe
    have hsum := add_le_add_left (sub_nonpos.mpr hstep)
      (H + covarianceSource (KSSpinSource.family (fun j => atom (v j)))
        (KSSpinSource.coefficientCovariance c) (V * Z * Vᴴ))
    simp only [add_zero] at hsum
    convert hsum using 1
    abel

/-- The exact maximizing full density, selected by compact attainment. -/
def optimizer [Nonempty n] (H : Matrix (n ⊕ n) (n ⊕ n) ℂ)
    (v : ι → n → ℂ) (c : ι → ℝ) (θ : ℝ) :=
  densityOptimizer H (covarianceKraus (KSSpinSource.family (fun j => atom (v j)))
    (KSSpinSource.coefficientCovariance c)) θ

/-- A local comparison for the actual optimizer and actual source support.
All support, optimizer, and transport premises are proved internally. -/
theorem local_move [Nonempty n]
    (H : Matrix (n ⊕ n) (n ⊕ n) ℂ) (v : ι → n → ℂ)
    (c : ι → ℝ) (hc : ∀ j, 0 < c j) {θ : ℝ} (hθ : 0 < θ)
    (i : ι) (t d : ℝ) (hd : 0 ≤ d) (hdc : d ≤ c i)
    (hsafe : |t| ≤ (c i - d) * realTrace
      (SourceTransport.stateTransport v c (optimizer H v c θ) *
        KSSpinCompression.compressedAtom (KSSpinLocalState.atoms v) i)) :
    ownerPotential (H + t • signedLift (atom (v i)))
      (KSSpinSource.family (KSSpinLocalState.atoms v))
      (KSSpinSource.coefficientCovariance (Function.update c i d)) θ ≤
    ownerPotential H (KSSpinSource.family (KSSpinLocalState.atoms v))
      (KSSpinSource.coefficientCovariance c) θ := by
  let V := KSSpinCompression.embedding (KSSpinLocalState.atoms v)
  let L := covarianceKraus (KSSpinSource.family (KSSpinLocalState.atoms v))
    (KSSpinSource.coefficientCovariance c)
  let S := optimizer H v c θ
  let Sh : selfAdjoint (Matrix (n ⊕ n) (n ⊕ n) ℂ) :=
    ⟨S, (densityOptimizer_posDef H L hθ).isHermitian⟩
  let Z := SourceTransport.stateTransport v c S
  have hS : S.PosDef := densityOptimizer_posDef H L hθ
  have hV := KSSpinCompression.embedding_isometry (KSSpinLocalState.atoms v)
  have hM := KSSpinCompression.compressed_source_posDef v hc hS
  have hS0 := KSSupportSymmetry.compress_posDef V hV hS
  apply local_move_in_frame H v c (fun j => (hc j).le) V hV hθ Sh hS
    (densityOptimizer_mem H L θ).2
    (by intro T hT; exact densityOptimizer_isMaxOn H L θ T hT)
    (SourceTransport.stateTransport_posDef v hc hS) hM
    (transportOptimizer_solve hS0 hM)
    (fun X _ => KSSpinCompression.source_reconstruct v c X) i t d hd hdc
  change |t| ≤ (c i - d) * realTrace (KSSpinSource.doubled (KSSpinLocalState.atoms v i) *
    (KSSpinCompression.embedding (KSSpinLocalState.atoms v) * Z *
      (KSSpinCompression.embedding (KSSpinLocalState.atoms v))ᴴ))
  rw [KSSpinCompression.transport_probe (KSSpinLocalState.atoms v) Z i,
    realTrace_mul_comm]
  exact hsafe

theorem weight_abs (u ζ x : ℝ) : Source.weight u ζ |x| = Source.weight u ζ x := by
  simp only [Source.weight, sq_abs]

theorem smoothWeights_update (ζ : ℝ) (x : ι → ℝ) (i : ι) (t : ℝ) :
    SourceTransport.smoothWeights ζ (Function.update x i t) =
      Function.update (SourceTransport.smoothWeights ζ x) i (Source.weight 64 ζ t) := by
  funext j
  by_cases hj : j = i
  · subst j
    simp only [SourceTransport.smoothWeights, Function.update_self]
  · simp only [SourceTransport.smoothWeights, Function.update_of_ne hj]

theorem outward_weight (u ζ x a s : ℝ) (hs : |s| = 1) (hout : s * x = |x|) :
    Source.weight u ζ (x + a * s) = Source.weight u ζ (|x| + a) := by
  have hs2 : s ^ 2 = 1 := by nlinarith [sq_abs s]
  have hb : s * |x| = x := by
    calc
      s * |x| = s * (s * x) := by rw [hout]
      _ = s ^ 2 * x := by ring
      _ = x := by rw [hs2, one_mul]
  have he : x + a * s = s * (|x| + a) := by rw [mul_add, hb, mul_comm s a]
  rw [he]
  simp only [Source.weight, mul_pow, hs2, one_mul]

theorem smoothWeights_outward_update (ζ : ℝ) (x : ι → ℝ) (i : ι)
    (a s : ℝ) (hs : |s| = 1) (hout : s * x i = |x i|) :
    SourceTransport.smoothWeights ζ (Function.update x i (x i + a * s)) =
      Function.update (SourceTransport.smoothWeights ζ x) i
        (Source.weight 64 ζ (|x i| + a)) := by
  rw [smoothWeights_update, outward_weight 64 ζ (x i) a s hs hout]

/-- The actual smooth-source outward candidate, with a certified local
center increment. The new source weight is its value at radius `|xᵢ|+a`. -/
theorem smooth_outward_move [Nonempty n]
    (H : Matrix (n ⊕ n) (n ⊕ n) ℂ) (v : ι → n → ℂ)
    (x : ι → ℝ) (hx : ∀ j, |x j| < 1)
    {ζ a θ : ℝ} (hζ : 0 < ζ) (ha : 0 < a) (hscale : ζ ≤ a / 10)
    (hθ : 0 < θ) (i : ι) (hmargin : |x i| + a ≤ 1)
    (s : ℝ) (hs : |s| = 1)
    (hsafe : 1 ≤ Source.secant 64 ζ |x i| a * realTrace
      (SourceTransport.stateTransport v (SourceTransport.smoothWeights ζ x)
        (optimizer H v (SourceTransport.smoothWeights ζ x) θ) *
          KSSpinCompression.compressedAtom (KSSpinLocalState.atoms v) i)) :
    ownerPotential (H + (a * s) • signedLift (atom (v i)))
      (KSSpinSource.family (KSSpinLocalState.atoms v))
      (KSSpinSource.coefficientCovariance
        (Function.update (SourceTransport.smoothWeights ζ x) i
          (Source.weight 64 ζ (|x i| + a)))) θ ≤
    ownerPotential H (KSSpinSource.family (KSSpinLocalState.atoms v))
      (KSSpinSource.coefficientCovariance (SourceTransport.smoothWeights ζ x)) θ := by
  let c := SourceTransport.smoothWeights ζ x
  let d := Source.weight 64 ζ (|x i| + a)
  let ell := Source.secant 64 ζ |x i| a
  have hc : ∀ j, 0 < c j := fun j => Source.weight_pos (by norm_num) (hx j)
  have hd : 0 ≤ d := Source.weight_nonneg (by norm_num)
    (by rw [abs_of_nonneg (by positivity : 0 ≤ |x i| + a)]; exact hmargin)
  have hloss : c i - d = a * ell := by
    dsimp only [c, d, ell, SourceTransport.smoothWeights, Source.secant]
    rw [weight_abs]
    field_simp
  have hell : 0 < ell := Source.secant_pos (by norm_num) hζ.le (abs_nonneg _) ha hscale
  have hdc : d ≤ c i := by have := mul_pos ha hell; rw [← hloss] at this; linarith
  apply local_move H v c hc hθ i (a * s) d hd hdc
  rw [abs_mul, abs_of_pos ha, hs, mul_one, hloss]
  have hm := mul_le_mul_of_nonneg_left hsafe ha.le
  simpa only [mul_one, mul_assoc] using hm

/-- The local comparison with the source recomputed at the actual updated
position; its scalar source invariant holds exactly. -/
theorem smooth_outward_position [Nonempty n]
    (H : Matrix (n ⊕ n) (n ⊕ n) ℂ) (v : ι → n → ℂ)
    (x : ι → ℝ) (hx : ∀ j, |x j| < 1)
    {ζ a θ : ℝ} (hζ : 0 < ζ) (ha : 0 < a) (hscale : ζ ≤ a / 10)
    (hθ : 0 < θ) (i : ι) (hmargin : |x i| + a ≤ 1)
    (s : ℝ) (hs : |s| = 1) (hout : s * x i = |x i|)
    (hsafe : 1 ≤ Source.secant 64 ζ |x i| a * realTrace
      (SourceTransport.stateTransport v (SourceTransport.smoothWeights ζ x)
        (optimizer H v (SourceTransport.smoothWeights ζ x) θ) *
          KSSpinCompression.compressedAtom (KSSpinLocalState.atoms v) i)) :
    ownerPotential (H + (a * s) • signedLift (atom (v i)))
      (KSSpinSource.family (KSSpinLocalState.atoms v))
      (KSSpinSource.coefficientCovariance (SourceTransport.smoothWeights ζ
        (Function.update x i (x i + a * s)))) θ ≤
    ownerPotential H (KSSpinSource.family (KSSpinLocalState.atoms v))
      (KSSpinSource.coefficientCovariance (SourceTransport.smoothWeights ζ x)) θ := by
  rw [smoothWeights_outward_update ζ x i a s hs hout]
  exact smooth_outward_move H v x hx hζ ha hscale hθ i hmargin s hs hsafe

/-- Boundary rounding with a physical debit uses only order monotonicity.
This also applies when other labels are frozen and their weights are zero. -/
theorem boundary_snap [Nonempty n]
    (H : Matrix (n ⊕ n) (n ⊕ n) ℂ) (v : ι → n → ℂ)
    (c : ι → ℝ) (hc : ∀ j, 0 ≤ c j) {θ : ℝ} (hθ : 0 < θ)
    (i : ι) (t r : ℝ) (hsize : |t| ≤ r) :
    ownerPotential (H + t • signedLift (atom (v i)) - r • KSSpinSource.doubled (atom (v i)))
      (KSSpinSource.family (fun j => atom (v j)))
      (KSSpinSource.coefficientCovariance (Function.update c i 0)) θ ≤
    ownerPotential H (KSSpinSource.family (fun j => atom (v j)))
      (KSSpinSource.coefficientCovariance c) θ := by
  have hA := KSSpinSource.family_isHermitian (fun j => atom (v j)) (fun j => atom_isHermitian _)
  have hC := KSSpinSource.coefficientCovariance_posSemidef hc
  have hCnew := KSSpinSource.coefficientCovariance_posSemidef (update_nonneg hc i le_rfl)
  have hstep := spin_step_le (atom_posSemidef (v i)) hsize
  have hcenter : H + t • signedLift (atom (v i)) - r • KSSpinSource.doubled (atom (v i)) ≤ H := by
    have hh := add_le_add_left (sub_nonpos.mpr hstep) H
    simpa only [add_zero, ← add_sub_assoc] using hh
  exact (KSDebitPotential.ownerPotential_mono_center hcenter _ hA hCnew hθ).trans
    (ownerPotential_mono_covariance H _ hA hCnew hC (covariance_update_le c i (hc i)) θ)

omit [Fintype n] [DecidableEq n] in
theorem debit_center_update (H B A : Matrix n n ℂ) (t r : ℝ) :
    KSDebitCenter.center (H + t • A) (B + r • A) =
      KSDebitCenter.center H B + t • signedLift A - r • KSSpinSource.doubled A := by
  ext a b
  cases a <;> cases b <;>
    simp [KSDebitCenter.center, signedLift, KSSpinSource.doubled, Matrix.fromBlocks,
      Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.neg_apply,
      smul_neg] <;> ring

/-- The boundary comparison expressed in physical center/debit coordinates. -/
theorem boundary_snap_debit [Nonempty n]
    (H B : Matrix n n ℂ) (v : ι → n → ℂ)
    (c : ι → ℝ) (hc : ∀ j, 0 ≤ c j) {θ : ℝ} (hθ : 0 < θ)
    (i : ι) (t r : ℝ) (hsize : |t| ≤ r) :
    KSDebitPotential.potential (H + t • atom (v i)) (B + r • atom (v i))
      v (Function.update c i 0) θ ≤ KSDebitPotential.potential H B v c θ := by
  unfold KSDebitPotential.potential
  rw [debit_center_update]
  exact boundary_snap _ v c hc hθ i t r hsize

/-- Once each label is rounded at distance at most `ρ`, Parseval bounds the
total debit by `ρ I`. The controller must prove the one-rounding invariant. -/
theorem debit_sum_bounds (v : ι → n → ℂ)
    (hp : (∑ i, atom (v i)) = 1) (r : ι → ℝ) {ρ : ℝ}
    (hr : ∀ i, 0 ≤ r i) (hρ : ∀ i, r i ≤ ρ) :
    (∑ i, r i • atom (v i)).PosSemidef ∧
      (∑ i, r i • atom (v i)) ≤ ρ • (1 : Matrix n n ℂ) := by
  constructor
  · exact (Finset.sum_nonneg (fun i _ =>
      (atom_posSemidef (v i)).smul (hr i) |>.nonneg)).posSemidef
  · calc
      (∑ i, r i • atom (v i)) ≤ ∑ i, ρ • atom (v i) :=
        Finset.sum_le_sum (fun i _ => smul_le_smul_of_nonneg_right (hρ i)
          (atom_posSemidef (v i)).nonneg)
      _ = ρ • (1 : Matrix n n ℂ) := by rw [← Finset.smul_sum, hp]

/-- Simultaneous local changes with matching physical debit and a smaller
source decrease the potential. No support or optimizer is assumed. -/
theorem simultaneous_debit_compare [Nonempty n]
    (H B : Matrix n n ℂ) (v : ι → n → ℂ)
    (c cnew t r : ι → ℝ) (hc : ∀ i, 0 ≤ c i) (hcnew : ∀ i, 0 ≤ cnew i)
    (hsource : ∀ i, cnew i ≤ c i) (hsize : ∀ i, |t i| ≤ r i)
    {θ : ℝ} (hθ : 0 < θ) :
    KSDebitPotential.potential (H + ∑ i, t i • atom (v i))
      (B + ∑ i, r i • atom (v i)) v cnew θ ≤
        KSDebitPotential.potential H B v c θ := by
  have hpos : (∑ i, t i • atom (v i)) ≤ ∑ i, r i • atom (v i) :=
    Finset.sum_le_sum (fun i _ => smul_le_smul_of_nonneg_right
      ((le_abs_self _).trans (hsize i)) (atom_posSemidef (v i)).nonneg)
  have hneg : -(∑ i, t i • atom (v i)) ≤ ∑ i, r i • atom (v i) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_le_sum
    intro i _
    rw [← neg_smul]
    exact smul_le_smul_of_nonneg_right ((neg_le_abs _).trans (hsize i))
      (atom_posSemidef (v i)).nonneg
  have hcenter : KSDebitCenter.center (H + ∑ i, t i • atom (v i))
      (B + ∑ i, r i • atom (v i)) ≤ KSDebitCenter.center H B := by
    rw [KSDebitCenter.center_eq_blocks, KSDebitCenter.center_eq_blocks]
    apply fromBlocks_diagonal_mono
    · have hh := add_le_add_left (sub_nonpos.mpr hpos) (H - B)
      convert hh using 1 <;> abel
    · have hh := add_le_add_left (sub_nonpos.mpr hneg) (-H - B)
      convert hh using 1 <;> abel
  have hC : KSSpinSource.coefficientCovariance cnew ≤ KSSpinSource.coefficientCovariance c := by
    apply Matrix.le_iff.mpr
    rw [KSSpinSource.coefficientCovariance, KSSpinSource.coefficientCovariance, Matrix.diagonal_sub]
    exact Matrix.posSemidef_diagonal_iff.mpr (fun j => by
      change 0 ≤ c j.1 / 2 - cnew j.1 / 2
      linarith [hsource j.1])
  have hA := KSSpinSource.family_isHermitian (fun j => atom (v j)) (fun j => atom_isHermitian _)
  exact (KSDebitPotential.ownerPotential_mono_center hcenter _ hA
    (KSSpinSource.coefficientCovariance_posSemidef hcnew) hθ).trans
    (ownerPotential_mono_covariance _ _ hA
      (KSSpinSource.coefficientCovariance_posSemidef hcnew)
      (KSSpinSource.coefficientCovariance_posSemidef hc) hC θ)

/-- Simultaneous true-boundary snaps preserve the actual source prescription
and decrease the potential after charging the coordinate distances. -/
theorem simultaneous_boundary_snap [Nonempty n]
    (H B : Matrix n n ℂ) (v : ι → n → ℂ) (x y : ι → ℝ)
    (hx : ∀ i, |x i| ≤ 1) (hy : ∀ i, y i = x i ∨ |y i| = 1)
    (ζ : ℝ) {θ : ℝ} (hθ : 0 < θ) :
    KSDebitPotential.potential (H + ∑ i, (y i - x i) • atom (v i))
      (B + ∑ i, |y i - x i| • atom (v i)) v
        (SourceTransport.smoothWeights ζ y) θ ≤
    KSDebitPotential.potential H B v (SourceTransport.smoothWeights ζ x) θ := by
  have hc : ∀ i, 0 ≤ SourceTransport.smoothWeights ζ x i :=
    fun i => Source.weight_nonneg (by norm_num) (hx i)
  have he (i : ι) : SourceTransport.smoothWeights ζ y i =
      SourceTransport.smoothWeights ζ x i ∨ SourceTransport.smoothWeights ζ y i = 0 := by
    rcases hy i with hi | hi
    · left
      change Source.weight 64 ζ (y i) = Source.weight 64 ζ (x i)
      rw [hi]
    · right
      have hi2 : y i ^ 2 = 1 := by nlinarith [sq_abs (y i)]
      simp only [SourceTransport.smoothWeights, Source.weight, hi2, sub_self, zero_add]
      ring
  apply simultaneous_debit_compare H B v (SourceTransport.smoothWeights ζ x)
    (SourceTransport.smoothWeights ζ y) (fun i => y i - x i) (fun i => |y i - x i|)
    hc _ _ (fun _ => le_rfl) hθ
  · intro i
    rcases he i with hi | hi
    · exact hi.symm ▸ hc i
    · exact le_of_eq hi.symm
  · intro i
    rcases he i with hi | hi
    · exact le_of_eq hi
    · exact (le_of_eq hi).trans (hc i)

end SeamlessKS.LocalComparison
