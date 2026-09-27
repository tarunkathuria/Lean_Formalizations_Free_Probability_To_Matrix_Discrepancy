import MatrixSpencer.KSStatement
import MatrixSpencer.KSCompactMinimum

/-! Exact endpoint bookkeeping and full-sign extraction for both cubes. -/

open scoped BigOperators Matrix Matrix.Norms.L2Operator
open Set

noncomputable section
namespace MatrixSpencer

def ksCube {N : ℕ} (a : ℝ) : Set (Fin N → ℝ) :=
  Icc (fun _ => -a) (fun _ => a)

def ksVertex {N : ℕ} (a : ℝ) (x : Fin N → ℝ) : Prop :=
  ∀ i, x i = -a ∨ x i = a

def ksFrozen {N : ℕ} (a : ℝ) (x : Fin N → ℝ) : Finset (Fin N) :=
  Finset.univ.filter (fun i => |x i| = a)

theorem ksCube_compact {N : ℕ} (a : ℝ) : IsCompact (ksCube (N := N) a) :=
  isCompact_Icc

theorem ksCube_zero {N : ℕ} {a : ℝ} (ha : 0 ≤ a) : (0 : Fin N → ℝ) ∈ ksCube a := by
  exact ⟨fun _ => by simpa using neg_nonpos.mpr ha, fun _ => ha⟩

theorem ksFrozen_card_le {N : ℕ} (a : ℝ) (x : Fin N → ℝ) : (ksFrozen a x).card ≤ N := by
  simpa using Finset.card_le_card (Finset.filter_subset (fun i => |x i| = a) Finset.univ)

theorem ksFrozen_lt_update {N : ℕ} {a : ℝ} (x : Fin N → ℝ) (i : Fin N)
    (hi : |x i| < a) (s : ℝ) (hs : |s| = a) :
    (ksFrozen a x).card < (ksFrozen a (Function.update x i s)).card := by
  have hsub : ksFrozen a x ⊆ ksFrozen a (Function.update x i s) := by
    intro j hj
    have hxj : |x j| = a := (Finset.mem_filter.mp hj).2
    have hji : j ≠ i := by
      intro he
      subst j
      exact (ne_of_lt hi) hxj
    simp only [ksFrozen, Finset.mem_filter, Finset.mem_univ, true_and]
    simpa only [Function.update_of_ne hji] using hxj
  apply Finset.card_lt_card
  apply Finset.ssubset_iff_subset_ne.mpr
  refine ⟨hsub, ?_⟩
  intro he
  have himem : i ∈ ksFrozen a (Function.update x i s) := by simp [ksFrozen, hs]
  rw [← he] at himem
  exact (ne_of_lt hi) (Finset.mem_filter.mp himem).2

theorem ksCube_update_endpoint {N : ℕ} {a : ℝ} (ha : 0 ≤ a)
    {x : Fin N → ℝ} (hx : x ∈ ksCube a) (i : Fin N)
    {s : ℝ} (hs : s = -a ∨ s = a) : Function.update x i s ∈ ksCube a := by
  constructor <;> intro j <;> by_cases hj : j = i
  · subst j
    simp only [Function.update_self]
    rcases hs with rfl | rfl <;> linarith
  · simpa only [Function.update_of_ne hj] using hx.1 j
  · subst j
    simp only [Function.update_self]
    rcases hs with rfl | rfl <;> linarith
  · simpa only [Function.update_of_ne hj] using hx.2 j

theorem ksVertex_div_fullSigning {N : ℕ} {a : ℝ} (ha : 0 < a)
    {x : Fin N → ℝ} (hx : ksVertex a x) : IsFullSigning (fun i => x i / a) := by
  intro i
  rcases hx i with hi | hi
  · right
    simp [hi, ha.ne']
  · left
    simp [hi, ha.ne']

theorem ks_signedSum_scale {N d : ℕ} (A : Fin N → CMatrix d)
    (x : Fin N → ℝ) (a : ℝ) :
    signedSum A (fun i => a * x i) = (a : ℂ) • signedSum A x := by
  simp only [signedSum, Complex.ofReal_mul, Finset.smul_sum, smul_smul]

theorem ks_spectralNorm_signedSum_scale {N d : ℕ} (A : Fin N → CMatrix d)
    (x : Fin N → ℝ) (a : ℝ) :
    spectralNorm (signedSum A (fun i => a * x i)) = |a| * spectralNorm (signedSum A x) := by
  rw [ks_signedSum_scale]
  simp only [spectralNorm_eq_scopedMatrixNorm, norm_smul, Complex.norm_real, Real.norm_eq_abs]

/-- Scaling a vertex of the radius-a cube gives genuine signs on every label. -/
theorem ks_vertex_signing_of_bound {N d : ℕ} (A : Fin N → CMatrix d)
    {a R : ℝ} (ha : 0 < a) {x : Fin N → ℝ} (hx : ksVertex a x)
    (hbound : spectralNorm (signedSum A x) ≤ a * R) :
    ∃ s : Fin N → ℝ, IsFullSigning s ∧ spectralNorm (signedSum A s) ≤ R := by
  let s := fun i => x i / a
  refine ⟨s, ksVertex_div_fullSigning ha hx, ?_⟩
  have he : x = fun i => a * s i := by
    funext i
    dsimp [s]
    field_simp
  have hn := ks_spectralNorm_signedSum_scale A s a
  rw [← he, abs_of_pos ha] at hn
  rw [hn] at hbound
  exact (mul_le_mul_left ha).mp hbound

end MatrixSpencer
