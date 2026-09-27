import MatrixSpencer.KSEighthManuscriptPreparationCost
import Mathlib.Data.List.NodupEquivFin



open Matrix
open scoped BigOperators Matrix.Norms.L2Operator
noncomputable section
namespace MatrixSpencer.KSEighthManuscriptPreprocess
variable {N d : ℕ}

def size (v : Fin N → Fin d → ℂ) (i : Fin N) : ℝ := ∑j, Complex.normSq (v i j)

theorem size_eq_norm (v : Fin N → Fin d → ℂ) (i : Fin N) : size v i = ‖KSRankOne.atom (v i)‖ := by
  rw [KSRankOne.atom_norm,KSRankOne.realTrace_atom]
  rfl

theorem size_nonneg (v : Fin N → Fin d → ℂ) (i : Fin N) : 0 ≤ size v i := by
  rw [size_eq_norm]
  exact norm_nonneg _

theorem atom_zero_of_size (v : Fin N → Fin d → ℂ) (i : Fin N) (hi : size v i = 0) :
    KSRankOne.atom (v i) = 0 := norm_eq_zero.mp ((size_eq_norm v i).symm.trans hi)

def labels (v : Fin N → Fin d → ℂ) := (List.finRange N).filter (fun i => decide (size v i ≠ 0))
def count (v : Fin N → Fin d → ℂ) := (labels v).length

theorem labels_nodup (v : Fin N → Fin d → ℂ) : (labels v).Nodup :=
  (List.nodup_finRange N).filter _

theorem mem_labels (v : Fin N → Fin d → ℂ) (i : Fin N) : i ∈ labels v ↔ size v i ≠ 0 := by
  simp [labels]

/-- Forward lookup and inverse finite index search in the actual filtered list. -/
def labelEquiv (v : Fin N → Fin d → ℂ) : Fin (count v) ≃ {i : Fin N // size v i ≠ 0} :=
  ((labels_nodup v).getEquiv (labels v)).trans
    { toFun := fun i => ⟨i.val,(mem_labels v i).mp i.property⟩
      invFun := fun i => ⟨i.val,(mem_labels v i).mpr i.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

def family (v : Fin N → Fin d → ℂ) : Fin (count v) → Fin d → ℂ := fun j => v (labelEquiv v j)

def restore (v : Fin N → Fin d → ℂ) (σ : Fin (count v) → ℝ) (i : Fin N) : ℝ :=
  if hi : size v i ≠ 0 then σ ((labelEquiv v).symm ⟨i,hi⟩) else 1

theorem restore_nonzero (v : Fin N → Fin d → ℂ) (σ : Fin (count v) → ℝ)
    (i : {i : Fin N // size v i ≠ 0}) : restore v σ i = σ ((labelEquiv v).symm i) := by
  simp only [restore,dif_pos i.property]

theorem restore_signs (v : Fin N → Fin d → ℂ) {σ : Fin (count v) → ℝ}
    (hσ : ∀j, IsSign (σ j)) : ∀i, IsSign (restore v σ i) := by
  intro i
  unfold restore
  split
  · exact hσ _
  · exact Or.inl rfl

theorem sum_restrict {E : Type*} [AddCommMonoid E] (v : Fin N → Fin d → ℂ) (f : Fin N → E)
    (hz : ∀i, size v i = 0 → f i = 0) :
    ∑i, f i = ∑j, f (labelEquiv v j) := by
  classical
  let S := Finset.univ.filter (fun i => size v i ≠ 0)
  have hs : ∑i ∈ S, f i = ∑i, f i := by
    apply Finset.sum_subset (Finset.subset_univ _)
    intro i _ hi
    apply hz
    simpa only [S,Finset.mem_filter,Finset.mem_univ,true_and,not_not] using hi
  rw [←hs]
  have hsub : (∑i ∈ S, f i) = ∑i : {i : Fin N // size v i ≠ 0}, f i :=
    Finset.sum_subtype S (by intro i; simp only [S,Finset.mem_filter,Finset.mem_univ,true_and]) f
  rw [hsub]
  exact ((labelEquiv v).sum_comp (fun i => f i)).symm

theorem family_parseval (v : Fin N → Fin d → ℂ) (hp : (∑i, KSRankOne.atom (v i)) = 1) :
    (∑j, KSRankOne.atom (family v j)) = 1 := by
  rw [sum_restrict v (fun i => KSRankOne.atom (v i)) (atom_zero_of_size v)] at hp
  exact hp

theorem restore_sum (v : Fin N → Fin d → ℂ) (σ : Fin (count v) → ℝ) :
    (∑i, restore v σ i • KSRankOne.atom (v i)) = ∑j, σ j • KSRankOne.atom (family v j) := by
  rw [sum_restrict v _ (by intro i hi; rw [atom_zero_of_size v i hi,smul_zero])]
  simp only [restore_nonzero,Equiv.symm_apply_apply,family]

def maximum (l : List ℝ) : ℝ := l.foldr max 0

theorem maximum_nonneg (l : List ℝ) : 0 ≤ maximum l := by
  induction l with
  | nil => exact le_rfl
  | cons a l ih => exact ih.trans (le_max_right _ _)

theorem le_maximum {l : List ℝ} {a : ℝ} (ha : a ∈ l) : a ≤ maximum l := by
  induction l with
  | nil => simp at ha
  | cons b l ih =>
    rcases List.mem_cons.mp ha with rfl | ha
    · exact le_max_left _ _
    · exact (ih ha).trans (le_max_right _ _)

theorem maximum_le {l : List ℝ} {R : ℝ} (hR : 0 ≤ R) (hl : ∀a ∈ l, a ≤ R) : maximum l ≤ R := by
  induction l with
  | nil => exact hR
  | cons a l ih =>
    exact max_le (hl a (List.mem_cons_self)) (ih (fun b hb => hl b (List.mem_cons_of_mem _ hb)))

/-- The original arithmetic maximum, unchanged by dropping zero labels. -/
def epsilon (v : Fin N → Fin d → ℂ) : ℝ := maximum ((List.finRange N).map (size v))

theorem epsilon_nonneg (v : Fin N → Fin d → ℂ) : 0 ≤ epsilon v := maximum_nonneg _

theorem size_le_epsilon (v : Fin N → Fin d → ℂ) (i : Fin N) : size v i ≤ epsilon v :=
  le_maximum (List.mem_map.mpr ⟨i,by simp,rfl⟩)

theorem epsilon_le (v : Fin N → Fin d → ℂ) {ε : ℝ} (hε : 0 ≤ ε)
    (hsize : ∀i, ‖KSRankOne.atom (v i)‖ ≤ ε) : epsilon v ≤ ε := by
  apply maximum_le hε
  intro a ha
  obtain ⟨i,hi,rfl⟩ := List.mem_map.mp ha
  exact (size_eq_norm v i).le.trans (hsize i)

theorem family_size (v : Fin N → Fin d → ℂ) (j : Fin (count v)) :
    ‖KSRankOne.atom (family v j)‖ ≤ epsilon v := by
  rw [family,←size_eq_norm]
  exact size_le_epsilon v _

theorem epsilon_le_one (v : Fin N → Fin d → ℂ) (hd : 0 < d)
    (hp : (∑i, KSRankOne.atom (v i)) = 1) : epsilon v ≤ 1 := by
  letI : Nonempty (Fin d) := ⟨⟨0,hd⟩⟩
  apply epsilon_le v zero_le_one
  intro i
  have hh := KSEighthManuscriptPreparationCost.signed_atom_norm_le_one v hp i
  rwa [signedLift_norm (KSRankOne.atom_isHermitian (v i))] at hh

theorem exists_size_pos (v : Fin N → Fin d → ℂ) (hd : 0 < d)
    (hp : (∑i, KSRankOne.atom (v i)) = 1) : ∃i, 0 < size v i := by
  by_contra! hh
  have hz (i : Fin N) : KSRankOne.atom (v i) = 0 := atom_zero_of_size v i (le_antisymm (hh i) (size_nonneg v i))
  have he := congrArg (fun A : Matrix (Fin d) (Fin d) ℂ => A ⟨0,hd⟩ ⟨0,hd⟩) hp
  simp only [hz,Finset.sum_const_zero,Matrix.zero_apply,Matrix.one_apply_eq] at he
  exact zero_ne_one he

theorem epsilon_pos (v : Fin N → Fin d → ℂ) (hd : 0 < d)
    (hp : (∑i, KSRankOne.atom (v i)) = 1) : 0 < epsilon v := by
  obtain ⟨i,hi⟩ := exists_size_pos v hd hp
  exact hi.trans_le (size_le_epsilon v i)

theorem count_pos (v : Fin N → Fin d → ℂ) (hd : 0 < d)
    (hp : (∑i, KSRankOne.atom (v i)) = 1) : 0 < count v := by
  obtain ⟨i,hi⟩ := exists_size_pos v hd hp
  have hm := (mem_labels v i).mpr hi.ne'
  have hn : labels v ≠ [] := by intro he; rw [he] at hm; exact List.not_mem_nil hm
  exact List.length_pos_iff.mpr hn

theorem count_le (v : Fin N → Fin d → ℂ) : count v ≤ N := by
  unfold count labels
  simpa using List.length_filter_le (fun i => decide (size v i ≠ 0)) (List.finRange N)


theorem dimension_le_count_epsilon (v : Fin N → Fin d → ℂ)
    (hp : (∑i, KSRankOne.atom (v i)) = 1) : (d : ℝ) ≤ (count v : ℝ)*epsilon v := by
  have he := congrArg realTrace (family_parseval v hp)
  rw [realTrace_sum] at he
  have hone : realTrace (1 : Matrix (Fin d) (Fin d) ℂ) = d := by simp [realTrace]
  rw [hone] at he
  have hh := Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ) => family_size v j)
  simp only [KSRankOne.atom_norm,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] at hh
  rw [he] at hh
  simpa using hh

end MatrixSpencer.KSEighthManuscriptPreprocess
