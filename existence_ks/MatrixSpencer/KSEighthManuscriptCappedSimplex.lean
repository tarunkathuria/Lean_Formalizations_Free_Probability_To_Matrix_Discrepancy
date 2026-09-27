import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Data.Finset.Max
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic



open scoped BigOperators
noncomputable section
namespace MatrixSpencer.KSEighthManuscriptCappedSimplex

variable {d : ℕ}

def clip (t : ℝ) : ℝ := max 0 (min 1 t)

theorem clip_nonneg (t : ℝ) : 0 ≤ clip t := le_max_left _ _
theorem clip_le_one (t : ℝ) : clip t ≤ 1 := max_le (by norm_num) (min_le_left _ _)
theorem clip_of_nonpos {t : ℝ} (ht : t ≤ 0) : clip t = 0 := by
  exact max_eq_left ((min_le_right _ _).trans ht)
theorem clip_of_one_le {t : ℝ} (ht : 1 ≤ t) : clip t = 1 := by
  simp [clip, min_eq_left ht]
theorem clip_of_mem {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 1) : clip t = t := by
  simp [clip, min_eq_right h1, max_eq_right h0]

def mass (z : Fin d → ℝ) (x : ℝ) : ℝ := ∑ i, clip (z i - x)
def radius (z : Fin d → ℝ) : ℝ := 1 + ∑ i, |z i|

theorem abs_le_radius (z : Fin d → ℝ) (i : Fin d) : |z i| ≤ radius z - 1 := by
  simpa [radius] using Finset.single_le_sum (fun j (_ : j ∈ Finset.univ) => abs_nonneg (z j))
    (Finset.mem_univ i)

theorem radius_pos (z : Fin d → ℝ) : 0 < radius z := by
  have h := Finset.sum_nonneg (fun i (_ : i ∈ Finset.univ) => abs_nonneg (z i))
  dsimp [radius]
  linarith

theorem mass_left (z : Fin d → ℝ) : mass z (-radius z) = d := by
  have h (i : Fin d) : clip (z i - -radius z) = 1 := by
    apply clip_of_one_le
    have := abs_le_radius z i
    have := neg_abs_le (z i)
    linarith
  simp only [mass, h, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]

theorem mass_right (z : Fin d → ℝ) : mass z (radius z) = 0 := by
  have h (i : Fin d) : clip (z i - radius z) = 0 := by
    apply clip_of_nonpos
    have := abs_le_radius z i
    have := le_abs_self (z i)
    linarith
  simp [mass, h]

theorem mass_continuous (z : Fin d → ℝ) : Continuous (mass z) := by
  unfold mass clip
  fun_prop

theorem exists_threshold (z : Fin d → ℝ) {s : ℝ} (h0 : 0 ≤ s) (hd : s ≤ d) :
    ∃ x, -radius z ≤ x ∧ x ≤ radius z ∧ mass z x = s := by
  have hr : -radius z ≤ radius z := by linarith [radius_pos z]
  have hs : s ∈ Set.Icc (mass z (radius z)) (mass z (-radius z)) := by
    simpa [mass_left, mass_right] using And.intro h0 hd
  obtain ⟨x, hx, he⟩ := intermediate_value_Icc' hr (mass_continuous z).continuousOn hs
  exact ⟨x, hx.1, hx.2, he⟩

def breaks (z : Fin d → ℝ) : List ℝ :=
  -radius z :: (List.finRange d).flatMap (fun i => [z i, z i - 1])

theorem left_mem_breaks (z : Fin d → ℝ) : -radius z ∈ breaks z := by simp [breaks]
theorem coordinate_mem_breaks (z : Fin d → ℝ) (i : Fin d) : z i ∈ breaks z := by
  simp only [breaks, List.mem_cons, List.mem_flatMap]
  exact Or.inr ⟨i, List.mem_finRange i, by simp⟩
theorem coordinate_sub_one_mem_breaks (z : Fin d → ℝ) (i : Fin d) : z i - 1 ∈ breaks z := by
  simp only [breaks, List.mem_cons, List.mem_flatMap]
  exact Or.inr ⟨i, List.mem_finRange i, by simp⟩

def middle (z : Fin d → ℝ) (b : ℝ) (i : Fin d) : Prop := b < z i ∧ z i ≤ b + 1
instance (z : Fin d → ℝ) (b : ℝ) (i : Fin d) : Decidable (middle z b i) :=
  inferInstanceAs (Decidable (b < z i ∧ z i ≤ b + 1))

def highCount (z : Fin d → ℝ) (b : ℝ) : ℝ := ∑ i, if b + 1 < z i then 1 else 0
def middleCount (z : Fin d → ℝ) (b : ℝ) : ℝ := ∑ i, if middle z b i then 1 else 0
def middleSum (z : Fin d → ℝ) (b : ℝ) : ℝ := ∑ i, if middle z b i then z i else 0

theorem cell_formula (z : Fin d → ℝ) {b x : ℝ} (hbx : b ≤ x)
    (hgap : ∀ t ∈ breaks z, t ≤ x → t ≤ b) :
    mass z x = middleSum z b + highCount z b - middleCount z b * x := by
  have hi (i : Fin d) : clip (z i - x) =
      (if middle z b i then z i else 0) + (if b + 1 < z i then 1 else 0) -
        (if middle z b i then 1 else 0) * x := by
    by_cases hh : b + 1 < z i
    · have hm : ¬ middle z b i := by intro h; exact (not_le.mpr hh) h.2
      have hx : x < z i - 1 := by
        by_contra hn
        have := hgap (z i - 1) (coordinate_sub_one_mem_breaks z i) (le_of_not_gt hn)
        linarith
      simp only [if_neg hm, if_pos hh, clip_of_one_le (t := z i-x) (by linarith)]
      ring
    · by_cases hm : b < z i
      · have hmid : middle z b i := ⟨hm, le_of_not_gt hh⟩
        have hx : x < z i := by
          by_contra hn
          exact (not_le.mpr hm) (hgap (z i) (coordinate_mem_breaks z i) (le_of_not_gt hn))
        simp only [if_pos hmid, if_neg hh, clip_of_mem (t := z i-x) (by linarith) (by linarith [le_of_not_gt hh])]
        ring
      · have hmid : ¬ middle z b i := by exact fun h => hm h.1
        simp only [if_neg hmid, if_neg hh, clip_of_nonpos (t := z i-x) (by linarith [le_of_not_gt hm])]
        ring
  simp only [mass, hi, Finset.sum_sub_distrib, Finset.sum_add_distrib,
    ← Finset.sum_mul, middleSum, middleCount, highCount]

def affineCandidate (z : Fin d → ℝ) (s b : ℝ) : ℝ :=
  if middleCount z b = 0 then b
  else (middleSum z b + highCount z b - s) / middleCount z b

def candidates (z : Fin d → ℝ) (s : ℝ) : List ℝ :=
  (breaks z).flatMap (fun b => [b, affineCandidate z s b])

theorem exists_exact_candidate (z : Fin d → ℝ) {s : ℝ} (h0 : 0 ≤ s) (hd : s ≤ d) :
    ∃ c ∈ candidates z s, mass z c = s := by
  classical
  obtain ⟨x, hxl, _, hxs⟩ := exists_threshold z h0 hd
  let B := (breaks z).toFinset.filter (fun b => b ≤ x)
  have hB : B.Nonempty := ⟨-radius z, by simp [B, left_mem_breaks, hxl]⟩
  let b := B.max' hB
  have hbB : b ∈ B := B.max'_mem hB
  have hbm : b ∈ breaks z := by simpa [B] using (Finset.mem_filter.mp hbB).1
  have hbx : b ≤ x := (Finset.mem_filter.mp hbB).2
  have hgap : ∀ t ∈ breaks z, t ≤ x → t ≤ b := by
    intro t ht htx
    exact B.le_max' t (by simp [B, ht, htx])
  by_cases he : mass z b = s
  · exact ⟨b, List.mem_flatMap.mpr ⟨b, hbm, by simp⟩, he⟩
  · have hx := cell_formula z hbx hgap
    have hb := cell_formula z (b := b) (x := b) le_rfl (fun _ _ ht => ht)
    have hc : middleCount z b ≠ 0 := by
      intro hc
      rw [hc, zero_mul, sub_zero] at hx hb
      exact he (hb.trans (hx.symm.trans hxs))
    have ha : affineCandidate z s b = x := by
      rw [affineCandidate, if_neg hc]
      apply (div_eq_iff hc).mpr
      rw [hxs] at hx
      linarith
    exact ⟨affineCandidate z s b, List.mem_flatMap.mpr ⟨b, hbm, by simp⟩, ha ▸ hxs⟩

def firstExact (z : Fin d → ℝ) (s : ℝ) : List ℝ → ℝ
  | [] => 0
  | c :: cs => if mass z c = s then c else firstExact z s cs

theorem firstExact_correct (z : Fin d → ℝ) (s : ℝ) (cs : List ℝ)
    (hc : ∃ c ∈ cs, mass z c = s) : mass z (firstExact z s cs) = s := by
  induction cs with
  | nil => simp at hc
  | cons c cs ih =>
    rw [firstExact]
    split_ifs with h
    · exact h
    · apply ih
      obtain ⟨a, ha, he⟩ := hc
      rcases List.mem_cons.mp ha with rfl | ha
      · exact (h he).elim
      · exact ⟨a, ha, he⟩

def threshold (z : Fin d → ℝ) (s : ℝ) : ℝ := firstExact z s (candidates z s)
def project (z : Fin d → ℝ) (s : ℝ) (i : Fin d) : ℝ := clip (z i - threshold z s)

theorem project_nonneg (z : Fin d → ℝ) (s : ℝ) (i : Fin d) : 0 ≤ project z s i := clip_nonneg _
theorem project_le_one (z : Fin d → ℝ) (s : ℝ) (i : Fin d) : project z s i ≤ 1 := clip_le_one _
theorem project_sum (z : Fin d → ℝ) {s : ℝ} (h0 : 0 ≤ s) (hd : s ≤ d) :
    (∑ i, project z s i) = s :=
  firstExact_correct z s _ (exists_exact_candidate z h0 hd)

theorem clip_variational (z x y : ℝ) (hy0 : 0 ≤ y) (hy1 : y ≤ 1) :
    (z - clip (z-x)) * (y - clip (z-x)) ≤ x * (y - clip (z-x)) := by
  by_cases h0 : z-x ≤ 0
  · rw [clip_of_nonpos h0, sub_zero, sub_zero]
    exact mul_le_mul_of_nonneg_right (by linarith) hy0
  · by_cases h1 : 1 ≤ z-x
    · rw [clip_of_one_le h1]
      exact mul_le_mul_of_nonpos_right (by linarith) (sub_nonpos.mpr hy1)
    · rw [clip_of_mem (le_of_not_ge h0) (le_of_not_ge h1)]
      ring_nf
      exact le_rfl

/-- The output is the Euclidean projection onto the capped simplex of mass s. -/
theorem project_variational (z : Fin d → ℝ) {s : ℝ} (h0 : 0 ≤ s) (hd : s ≤ d)
    (y : Fin d → ℝ) (hy0 : ∀ i, 0 ≤ y i) (hy1 : ∀ i, y i ≤ 1)
    (hys : ∑ i, y i = s) :
    (∑ i, (z i - project z s i) * (y i - project z s i)) ≤ 0 := by
  calc
    _ ≤ ∑ i, threshold z s * (y i - project z s i) :=
      Finset.sum_le_sum (fun i _ => clip_variational _ _ _ (hy0 i) (hy1 i))
    _ = 0 := by
      rw [← Finset.mul_sum, Finset.sum_sub_distrib, hys, project_sum z h0 hd]
      ring

theorem project_minimizes (z : Fin d → ℝ) {s : ℝ} (h0 : 0 ≤ s) (hd : s ≤ d)
    (y : Fin d → ℝ) (hy0 : ∀ i, 0 ≤ y i) (hy1 : ∀ i, y i ≤ 1)
    (hys : ∑ i, y i = s) :
    (∑ i, (project z s i - z i)^2) ≤ ∑ i, (y i - z i)^2 := by
  have hv := project_variational z h0 hd y hy0 hy1 hys
  have hn : 0 ≤ ∑ i, (y i - project z s i)^2 :=
    Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have he : (∑ i, (y i - z i)^2) - (∑ i, (project z s i - z i)^2) =
      (∑ i, (y i - project z s i)^2) -
        2 * (∑ i, (z i - project z s i) * (y i - project z s i)) := by
    rw [← Finset.sum_sub_distrib, Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  linarith

/-- The candidate list is linear in dimension; each candidate uses finite sums. -/
theorem candidates_length (z : Fin d → ℝ) (s : ℝ) :
    (candidates z s).length = 4*d+2 := by
  simp [candidates, breaks, List.length_flatMap, List.length_finRange]
  omega

end MatrixSpencer.KSEighthManuscriptCappedSimplex
