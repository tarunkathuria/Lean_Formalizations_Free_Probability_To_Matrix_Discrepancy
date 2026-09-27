import SeamlessKS.State

/-! Both actual local movements stay in the current face and make entropy progress. -/
open Set
open scoped BigOperators
noncomputable section
namespace SeamlessKS.Proposals
open MatrixSpencer SeamlessKS.State
variable {N : ℕ} {ρ : ℝ}

theorem stays_in_cube (hρ : 0 < ρ) (s : PreparedState N ρ) (y : Fin N → ℝ)
    (hfrozen : ∀ i, |s.coeff i|=1 → y i=s.coeff i)
    (hdisp : ∀ i, |y i-s.coeff i|≤ρ/8) :
    y ∈ ksCube 1 ∧ (∀ i, |s.coeff i|<1 → |y i|<1) := by
  have hbound (i : Fin N) : |y i|≤1 := by
    rcases lt_or_eq_of_le (coeff_abs_le s.toCubeState i) with hi|hi
    · have hs := s.margin i hi
      have ha : |y i|≤|s.coeff i|+|y i-s.coeff i| := by
        calc |y i|=|s.coeff i+(y i-s.coeff i)| := by congr 1; ring
             _ ≤ _ := abs_add_le _ _
      linarith [hdisp i]
    · rw [hfrozen i hi,hi]
  constructor
  · exact ⟨fun i => (abs_le.mp (hbound i)).1,fun i => (abs_le.mp (hbound i)).2⟩
  · intro i hi
    have hs := s.margin i hi
    have ha : |y i|≤|s.coeff i|+|y i-s.coeff i| := by
      calc |y i|=|s.coeff i+(y i-s.coeff i)| := by congr 1; ring
           _ ≤ _ := abs_add_le _ _
    linarith [hdisp i]

def outwardVector (x : Fin N → ℝ) (i : Fin N) (a : ℝ) : Fin N → ℝ :=
  Function.update x i (Progress.outward (x i) a)

theorem outward_displacement {a : ℝ} (ha : 0≤a) (x : Fin N → ℝ)
    (i j : Fin N) : |outwardVector x i a j-x j|≤a := by
  by_cases hij : j=i
  · subst j
    simp only [outwardVector,Function.update_self,Progress.outward]
    split_ifs <;> simp [abs_of_nonneg ha]
  · simp [outwardVector,Function.update_of_ne hij,ha]

theorem outward_preserves_frozen (s : PreparedState N ρ) (i : Fin N)
    (hi : |s.coeff i|<1) (a : ℝ) (j : Fin N) (hj : |s.coeff j|=1) :
    outwardVector s.coeff i a j=s.coeff j := by
  have hji : j≠i := by intro he; subst j; rw [hj] at hi; exact lt_irrefl _ hi
  simp only [outwardVector,Function.update_of_ne hji]

def outwardMove (hρ : 0 < ρ) (s : PreparedState N ρ) (i : Fin N)
    (hi : |s.coeff i|<1) (a : ℝ) (ha : 0≤a) (har : a≤ρ/8) : CubeState N ρ :=
  move s.toCubeState (outwardVector s.coeff i a)
    (stays_in_cube hρ s _ (outward_preserves_frozen s i hi a)
      (fun j => (outward_displacement ha s.coeff i j).trans har)).1
    (outward_preserves_frozen s i hi a)

theorem outward_entropy (hρ : 0 < ρ) (s : PreparedState N ρ) (i : Fin N)
    (hi : |s.coeff i|<1) (a : ℝ) (ha : 0≤a) (har : a≤ρ/8) :
    Progress.entropy (outwardMove hρ s i hi a ha har).coeff≤Progress.entropy s.coeff-a^2 := by
  have hface : |s.coeff i|+a≤1 := by have hh := s.margin i hi; linarith
  have hh := Progress.outward_entropy_drop ha hface
  change Progress.entropy (Function.update s.coeff i (Progress.outward (s.coeff i) a))≤_
  simp only [Progress.entropy] at *
  simp_rw [Function.apply_update (fun _ => KSCubeEntropy.u)]
  rw [Finset.sum_update_of_mem (Finset.mem_univ i)]
  rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ i)]
  simp only [Finset.sdiff_singleton_eq_erase]
  linarith

theorem symmetric_displacement {ζ : ℝ} (hζ : 0≤ζ) (s : PreparedState N ρ)
    (v : EuclideanSpace ℝ (Fin N)) (hv : ‖v‖=1) (t : ℝ)
    (ht : |t|≤ρ/16) (i : Fin N) :
    |Progress.proposal s.coeff (weights ζ s.coeff) v t i-s.coeff i|≤ρ/8 := by
  have hd := Progress.proposal_displacement_le s.coeff (weights ζ s.coeff) v hv
    (weights_upper hζ s.toCubeState) t i
  have hs : Real.sqrt 2≤2 := Real.sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩
  have hm := mul_le_mul_of_nonneg_left hs (abs_nonneg t)
  linarith

theorem symmetric_preserves_frozen (ζ : ℝ) (s : PreparedState N ρ)
    (v : EuclideanSpace ℝ (Fin N)) (t : ℝ) (i : Fin N) (hi : |s.coeff i|=1) :
    Progress.proposal s.coeff (weights ζ s.coeff) v t i=s.coeff i :=
  Progress.proposal_preserves_frozen _ _ v t i (weights_frozen ζ s.toCubeState i hi)

def symmetricMove (hρ : 0 < ρ) {ζ : ℝ} (hζ : 0≤ζ) (s : PreparedState N ρ)
    (v : EuclideanSpace ℝ (Fin N)) (hv : ‖v‖=1) (t : ℝ) (ht : |t|≤ρ/16) : CubeState N ρ :=
  move s.toCubeState (Progress.proposal s.coeff (weights ζ s.coeff) v t)
    (stays_in_cube hρ s _ (symmetric_preserves_frozen ζ s v t)
      (symmetric_displacement hζ s v hv t ht)).1 (symmetric_preserves_frozen ζ s v t)

theorem symmetric_entropy (hρ : 0 < ρ) {ζ : ℝ} (hζ : 0≤ζ) (s : PreparedState N ρ)
    (v : EuclideanSpace ℝ (Fin N)) (hv : ‖v‖=1)
    (hvfrozen : ∀ i, |s.coeff i|=1 → v i=0) (t : ℝ) (ht : |t|≤ρ/16) :
    (Progress.entropy (symmetricMove hρ hζ s v hv t ht).coeff+
      Progress.entropy (symmetricMove hρ hζ s v hv (-t) (by simpa only [abs_neg] using ht)).coeff)/2≤
      Progress.entropy s.coeff-t^2 := by
  apply Progress.symmetric_entropy_drop s.coeff (weights ζ s.coeff)
    (coeff_abs_le s.toCubeState) (weights_lower ζ s.toCubeState)
    (weights_frozen ζ s.toCubeState) v hv hvfrozen t
  intro i hi
  have hd := symmetric_displacement hζ s v hv t ht i
  simp only [Progress.proposal,add_sub_cancel_left] at hd
  have hh := s.margin i hi
  linarith

end SeamlessKS.Proposals
