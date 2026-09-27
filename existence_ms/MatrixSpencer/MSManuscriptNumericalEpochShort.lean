import MatrixSpencer.MSManuscriptNumericalShort


open Matrix
open scoped BigOperators MatrixOrder
noncomputable section
namespace MatrixSpencer.MSManuscriptNumericalEpochShort
open MSManuscriptNumericalShort
variable {d : ℕ}

def applyConstraints (C : Matrix (Fin d) (Fin d) ℝ) : List (Fin d → ℝ) → Matrix (Fin d) (Fin d) ℝ
  | [] => C
  | u::us => applyConstraints (short C u) us

theorem applyConstraints_posSemidef (C : Matrix (Fin d) (Fin d) ℝ) (hC : C.PosSemidef)
    (us : List (Fin d → ℝ)) : (applyConstraints C us).PosSemidef := by
  induction us generalizing C with
  | nil => exact hC
  | cons u us ih => exact ih _ (short_posSemidef C hC u)

theorem applyConstraints_le (C : Matrix (Fin d) (Fin d) ℝ) (hC : C.PosSemidef)
    (us : List (Fin d → ℝ)) : applyConstraints C us≤C := by
  induction us generalizing C with
  | nil => exact le_rfl
  | cons u us ih => exact (ih _ (short_posSemidef C hC u)).trans (short_le C hC u)

theorem applyConstraints_preserves (C : Matrix (Fin d) (Fin d) ℝ) (hC : C.PosSemidef)
    (us : List (Fin d → ℝ)) (v : Fin d → ℝ) (hv : C*ᵥv=0) : applyConstraints C us*ᵥv=0 := by
  induction us generalizing C with
  | nil => exact hv
  | cons u us ih => exact ih _ (short_posSemidef C hC u) (short_preserves_annihilator C hC.isHermitian u v hv)

theorem applyConstraints_annihilates (C : Matrix (Fin d) (Fin d) ℝ) (hC : C.PosSemidef)
    (us : List (Fin d → ℝ)) (v : Fin d → ℝ) (hv : v∈us) : applyConstraints C us*ᵥv=0 := by
  induction us generalizing C with
  | nil => simp at hv
  | cons u us ih =>
    rcases List.mem_cons.mp hv with he|hm
    · subst v
      exact applyConstraints_preserves _ (short_posSemidef C hC u) us u (short_annihilates C hC u)
    · exact ih _ (short_posSemidef C hC u) hm

theorem applyConstraints_trace_loss (C : Matrix (Fin d) (Fin d) ℝ) (hC : C.PosSemidef)
    (hC1 : C≤1) (us : List (Fin d → ℝ)) : realTrace C-realTrace (applyConstraints C us)≤us.length := by
  induction us generalizing C with
  | nil => simp [applyConstraints]
  | cons u us ih =>
    have h := ih _ (short_posSemidef C hC u) ((short_le C hC u).trans hC1)
    have hh := short_trace_loss C hC hC1 u
    simp only [applyConstraints,List.length_cons,Nat.cast_add,Nat.cast_one]
    linarith

theorem applyConstraints_maximal (C B : Matrix (Fin d) (Fin d) ℝ) (hC : C.PosSemidef)
    (hB : B.PosSemidef) (hBC : B≤C) (us : List (Fin d → ℝ))
    (hBu : ∀u∈us,B*ᵥu=0) : B≤applyConstraints C us := by
  induction us generalizing C with
  | nil => exact hBC
  | cons u us ih =>
    apply ih _ (short_posSemidef C hC u) (short_maximal C B hC hB hBC u (hBu u (by simp)))
    intro v hv
    exact hBu v (List.mem_cons_of_mem u hv)

def frozenLabels (F : Finset (Fin d)) : List (Fin d) :=
  (List.finRange d).filter (fun i => decide (i∈F))
def constraints (F : Finset (Fin d)) (x : EuclideanSpace ℝ (Fin d)) : List (Fin d → ℝ) :=
  (frozenLabels F).map (fun i => Pi.single i 1) ++ [WithLp.ofLp x]
def epoch (C : Matrix (Fin d) (Fin d) ℝ) (F : Finset (Fin d)) (x : EuclideanSpace ℝ (Fin d)) :=
  applyConstraints C (constraints F x)

theorem mem_frozenLabels (F : Finset (Fin d)) (i : Fin d) : i∈frozenLabels F↔i∈F := by simp [frozenLabels]
theorem length_frozenLabels (F : Finset (Fin d)) : (frozenLabels F).length=F.card := by
  have hn : (frozenLabels F).Nodup := (List.nodup_finRange d).filter _
  have he : (frozenLabels F).toFinset=F := by ext i; simp only [List.mem_toFinset,mem_frozenLabels]
  rw [←List.toFinset_card_of_nodup hn,he]

theorem length_constraints (F : Finset (Fin d)) (x : EuclideanSpace ℝ (Fin d)) :
    (constraints F x).length=F.card+1 := by simp [constraints,length_frozenLabels]

theorem epoch_posSemidef (C : Matrix (Fin d) (Fin d) ℝ) (hC : C.PosSemidef)
    (F : Finset (Fin d)) (x : EuclideanSpace ℝ (Fin d)) : (epoch C F x).PosSemidef :=
  applyConstraints_posSemidef C hC _
theorem epoch_le (C : Matrix (Fin d) (Fin d) ℝ) (hC : C.PosSemidef)
    (F : Finset (Fin d)) (x : EuclideanSpace ℝ (Fin d)) : epoch C F x≤C :=
  applyConstraints_le C hC _
theorem epoch_radial (C : Matrix (Fin d) (Fin d) ℝ) (hC : C.PosSemidef)
    (F : Finset (Fin d)) (x : EuclideanSpace ℝ (Fin d)) : epoch C F x*ᵥWithLp.ofLp x=0 :=
  applyConstraints_annihilates C hC _ _ (by simp [constraints])
theorem epoch_frozen (C : Matrix (Fin d) (Fin d) ℝ) (hC : C.PosSemidef)
    (F : Finset (Fin d)) (x : EuclideanSpace ℝ (Fin d)) (i : Fin d) (hi : i∈F) :
    epoch C F x*ᵥPi.single i 1=0 := by
  apply applyConstraints_annihilates C hC
  apply List.mem_append_left
  exact List.mem_map.mpr ⟨i,(mem_frozenLabels F i).mpr hi,rfl⟩

theorem epoch_trace_lower (C : Matrix (Fin d) (Fin d) ℝ) (hC : C.PosSemidef) (hC1 : C≤1)
    (F : Finset (Fin d)) (x : EuclideanSpace ℝ (Fin d)) :
    realTrace C-(F.card:ℝ)-1≤realTrace (epoch C F x) := by
  have h := applyConstraints_trace_loss C hC hC1 (constraints F x)
  rw [length_constraints,Nat.cast_add,Nat.cast_one] at h
  change realTrace C-realTrace (epoch C F x)≤(F.card:ℝ)+1 at h
  linarith

theorem epoch_maximal (C B : Matrix (Fin d) (Fin d) ℝ) (hC : C.PosSemidef)
    (hB : B.PosSemidef) (hBC : B≤C) (F : Finset (Fin d)) (x : EuclideanSpace ℝ (Fin d))
    (hBF : ∀i∈F,B*ᵥPi.single i 1=0) (hBx : B*ᵥWithLp.ofLp x=0) : B≤epoch C F x := by
  apply applyConstraints_maximal C B hC hB hBC
  intro u hu
  rcases List.mem_append.mp hu with huf|hux
  · obtain ⟨i,hi,rfl⟩ := List.mem_map.mp huf
    exact hBF i ((mem_frozenLabels F i).mp hi)
  · have he : u=WithLp.ofLp x := List.mem_singleton.mp hux
    rw [he]
    exact hBx

end MatrixSpencer.MSManuscriptNumericalEpochShort
