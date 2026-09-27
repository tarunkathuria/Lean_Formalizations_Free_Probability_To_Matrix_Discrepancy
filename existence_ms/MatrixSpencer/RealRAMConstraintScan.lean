import MatrixSpencer.RealRAMScalarShort
import MatrixSpencer.RealRAMRename
import MatrixSpencer.MSManuscriptNumericalEpochShort

/-!
# Primitive execution of a finite sequence of covariance constraints

Stage j reads matrix bank j and immutable constraint j, and writes bank j+1.
Register renaming literally expands the guarded scalar-short program. All
scratch banks may start arbitrarily; no free matrix assignment or matrix
function call is used. The scan is statically unrolled for its supplied finite
constraint count. Its arithmetic/comparison/store count is at most
`46*k*(d+1)^4`. Sampling a real-weight distribution is a separate operation.
-/
open Matrix
noncomputable section
namespace MatrixSpencer.RealRAM.ConstraintScan
abbrev Entries (d : ℕ) := ScalarShort.Entries d
abbrev Registers (d k : ℕ) := (Fin (k+1) × Entries d) ⊕ (Fin k × Fin d)
def matrix {d k : ℕ} (v : Registers d k → ℝ) (b : Fin (k+1)) : Matrix (Fin d) (Fin d) ℝ :=
  fun i j => v (.inl (b,(i,j)))
def constraint {d k : ℕ} (v : Registers d k → ℝ) (j : Fin k) : Fin d → ℝ :=
  fun i => v (.inr (j,i))
def embedding {d k : ℕ} (j : Fin k) : ScalarShort.Registers d → Registers d k
  | .inl (.inl ij) => .inl (j.castSucc,ij)
  | .inl (.inr i) => .inr (j,i)
  | .inr ij => .inl (j.succ,ij)

theorem embedding_injective {d k : ℕ} (j : Fin k) : Function.Injective (embedding (d:=d) j) := by
  intro a b hab
  have hne : j.castSucc≠j.succ := by
    intro h
    have hv := congrArg Fin.val h
    change j.val=j.val+1 at hv
    omega
  rcases a with (a|a)|a <;> rcases b with (b|b)|b <;>
    simp_all [embedding,Prod.mk.injEq]

def step {d k : ℕ} (j : Fin k) : Program (Registers d k) :=
  (ScalarShort.program d).rename (embedding j)

theorem step_safe {d k : ℕ} (j : Fin k) (v : Registers d k → ℝ) : (step j).Safe v :=
  (Program.safe_rename _ (embedding_injective j) _ v).mpr (ScalarShort.program_safe _)

theorem step_bound {d k : ℕ} (j : Fin k) : (step (d:=d) j).bound≤46*(d+1)^4 := by
  simpa only [step,Program.bound_rename] using ScalarShort.program_bound d

theorem step_output {d k : ℕ} (j : Fin k) (v : Registers d k → ℝ) :
    matrix ((step j).run v) j.succ =
      MSManuscriptNumericalShort.short (matrix v j.castSucc) (constraint v j) := by
  ext a b
  have hr := congrFun (Program.run_rename (embedding j) (embedding_injective j)
    (ScalarShort.program d) v) (.inr (a,b))
  rw [ScalarShort.program_output] at hr
  exact hr

theorem step_constraint {d k : ℕ} (j l : Fin k) (v : Registers d k → ℝ) :
    constraint ((step j).run v) l=constraint v l := by
  funext i
  by_cases hl : l=j
  · subst l
    have hr := congrFun (Program.run_rename (embedding j) (embedding_injective j)
      (ScalarShort.program d) v) (.inl (.inr i))
    rw [ScalarShort.program_preserves_input] at hr
    exact hr
  · apply Program.run_rename_outside
    intro a
    rcases a with (a|a)|a <;> simp [embedding,Ne.symm hl]

theorem step_matrix_preserves {d k : ℕ} (j : Fin k) (v : Registers d k → ℝ)
    (b : Fin (k+1)) (hb : b≠j.succ) : matrix ((step j).run v) b=matrix v b := by
  ext a c
  by_cases hbj : b=j.castSucc
  · subst b
    have hr := congrFun (Program.run_rename (embedding j) (embedding_injective j)
      (ScalarShort.program d) v) (.inl (.inl (a,c)))
    rw [ScalarShort.program_preserves_input] at hr
    exact hr
  · apply Program.run_rename_outside
    intro z
    rcases z with (z|z)|z <;> simp [embedding,Ne.symm hbj,Ne.symm hb]

def scan (d k : ℕ) : ℕ → Program (Registers d k)
  | 0 => .skip
  | n+1 => if hn : n<k then .seq (scan d k n) (step ⟨n,hn⟩) else scan d k n

def matrices {d k : ℕ} (C : Matrix (Fin d) (Fin d) ℝ) (u : Fin k → Fin d → ℝ) :
    ℕ → Matrix (Fin d) (Fin d) ℝ
  | 0 => C
  | n+1 => if hn : n<k then MSManuscriptNumericalShort.short (matrices C u n) (u ⟨n,hn⟩)
      else matrices C u n

theorem scan_safe (d k n : ℕ) (v : Registers d k → ℝ) : (scan d k n).Safe v := by
  induction n with
  | zero => trivial
  | succ n ih =>
    simp only [scan]
    split_ifs with hn
    · exact ⟨ih,step_safe _ _⟩
    · exact ih

theorem scan_constraint {d k : ℕ} (n : ℕ) (v : Registers d k → ℝ) (j : Fin k) :
    constraint ((scan d k n).run v) j=constraint v j := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [scan]
    split_ifs with hn
    · change constraint ((step ⟨n,hn⟩).run ((scan d k n).run v)) j=constraint v j
      rw [step_constraint,ih]
    · exact ih

theorem scan_output {d k : ℕ} (n : ℕ) (hn : n≤k) (v : Registers d k → ℝ) :
    matrix ((scan d k n).run v) ⟨n,by omega⟩=
      matrices (matrix v 0) (constraint v) n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have hnk : n<k := by omega
    simp only [scan,matrices,dif_pos hnk,Program.run]
    have hs := step_output (d:=d) ⟨n,hnk⟩ ((scan d k n).run v)
    have hm : matrix ((scan d k n).run v) (⟨n,hnk⟩ : Fin k).castSucc =
        matrices (matrix v 0) (constraint v) n := ih (by omega)
    rw [hm,scan_constraint] at hs
    exact hs

theorem scan_stored {d k : ℕ} (n : ℕ) (hn : n≤k) (v : Registers d k → ℝ)
    (j : ℕ) (hj : j≤n) :
    matrix ((scan d k n).run v) ⟨j,by omega⟩=
      matrices (matrix v 0) (constraint v) j := by
  induction n with
  | zero =>
    have hj0 : j=0 := by omega
    subst j
    rfl
  | succ n ih =>
    by_cases hje : j=n+1
    · subst j; exact scan_output _ hn v
    · have hnk : n<k := by omega
      simp only [scan,dif_pos hnk,Program.run]
      rw [step_matrix_preserves _ _ _ (by intro he; have hv := congrArg Fin.val he; simpa using hje hv)]
      exact ih (by omega) (by omega)

theorem scan_bound (d k n : ℕ) : (scan d k n).bound≤n*(46*(d+1)^4) := by
  induction n with
  | zero => simp [scan,Program.bound]
  | succ n ih =>
    simp only [scan]
    split_ifs with hn
    · change (scan d k n).bound+(step (d:=d) ⟨n,hn⟩).bound≤_
      have hs := step_bound (d:=d) (⟨n,hn⟩ : Fin k)
      nlinarith
    · exact ih.trans (Nat.mul_le_mul_right _ (by omega))

theorem applyConstraints_append {d : ℕ} (C : Matrix (Fin d) (Fin d) ℝ)
    (us vs : List (Fin d → ℝ)) :
    MSManuscriptNumericalEpochShort.applyConstraints C (us++vs)=
      MSManuscriptNumericalEpochShort.applyConstraints
        (MSManuscriptNumericalEpochShort.applyConstraints C us) vs := by
  induction us generalizing C with
  | nil => rfl
  | cons u us ih => exact ih _

theorem matrices_eq_take {d k : ℕ} (C : Matrix (Fin d) (Fin d) ℝ)
    (u : Fin k → Fin d → ℝ) (n : ℕ) (hn : n≤k) :
    matrices C u n=MSManuscriptNumericalEpochShort.applyConstraints C ((List.ofFn u).take n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have hnk : n<k := by omega
    rw [matrices,dif_pos hnk,ih (by omega),
      List.take_succ_eq_append_getElem (by simpa using hnk),applyConstraints_append]
    simp only [MSManuscriptNumericalEpochShort.applyConstraints,List.getElem_ofFn]

theorem matrices_eq_applyConstraints {d k : ℕ} (C : Matrix (Fin d) (Fin d) ℝ)
    (u : Fin k → Fin d → ℝ) :
    matrices C u k=MSManuscriptNumericalEpochShort.applyConstraints C (List.ofFn u) := by
  have ht : (List.ofFn u).take k=List.ofFn u := List.take_of_length_le (by simp)
  simpa only [ht] using matrices_eq_take C u k le_rfl

/-- The complete finite constraint list is realized by primitive execution with
an explicit polynomial bound. This requires no PSD or nonzero-pivot premise. -/
theorem scan_executes {d k : ℕ} (v : Registers d k → ℝ) :
    ∃w : Registers d k → ℝ, ∃cost≤46*k*(d+1)^4,
      Program.Executes (scan d k k) v w cost ∧
      matrix w ⟨k,by omega⟩=matrices (matrix v 0) (constraint v) k ∧
      ∀j,constraint w j=constraint v j := by
  refine ⟨(scan d k k).run v,(scan d k k).cost v,?_,
    Program.executes_of_safe _ v (scan_safe d k k v),scan_output k le_rfl v,
    fun j => scan_constraint k v j⟩
  have h := ((scan d k k).cost_le_bound v).trans (scan_bound d k k)
  nlinarith

/-- Correctness against the existing exact constrained-short definition, rather
than only against an auxiliary numerical recurrence. -/
theorem scan_executes_constraints {d k : ℕ} (v : Registers d k → ℝ) :
    ∃w : Registers d k → ℝ, ∃cost≤46*k*(d+1)^4,
      Program.Executes (scan d k k) v w cost ∧
      matrix w ⟨k,by omega⟩=
        MSManuscriptNumericalEpochShort.applyConstraints (matrix v 0) (List.ofFn (constraint v)) ∧
      ∀j,constraint w j=constraint v j := by
  simpa only [matrices_eq_applyConstraints] using scan_executes v

end MatrixSpencer.RealRAM.ConstraintScan
