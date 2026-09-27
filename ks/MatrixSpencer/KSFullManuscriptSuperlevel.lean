import MatrixSpencer.KSFullManuscriptAffinePSD

/-!
# Computed affine SDP superlevel separation

The actual query first runs symmetric elimination on the affine matrix pencil,
then tests the linear objective. A zero objective with an infeasible threshold
has empty target; a specified nonzero fallback normal handles this case. The
known feasible point belongs only to the base spectrahedron, so this routine
is defined and certified even at infeasible objective thresholds.
-/

open scoped InnerProductSpace
noncomputable section
namespace MatrixSpencer.KSFullManuscriptSuperlevel

open KSFullManuscriptAffinePSD KSFullManuscriptEllipsoidRun
variable {ℓ n : ℕ}

def objective (c : Space ℓ) (b : ℝ) (x : Space ℓ) : ℝ := b + ⟪c, x⟫_ℝ

def target (D : Data ℓ n) (c : Space ℓ) (b t : ℝ) : Set (Space ℓ) :=
  {x | x ∈ KSFullManuscriptAffinePSD.target D ∧ t ≤ objective c b x}

def query (D : Data ℓ n) (c fallback : Space ℓ) (b t : ℝ) (x : Space ℓ) :
    Option (Space ℓ) :=
  match KSFullManuscriptAffinePSD.query D x with
  | some g => some g
  | none => if t ≤ objective c b x then none else some (if c = 0 then fallback else -c)

theorem query_none_iff (D : Data ℓ n) (c fallback : Space ℓ) (b t : ℝ) (x : Space ℓ) :
    query D c fallback b t x = none ↔ x ∈ target D c b t := by
  unfold query target
  cases hq : KSFullManuscriptAffinePSD.query D x with
  | none =>
    have hx := (KSFullManuscriptAffinePSD.query_none_iff D x).mp hq
    simp [hx]
  | some g =>
    have hx : x ∉ KSFullManuscriptAffinePSD.target D := by
      intro hx
      have hh := (KSFullManuscriptAffinePSD.query_none_iff D x).mpr hx
      simp [hq] at hh
    simp [hx]

theorem objective_cut {c x y : Space ℓ} {b t : ℝ}
    (hx : ¬t ≤ objective c b x) (hy : t ≤ objective c b y) :
    ⟪-c, y - x⟫_ℝ ≤ 0 := by
  simp only [inner_neg_left, inner_sub_right, objective] at *
  linarith

/-- Every branch is the specified arithmetic PSD/objective test. The feasible
base point and nonzero fallback certify normals; neither chooses a cut. -/
def procedure (D : Data ℓ n) (c fallback : Space ℓ) (b t : ℝ)
    (z : Space ℓ) (hz : z ∈ KSFullManuscriptAffinePSD.target D) (hf : fallback ≠ 0) :
    SeparationProcedure (target D c b t) where
  query := query D c fallback b t
  feasible := fun x hx => (query_none_iff D c fallback b t x).mp hx
  separates := by
    intro x g hg
    unfold query at hg
    cases hq : KSFullManuscriptAffinePSD.query D x with
    | some a =>
      simp only [hq, Option.some.injEq] at hg
      subst g
      have ha := (KSFullManuscriptAffinePSD.procedure D z hz).separates x a hq
      exact ⟨ha.1, fun y hy => ha.2 y hy.1⟩
    | none =>
      simp only [hq] at hg
      split_ifs at hg with ht hc
      · simp only [Option.some.injEq] at hg
        subst g
        refine ⟨hf, fun y hy => ?_⟩
        have hx : ¬t ≤ b := by simpa [objective, hc] using ht
        have hy' : t ≤ b := by simpa [objective, hc] using hy.2
        exact False.elim (hx hy')
      · simp only [Option.some.injEq] at hg
        subst g
        exact ⟨neg_ne_zero.mpr hc, fun y hy => objective_cut ht hy.2⟩

end MatrixSpencer.KSFullManuscriptSuperlevel
