import MatrixSpencer.RectangularRidgePotential
import MatrixSpencer.DyadicOwnerSDPIdentity

/-!
# The rectangular square-root ridge uses the existing SDP variables

The first matrix in the dyadic chain already represents the square root.
Adding its trace to the affine objective therefore adds no variables and no
matrix inequalities. Both trace powers and fidelity are attained together.
-/
open Matrix Set
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section
namespace MatrixSpencer.RectangularRidgeSDP
open DyadicSDPTracePower DyadicOwnerSDPIdentity
variable {n ι : Type*} [Fintype n] [DecidableEq n] [Fintype ι]

def value (H : Matrix n n ℂ) (m : ℕ) (θ κ : ℝ) (hm : 1 ≤ m)
    (S : Matrix n n ℂ) (X : Fin (m + 1) → Matrix n n ℂ) (Z : Matrix n n ℂ) : ℝ :=
  DyadicOwnerSDPIdentity.value H m θ S X Z + 2 * κ * realTrace (X ⟨1, by omega⟩)

omit [Fintype ι] in
theorem chain_first_trace_le {S : Matrix n n ℂ} (hS : S.PosSemidef)
    {m : ℕ} (hm : 1 ≤ m) {X : Fin (m + 1) → Matrix n n ℂ} (hX : Chain S m X) :
    realTrace (X ⟨1, by omega⟩) ≤ realTrace (CFC.sqrt S) := by
  let Y : Fin 2 → Matrix n n ℂ := fun j => X ⟨j.val, by omega⟩
  have hy : Chain S 1 Y := by
    refine ⟨hX.1, ?_⟩
    intro j
    have hj : j = 0 := Subsingleton.elim _ _
    subst j
    exact hX.2 ⟨0, by omega⟩
  have hh := chain_trace_le hS hy
  simpa [Y, power, dyadicRoot_succ, dyadicRoot_zero] using hh

omit [Fintype ι] in
theorem canonical_first (S : Matrix n n ℂ) {m : ℕ} (hm : 1 ≤ m) :
    canonical S m ⟨1, by omega⟩ = CFC.sqrt S := by
  simp [canonical, power, dyadicRoot_succ, dyadicRoot_zero]

theorem feasible_value_le (H : Matrix n n ℂ) (B : ι → Matrix n n ℂ)
    {m : ℕ} (hm : 1 ≤ m) {θ κ : ℝ} (hθ : 0 ≤ θ) (hκ : 0 ≤ κ)
    {S : Matrix n n ℂ} {X : Fin (m + 1) → Matrix n n ℂ} {Z : Matrix n n ℂ}
    (hf : Feasible (krausChannel B) m S X Z) :
    value H m θ κ hm S X Z ≤ RectangularRidgePotential.objective H B m θ κ S := by
  have hd := DyadicOwnerSDPIdentity.feasible_value_le (H := H) hm hθ hf
  have hr := mul_le_mul_of_nonneg_left (chain_first_trace_le hf.1.1 hm hf.2.1)
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hκ)
  exact add_le_add hd hr

theorem fixed_density_attainment (H : Matrix n n ℂ) (B : ι → Matrix n n ℂ)
    {m : ℕ} (hm : 1 ≤ m) (θ κ : ℝ) {S : Matrix n n ℂ}
    (hS : S ∈ densitySet) (hp : S.PosDef) :
    ∃ X : Fin (m + 1) → Matrix n n ℂ, ∃ Z : Matrix n n ℂ,
      Feasible (krausChannel B) m S X Z ∧
      value H m θ κ hm S X Z = RectangularRidgePotential.objective H B m θ κ S := by
  obtain ⟨Z, hZ, ht⟩ := KSFullManuscriptFidelityBlock.exists_attaining_block hp
    (krausChannel_posSemidef B hS.1)
  refine ⟨canonical S m, Z, ⟨hS, canonical_chain hS.1 m, hZ⟩, ?_⟩
  simp only [value, DyadicOwnerSDPIdentity.value, RectangularRidgePotential.objective,
    dyadicDensityObjective, canonical_first S hm, canonical_last, ht,
    power, dyadicTsallisRegularizer]

/-- Exact attained SDP identity for the modified objective, allowing singular
or zero covariance sources. The feasible set is unchanged. -/
theorem SDP_exact [Nonempty n] (H : Matrix n n ℂ) (B : ι → Matrix n n ℂ)
    {m : ℕ} (hm : 1 ≤ m) {θ κ : ℝ} (hθ : 0 < θ) (hκ : 0 ≤ κ) :
    ∃ S : Matrix n n ℂ, ∃ X : Fin (m + 1) → Matrix n n ℂ, ∃ Z : Matrix n n ℂ,
      Feasible (krausChannel B) m S X Z ∧
      value H m θ κ hm S X Z = RectangularRidgePotential.potential H B m θ κ ∧
      ∀ S' X' Z', Feasible (krausChannel B) m S' X' Z' →
        value H m θ κ hm S' X' Z' ≤ value H m θ κ hm S X Z := by
  let S := RectangularRidgePotential.optimizer H B m θ κ
  have hs : S ∈ densitySet := RectangularRidgePotential.optimizer_mem H B m θ κ
  have hp : S.PosDef := RectangularRidgePotential.optimizer_posDef H B hm hθ hκ
  obtain ⟨X, Z, hf, hv⟩ := fixed_density_attainment H B hm θ κ hs hp
  have he : value H m θ κ hm S X Z = RectangularRidgePotential.potential H B m θ κ := by
    rw [hv, RectangularRidgePotential.potential_eq_optimizer]
  refine ⟨S, X, Z, hf, he, ?_⟩
  intro S' X' Z' h'
  rw [he]
  exact (feasible_value_le H B hm hθ.le hκ h').trans
    (RectangularRidgePotential.objective_le_potential H B m θ κ h'.1)

end MatrixSpencer.RectangularRidgeSDP
