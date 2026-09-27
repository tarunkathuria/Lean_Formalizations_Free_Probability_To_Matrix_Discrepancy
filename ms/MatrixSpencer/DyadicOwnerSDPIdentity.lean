import MatrixSpencer.DyadicSDPTracePower
import MatrixSpencer.DyadicOwnerFunctions
import MatrixSpencer.KSFullManuscriptFidelityBlockUpper

/-!
# Exact semidefinite representation of the dyadic owner potential

The dyadic power uses `m` two-by-two matrix blocks and the fidelity uses one
additional block. The upper bound permits singular densities and sources.
Attainment of the whole SDP follows from the already proved faithful dyadic
density optimizer, so the covariance source may be arbitrary PSD, including
zero. No positive definiteness of the covariance or nonempty source index is
assumed. The attaining points here prove a variational identity; evaluating
them is not part of a numerical solver implementation.
-/

open Matrix Set
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section
namespace MatrixSpencer.DyadicOwnerSDPIdentity

open DyadicSDPTracePower KSFullManuscriptFidelityBlockUpper

variable {n ι : Type*} [Fintype n] [DecidableEq n] [Fintype ι]

/-- All constraints of the dyadic owner SDP. The fidelity variable `Z` is
unrestricted complex; each dyadic auxiliary matrix is constrained by `Chain`.
The zeroth auxiliary matrix is the fixed identity. -/
def Feasible (Ω : Matrix n n ℂ → Matrix n n ℂ) (m : ℕ)
    (S : Matrix n n ℂ) (X : Fin (m + 1) → Matrix n n ℂ)
    (Z : Matrix n n ℂ) : Prop :=
  S ∈ densitySet ∧ Chain S m X ∧
    (Matrix.fromBlocks S Z Zᴴ (Ω S)).PosSemidef

/-- The objective is real-linear in every matrix variable. -/
def value (H : Matrix n n ℂ) (m : ℕ) (θ : ℝ)
    (S : Matrix n n ℂ) (X : Fin (m + 1) → Matrix n n ℂ)
    (Z : Matrix n n ℂ) : ℝ :=
  realTrace (H * S) + 2 * realTrace Z +
    (θ * (2 ^ m : ℝ) / ((2 ^ m : ℝ) - 1)) * realTrace (X (Fin.last m))

def objective (H : Matrix n n ℂ) (Ω : Matrix n n ℂ → Matrix n n ℂ)
    (m : ℕ) (θ : ℝ) (S : Matrix n n ℂ) : ℝ :=
  realTrace (H * S) + 2 * fidelity S (Ω S) + dyadicTsallisRegularizer m θ S

omit [Fintype ι] in
theorem feasible_density {Ω : Matrix n n ℂ → Matrix n n ℂ} {m : ℕ}
    {S : Matrix n n ℂ} {X : Fin (m + 1) → Matrix n n ℂ} {Z : Matrix n n ℂ}
    (h : Feasible Ω m S X Z) : S ∈ densitySet := h.1

omit [Fintype ι] in
theorem coefficient_nonneg {m : ℕ} (hm : 1 ≤ m) {θ : ℝ} (hθ : 0 ≤ θ) :
    0 ≤ θ * (2 ^ m : ℝ) / ((2 ^ m : ℝ) - 1) := by
  have hp : (2 : ℝ) ≤ 2 ^ m := by exact_mod_cast DyadicBoundaryGain.order_ge_two hm
  exact div_nonneg (mul_nonneg hθ (by positivity)) (by linarith)

omit [Fintype ι] in
/-- Every feasible objective is bounded by the actual dyadic owner objective.
This statement covers singular `S` and singular `Ω S`. -/
theorem feasible_value_le {H : Matrix n n ℂ}
    {Ω : Matrix n n ℂ → Matrix n n ℂ} {m : ℕ} {θ : ℝ}
    {S : Matrix n n ℂ} {X : Fin (m + 1) → Matrix n n ℂ} {Z : Matrix n n ℂ}
    (hm : 1 ≤ m) (hθ : 0 ≤ θ) (h : Feasible Ω m S X Z) :
    value H m θ S X Z ≤ objective H Ω m θ S := by
  have hz := block_trace_le_fidelity h.2.2
  have hx := chain_trace_le h.1.1 h.2.1
  have ht := mul_le_mul_of_nonneg_left hx (coefficient_nonneg hm hθ)
  unfold value objective dyadicTsallisRegularizer
  change realTrace (H * S) + 2 * realTrace Z + _ ≤
    realTrace (H * S) + 2 * fidelity S (Ω S) +
      (θ * (2 ^ m : ℝ) / ((2 ^ m : ℝ) - 1)) * realTrace (power m S)
  linarith

omit [Fintype ι] in
/-- For every faithful density, the auxiliary matrices attain its exact
objective, even if the source is singular. -/
theorem fixed_density_attainment {H : Matrix n n ℂ}
    {Ω : Matrix n n ℂ → Matrix n n ℂ} {m : ℕ} {θ : ℝ}
    {S : Matrix n n ℂ} (hS : S ∈ densitySet) (hp : S.PosDef)
    (hΩ : (Ω S).PosSemidef) :
    ∃ X : Fin (m + 1) → Matrix n n ℂ, ∃ Z : Matrix n n ℂ,
      Feasible Ω m S X Z ∧ value H m θ S X Z = objective H Ω m θ S := by
  obtain ⟨Z, hZ, ht⟩ := KSFullManuscriptFidelityBlock.exists_attaining_block hp hΩ
  refine ⟨canonical S m, Z, ⟨hS, canonical_chain hS.1 m, hZ⟩, ?_⟩
  simp only [value, objective, canonical_last, ht, power, dyadicTsallisRegularizer]

theorem feasible_value_le_densityPotential [Nonempty n]
    {H : Matrix n n ℂ} {B : ι → Matrix n n ℂ} {m : ℕ} {θ : ℝ}
    {S : Matrix n n ℂ} {X : Fin (m + 1) → Matrix n n ℂ} {Z : Matrix n n ℂ}
    (hm : 1 ≤ m) (hθ : 0 ≤ θ) (h : Feasible (krausChannel B) m S X Z) :
    value H m θ S X Z ≤ dyadicDensityPotential H B m θ :=
  (feasible_value_le hm hθ h).trans
    (dyadicDensityObjective_le_potential H B m θ h.1)

/-- The actual dyadic density potential is the attained maximum of this SDP.
There is no full-rank premise on the Kraus source. -/
theorem kraus_SDP_exact [Nonempty n] (H : Matrix n n ℂ) (B : ι → Matrix n n ℂ)
    {m : ℕ} (hm : 1 ≤ m) {θ : ℝ} (hθ : 0 < θ) :
    ∃ S : Matrix n n ℂ, ∃ X : Fin (m + 1) → Matrix n n ℂ, ∃ Z : Matrix n n ℂ,
      Feasible (krausChannel B) m S X Z ∧
      value H m θ S X Z = dyadicDensityPotential H B m θ ∧
      ∀ S' X' Z', Feasible (krausChannel B) m S' X' Z' →
        value H m θ S' X' Z' ≤ value H m θ S X Z := by
  let S := dyadicDensityOptimizer H B m θ
  have hs : S ∈ densitySet := dyadicDensityOptimizer_mem H B m θ
  have hp : S.PosDef := dyadicDensityOptimizer_posDef H B m hm θ hθ
  obtain ⟨X, Z, hf, hv⟩ := fixed_density_attainment (H := H) (m := m) (θ := θ)
    hs hp (krausChannel_posSemidef B hs.1)
  have he : value H m θ S X Z = dyadicDensityPotential H B m θ := by
    rw [hv, dyadicDensityPotential_eq_optimizer]
    rfl
  refine ⟨S, X, Z, hf, he, ?_⟩
  intro S' X' Z' h'
  rw [he]
  exact feasible_value_le_densityPotential hm hθ.le h'

/-- Real values achieved by feasible SDP matrix variables. -/
def values (H : Matrix n n ℂ) (Ω : Matrix n n ℂ → Matrix n n ℂ)
    (m : ℕ) (θ : ℝ) : Set ℝ :=
  {v | ∃ S : Matrix n n ℂ, ∃ X : Fin (m + 1) → Matrix n n ℂ,
    ∃ Z : Matrix n n ℂ, Feasible Ω m S X Z ∧ value H m θ S X Z = v}

theorem kraus_isGreatest [Nonempty n] (H : Matrix n n ℂ) (B : ι → Matrix n n ℂ)
    {m : ℕ} (hm : 1 ≤ m) {θ : ℝ} (hθ : 0 < θ) :
    IsGreatest (values H (krausChannel B) m θ) (dyadicDensityPotential H B m θ) := by
  obtain ⟨S, X, Z, hf, hv, _⟩ := kraus_SDP_exact H B hm hθ
  refine ⟨⟨S, X, Z, hf, hv⟩, ?_⟩
  rintro v ⟨S', X', Z', hf', rfl⟩
  exact feasible_value_le_densityPotential hm hθ.le hf'

theorem kraus_sSup_eq [Nonempty n] (H : Matrix n n ℂ) (B : ι → Matrix n n ℂ)
    {m : ℕ} (hm : 1 ≤ m) {θ : ℝ} (hθ : 0 < θ) :
    sSup (values H (krausChannel B) m θ) = dyadicDensityPotential H B m θ :=
  (kraus_isGreatest H B hm hθ).csSup_eq

section Covariance

variable [DecidableEq ι]

theorem covariance_feasible_iff (A : ι → Matrix n n ℂ)
    (hA : ∀ i, (A i).IsHermitian) {C : Matrix ι ι ℝ} (hC : C.PosSemidef)
    {m : ℕ} {S : Matrix n n ℂ} {X : Fin (m + 1) → Matrix n n ℂ}
    {Z : Matrix n n ℂ} :
    Feasible (covarianceSource A C) m S X Z ↔
      Feasible (krausChannel (covarianceKraus A C)) m S X Z := by
  unfold Feasible
  rw [covarianceSource_eq_kraus A hA hC]

theorem feasible_value_le_ownerPotential [Nonempty n]
    (H : Matrix n n ℂ) (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).IsHermitian)
    {C : Matrix ι ι ℝ} (hC : C.PosSemidef) {m : ℕ} (hm : 1 ≤ m)
    {θ : ℝ} (hθ : 0 ≤ θ) {S : Matrix n n ℂ}
    {X : Fin (m + 1) → Matrix n n ℂ} {Z : Matrix n n ℂ}
    (h : Feasible (covarianceSource A C) m S X Z) :
    value H m θ S X Z ≤ dyadicOwnerPotential H A C m θ := by
  change value H m θ S X Z ≤ regularizedOwnerPotential H A C (dyadicTsallisRegularizer m θ)
  rw [regularizedOwnerPotential_eq_dyadicDensityPotential H A hA hC]
  exact feasible_value_le_densityPotential hm hθ ((covariance_feasible_iff A hA hC).mp h)

/-- Direct representation of the original covariance owner potential. The
covariance can be singular, zero, or indexed by an empty source family. -/
theorem owner_SDP_exact [Nonempty n] (H : Matrix n n ℂ) (A : ι → Matrix n n ℂ)
    (hA : ∀ i, (A i).IsHermitian) {C : Matrix ι ι ℝ} (hC : C.PosSemidef)
    {m : ℕ} (hm : 1 ≤ m) {θ : ℝ} (hθ : 0 < θ) :
    ∃ S : Matrix n n ℂ, ∃ X : Fin (m + 1) → Matrix n n ℂ, ∃ Z : Matrix n n ℂ,
      Feasible (covarianceSource A C) m S X Z ∧
      value H m θ S X Z = dyadicOwnerPotential H A C m θ ∧
      ∀ S' X' Z', Feasible (covarianceSource A C) m S' X' Z' →
        value H m θ S' X' Z' ≤ value H m θ S X Z := by
  obtain ⟨S, X, Z, hf, hv, hmax⟩ := kraus_SDP_exact H (covarianceKraus A C) hm hθ
  refine ⟨S, X, Z, (covariance_feasible_iff A hA hC).mpr hf, ?_, ?_⟩
  · change value H m θ S X Z = regularizedOwnerPotential H A C (dyadicTsallisRegularizer m θ)
    rw [regularizedOwnerPotential_eq_dyadicDensityPotential H A hA hC]
    exact hv
  · intro S' X' Z' h'
    exact hmax S' X' Z' ((covariance_feasible_iff A hA hC).mp h')

theorem owner_isGreatest [Nonempty n] (H : Matrix n n ℂ) (A : ι → Matrix n n ℂ)
    (hA : ∀ i, (A i).IsHermitian) {C : Matrix ι ι ℝ} (hC : C.PosSemidef)
    {m : ℕ} (hm : 1 ≤ m) {θ : ℝ} (hθ : 0 < θ) :
    IsGreatest (values H (covarianceSource A C) m θ) (dyadicOwnerPotential H A C m θ) := by
  obtain ⟨S, X, Z, hf, hv, _⟩ := owner_SDP_exact H A hA hC hm hθ
  refine ⟨⟨S, X, Z, hf, hv⟩, ?_⟩
  rintro v ⟨S', X', Z', hf', rfl⟩
  exact feasible_value_le_ownerPotential H A hA hC hm hθ.le hf'

/-- Equality with the SDP supremum, together with `owner_SDP_exact` proving
that this supremum is genuinely attained. -/
theorem owner_sSup_eq [Nonempty n] (H : Matrix n n ℂ) (A : ι → Matrix n n ℂ)
    (hA : ∀ i, (A i).IsHermitian) {C : Matrix ι ι ℝ} (hC : C.PosSemidef)
    {m : ℕ} (hm : 1 ≤ m) {θ : ℝ} (hθ : 0 < θ) :
    sSup (values H (covarianceSource A C) m θ) = dyadicOwnerPotential H A C m θ :=
  (owner_isGreatest H A hA hC hm hθ).csSup_eq

end Covariance

end MatrixSpencer.DyadicOwnerSDPIdentity
