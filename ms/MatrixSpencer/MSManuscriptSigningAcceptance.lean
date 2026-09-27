import MatrixSpencer.KSComplexNorm
import MatrixSpencer.MSManuscriptAcceptanceRetry
import MatrixSpencer.MSManuscriptSamplerTools

/-!
# Numerical full-signing acceptance and retries

Every original sign is checked by a finite scan and the matrix norm is checked
by the finite realified Jacobi upper report. Existing epoch/full-process failure
is preserved. The input sampler's good-output probability is an explicit
premise for the numerical epoch/full-signing construction to discharge.
No analytically chosen successful signing is used here.
-/

open Matrix
open scoped BigOperators Matrix.Norms.L2Operator
noncomputable section
namespace MatrixSpencer.MSManuscriptSigningAcceptance

open MSManuscriptAdaptive
attribute [local instance] Classical.propDecidable
variable {N d : ℕ}

def signedMatrix (A : Fin N → Matrix (Fin d) (Fin d) ℂ) (σ : Fin N → ℝ) :
    Matrix (Fin d) (Fin d) ℂ := ∑ i, σ i • A i

theorem signedMatrix_isHermitian (A : Fin N → Matrix (Fin d) (Fin d) ℂ)
    (hA : ∀ i, (A i).IsHermitian) (σ : Fin N → ℝ) :
    (signedMatrix A σ).IsHermitian := by
  change (∑ i, σ i • A i)ᴴ = ∑ i, σ i • A i
  simp only [Matrix.conjTranspose_sum, Matrix.conjTranspose_smul, star_trivial,
    fun i => (hA i).eq]

/-- All original labels, then the computed norm report. -/
def accepts (A : Fin N → Matrix (Fin d) (Fin d) ℂ) (ν bound : ℝ) (σ : Fin N → ℝ) : Bool :=
  (List.finRange N).all (fun i => decide (σ i = 1) || decide (σ i = -1)) &&
    KSComplexNorm.accepts (signedMatrix A σ) ν bound

theorem accepts_iff (A : Fin N → Matrix (Fin d) (Fin d) ℂ) (ν bound : ℝ) (σ : Fin N → ℝ) :
    accepts A ν bound σ = true ↔ (∀ i, σ i = 1 ∨ σ i = -1) ∧
      KSComplexNorm.report (signedMatrix A σ) ν ≤ bound := by
  simp [accepts, List.all_eq_true, KSComplexNorm.accepts]

theorem accepts_sound (A : Fin N → Matrix (Fin d) (Fin d) ℂ)
    (hA : ∀ i, (A i).IsHermitian) {ν bound : ℝ} (hν : 0 < ν) (σ : Fin N → ℝ)
    (ha : accepts A ν bound σ = true) :
    (∀ i, σ i = 1 ∨ σ i = -1) ∧ ‖signedMatrix A σ‖ ≤ bound := by
  obtain ⟨hs,hr⟩ := (accepts_iff A ν bound σ).mp ha
  exact ⟨hs,KSComplexNorm.accepted_norm_le _ (signedMatrix_isHermitian A hA σ) hν hr⟩

theorem good_accepted (A : Fin N → Matrix (Fin d) (Fin d) ℂ)
    (hA : ∀ i, (A i).IsHermitian) {ν bound goodBound : ℝ} (hν : 0 < ν)
    (hallow : goodBound+ν ≤ bound) (σ : Fin N → ℝ)
    (hs : ∀ i, σ i = 1 ∨ σ i = -1) (hg : ‖signedMatrix A σ‖ ≤ goodBound) :
    accepts A ν bound σ = true :=
  (accepts_iff A ν bound σ).mpr ⟨hs,
    KSComplexNorm.good_norm_accepted _ (signedMatrix_isHermitian A hA σ) hν hg hallow⟩

/-- A failed epoch/full process cannot pass the final filter. -/
def acceptsOption (A : Fin N → Matrix (Fin d) (Fin d) ℂ) (ν bound : ℝ) :
    Option (Fin N → ℝ) → Bool
  | none => false
  | some σ => accepts A ν bound σ

def Good (A : Fin N → Matrix (Fin d) (Fin d) ℂ) (bound : ℝ) :
    Option (Fin N → ℝ) → Prop
  | none => False
  | some σ => (∀ i, σ i = 1 ∨ σ i = -1) ∧ ‖signedMatrix A σ‖ ≤ bound

/-- Independent repetitions of the actual input sampler, returning the first
candidate that passes both numerical tests. -/
def output (A : Fin N → Matrix (Fin d) (Fin d) ℂ) (ν bound : ℝ)
    (P : Sampler (Option (Fin N → ℝ))) (r : ℕ) : Sampler (Option (Fin N → ℝ)) :=
  (MSManuscriptAcceptanceRetry.output P (acceptsOption A ν bound) r).map Option.join

theorem output_sound (A : Fin N → Matrix (Fin d) (Fin d) ℂ)
    (hA : ∀ i, (A i).IsHermitian) {ν bound : ℝ} (hν : 0 < ν)
    (P : Sampler (Option (Fin N → ℝ))) (r : ℕ)
    (z : (output A ν bound P r).Draws) (σ : Fin N → ℝ)
    (ho : (output A ν bound P r).value z = some σ) :
    (∀ i, σ i = 1 ∨ σ i = -1) ∧
      ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (∑ i, σ i • A i)‖ ≤ bound := by
  change ((MSManuscriptAcceptanceRetry.output P (acceptsOption A ν bound) r).value z).join = some σ at ho
  have hinner : (MSManuscriptAcceptanceRetry.output P (acceptsOption A ν bound) r).value z = some (some σ) := by
    cases he : (MSManuscriptAcceptanceRetry.output P (acceptsOption A ν bound) r).value z with
    | none => simp [he] at ho
    | some a => cases a <;> simpa [he] using ho
  have h := MSManuscriptAcceptanceRetry.output_sound P (acceptsOption A ν bound)
    (fun a => match a with | none => False | some s => (∀ i, s i = 1 ∨ s i = -1) ∧ ‖signedMatrix A s‖ ≤ bound)
    (by
      intro w hw
      cases he : P.value w with
      | none => simp [he, acceptsOption] at hw
      | some s => simpa [he] using accepts_sound A hA hν s (by simpa [he, acceptsOption] using hw))
    r z (some σ) hinner
  exact h

/-- Accepted nested output is never `some none`, so flattening preserves the
literal success event and every product weight. -/
theorem output_isSome (A : Fin N → Matrix (Fin d) (Fin d) ℂ) (ν bound : ℝ)
    (P : Sampler (Option (Fin N → ℝ))) (r : ℕ) (z : (output A ν bound P r).Draws) :
    ((output A ν bound P r).value z).isSome =
      ((MSManuscriptAcceptanceRetry.output P (acceptsOption A ν bound) r).value z).isSome := by
  have hnon : (MSManuscriptAcceptanceRetry.output P (acceptsOption A ν bound) r).value z ≠ some none := by
    intro he
    have h := MSManuscriptAcceptanceRetry.output_sound P (acceptsOption A ν bound)
      (fun a => a.isSome = true)
      (by intro w hw; cases he : P.value w <;> simp_all [acceptsOption]) r z none he
    simp at h
  change (((MSManuscriptAcceptanceRetry.output P (acceptsOption A ν bound) r).value z).join).isSome = _
  cases he : (MSManuscriptAcceptanceRetry.output P (acceptsOption A ν bound) r).value z with
  | none => rfl
  | some a => cases a <;> simp_all

/-- The full-process quality premise is explicit; norm-report accuracy,
finite sign checking, failure preservation, and retry amplification are proved. -/
theorem output_event_probability_ge (A : Fin N → Matrix (Fin d) (Fin d) ℂ)
    (hA : ∀ i, (A i).IsHermitian) {ν bound goodBound p : ℝ} (hν : 0 < ν)
    (hallow : goodBound+ν ≤ bound) (P : Sampler (Option (Fin N → ℝ)))
    (hgood : p ≤ P.expectation (fun a => if Good A goodBound a then 1 else 0)) (r : ℕ) :
    1-(1-p)^r ≤ ∑ z : (output A ν bound P r).Draws, (output A ν bound P r).weight z *
      (if ((output A ν bound P r).value z).isSome then 1 else 0) := by
  have hp := MSManuscriptAcceptanceRetry.acceptance_probability_ge P (acceptsOption A ν bound)
    (Good A goodBound) hgood (by
      intro z hz
      cases he : P.value z with
      | none => simp [he, Good] at hz
      | some σ =>
        obtain ⟨hs,hn⟩ := (show (∀ i, σ i = 1 ∨ σ i = -1) ∧ ‖signedMatrix A σ‖ ≤ goodBound from by simpa [he, Good] using hz)
        simpa [he, acceptsOption] using good_accepted A hA hν hallow σ hs hn)
  have h := MSManuscriptAcceptanceRetry.output_event_probability_ge P (acceptsOption A ν bound) hp r
  convert h using 1
  apply Finset.sum_congr rfl
  intro z _
  rw [output_isSome]
  rfl

end MatrixSpencer.MSManuscriptSigningAcceptance
