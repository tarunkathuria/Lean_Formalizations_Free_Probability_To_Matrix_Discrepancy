import MatrixSpencer.KSSpinLocalState
import MatrixSpencer.KSSpinLiveSource
import MatrixSpencer.KSFinalAssembly

/-! Every maximally frozen minimum of the actual spin potential is a vertex. -/

open Matrix Filter Topology Set
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section
namespace MatrixSpencer.KSSpinVertex
open KSPotentialModels KSLiveCurve

variable {N : ℕ} {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
local instance {k : Type*} [Fintype k] [DecidableEq k] : CStarAlgebra (Matrix k k ℂ) := {}

theorem maxFrozen_isVertex (v : Fin N → n → ℂ) {θ : ℝ} (hθ : 0 < θ)
    {x : Fin N → ℝ}
    (hx : MaxFrozenMinimum 1 (spinPotential (fun i => KSRankOne.atom (v i)) θ) x) :
    ksVertex 1 x := by
  classical
  rcases isEmpty_or_nonempty (Live 1 x) with hI | hI
  · letI := hI
    intro i
    have hi : ¬ |x i| < 1 := fun hi => isEmptyElim (⟨i, hi⟩ : Live 1 x)
    have habs : |x i| = 1 := le_antisymm (abs_le.mpr ⟨hx.1.1 i, hx.1.2 i⟩) (not_lt.mp hi)
    rcases le_total (x i) 0 with ht | ht
    · left
      rw [abs_of_nonpos ht] at habs
      linarith
    · right
      rwa [abs_of_nonneg ht] at habs
  · letI := hI
    let A := fun i => KSRankOne.atom (v i)
    let vl : Live 1 x → n → ℂ := fun i => v i
    let xl : Live 1 x → ℝ := fun i => x i
    let Q := center A x
    let c := naturalOwners 64 x
    let cl : Live 1 x → ℝ := fun i => 64 * (1 - xl i ^ 2)
    have hA : ∀ i, (A i).IsHermitian := fun i => KSRankOne.atom_isHermitian _
    have hc : ∀ i, 0 ≤ c i := naturalOwners_nonneg (by norm_num) le_rfl hx.1
    have hxl : ∀ i : Live 1 x, |xl i| < 1 := fun i => i.property
    have hcl : ∀ i, 0 < cl i := KSSpinLocalState.owners_pos hxl
    have hvl : ∀ i, vl i ≠ 0 := fun i => KSFinalAssembly.spin_live_vector_ne_zero v θ hx i i.property
    obtain ⟨S, hSmem, hS, _, hmax⟩ := exists_ownerOptimizer (signedLift Q) (KSSpinSource.family A)
      (KSSpinSource.family_isHermitian A hA) (KSSpinSource.coefficientCovariance_posSemidef hc) hθ
    let Sh : selfAdjoint (Matrix (n ⊕ n) (n ⊕ n) ℂ) := ⟨S, hS.isHermitian⟩
    have hobjective (T : Matrix (n ⊕ n) (n ⊕ n) ℂ) :
        ownerObjective (signedLift Q) (KSSpinSource.family A) (KSSpinSource.coefficientCovariance c) θ T =
        ownerObjective (signedLift Q) (KSSpinSource.family (KSSpinLocalState.atoms vl))
          (KSSpinSource.coefficientCovariance cl) θ T :=
      KSSpinLiveSource.objective_restrict v 1 x c (naturalOwner_dead hx.1 64) (signedLift Q) θ T
    have hmaxl : ∀ T ∈ densitySet,
        ownerObjective (signedLift Q) (KSSpinSource.family (KSSpinLocalState.atoms vl))
          (KSSpinSource.coefficientCovariance cl) θ T ≤
        ownerObjective (signedLift Q) (KSSpinSource.family (KSSpinLocalState.atoms vl))
          (KSSpinSource.coefficientCovariance cl) θ S := by
      intro T hT
      rw [← hobjective T, ← hobjective S]
      exact hmax T hT
    let V := KSSpinCompression.embedding (KSSpinLocalState.atoms vl)
    let Z := KSSpinLocalState.stateTransport vl xl S
    have hV : Vᴴ * V = 1 := KSSpinCompression.embedding_isometry _
    have hS0 := KSSupportSymmetry.compress_posDef V hV hS
    have hM := KSSpinCompression.compressed_source_posDef vl hcl hS
    have hZ : Z.PosDef := transportOptimizer_posDef hS0 hM
    have hsolve := transportOptimizer_solve hS0 hM
    have he (T : Matrix (n ⊕ n) (n ⊕ n) ℂ) :
        covarianceSource (KSSpinSource.family A) (KSSpinSource.coefficientCovariance c) T =
        covarianceSource (KSSpinSource.family (KSSpinLocalState.atoms vl))
          (KSSpinSource.coefficientCovariance cl) T :=
      KSSpinLiveSource.source_at_state v hx.1 T
    have hmaxd : ∀ T ∈ densitySet,
        densityObjective (signedLift Q)
          (covarianceKraus (KSSpinSource.family A) (KSSpinSource.coefficientCovariance c)) θ T ≤
        densityObjective (signedLift Q)
          (covarianceKraus (KSSpinSource.family A) (KSSpinSource.coefficientCovariance c)) θ Sh := by
      intro T hT
      rw [← ownerObjective_eq_densityObjective _ _ (KSSpinSource.family_isHermitian A hA)
        (KSSpinSource.coefficientCovariance_posSemidef hc),
        ← ownerObjective_eq_densityObjective _ _ (KSSpinSource.family_isHermitian A hA)
        (KSSpinSource.coefficientCovariance_posSemidef hc)]
      exact hmax T hT
    have hfail : ∀ i : Live 1 x, cl i * realTrace (Z * KSSpinCompression.compressedAtom
        (KSSpinLocalState.atoms vl) i) < 1 - |xl i| := by
      intro i
      have hf := KSSpinChosenRetirement.maxFrozen_noSafe_in_frame v hθ hx V hV Sh hS hSmem.2 hmaxd hZ
        (by change (Vᴴ * covarianceSource (KSSpinSource.family A) _ S * V).PosDef
            rw [he S]; exact hM)
        (by change Z * (Vᴴ * covarianceSource (KSSpinSource.family A) _ S * V) * Z = Vᴴ * S * V
            rw [he S]; exact hsolve)
        (by intro T hT; change V * (Vᴴ * covarianceSource (KSSpinSource.family A) _ T * V) * Vᴴ = _
            rw [he T]; exact KSSpinCompression.source_reconstruct vl cl T)
        i i.property
      change cl i * realTrace (KSSpinSource.doubled (KSRankOne.atom (vl i)) * (V * Z * Vᴴ)) < _ at hf
      have hp : realTrace (KSSpinSource.doubled (KSRankOne.atom (vl i)) * (V * Z * Vᴴ)) =
          realTrace (KSSpinCompression.compressedAtom (KSSpinLocalState.atoms vl) i * Z) :=
        KSSpinCompression.transport_probe (KSSpinLocalState.atoms vl) Z i
      rw [hp, realTrace_mul_comm] at hf
      exact hf
    obtain ⟨h, _, hn⟩ := KSSpinLocalState.exists_not_isLocalMin_curve Q (center_isHermitian A hA x)
      vl hvl xl hxl hθ S hS hSmem.2 hmaxl hfail
    exfalso
    apply hn
    have hm := isLocalMin_path hx.1 (spinPotential A θ) (fun y hy => hx.2.1 hy) h
    have hp : (fun t => spinPotential A θ (path 1 x h t)) =
        KSSpinLocalState.curvePotential Q vl θ xl h := by
      funext t
      exact KSSpinLiveSource.potential_path v hx.1 θ h t
    rwa [hp] at hm

end MatrixSpencer.KSSpinVertex
