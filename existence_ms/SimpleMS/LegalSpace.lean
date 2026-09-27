import SimpleMS.FlatCovariance

open Matrix
open scoped BigOperators MatrixOrder
noncomputable section
namespace SimpleMS
variable {N : ℕ}

/-- Frozen coordinates and radial orthogonality in original label coordinates. -/
def constraintMap (F : Finset (Fin N)) (x : EuclideanSpace ℝ (Fin N)) :
    EuclideanSpace ℝ (Fin N) →ₗ[ℝ] (({i // i ∈ F} → ℝ) × ℝ) where
  toFun v := (fun i => v i.val, inner ℝ x v)
  map_add' u v := by ext i <;> simp [inner_add_right]
  map_smul' a v := by ext i <;> simp [inner_smul_right]

def legalSpace (F : Finset (Fin N)) (x : EuclideanSpace ℝ (Fin N)) := LinearMap.ker (constraintMap F x)

lemma mem_legalSpace (F : Finset (Fin N)) (x v : EuclideanSpace ℝ (Fin N)) :
    v ∈ legalSpace F x ↔ (∀ i∈F,v i=0) ∧ inner ℝ x v=0 := by
  change (constraintMap F x) v=0 ↔ _
  simp only [constraintMap,LinearMap.coe_mk,AddHom.coe_mk,Prod.mk.injEq,Prod.zero_eq_mk]
  constructor
  · rintro ⟨hf,hx⟩
    exact ⟨fun i hi => congr_fun hf ⟨i,hi⟩,hx⟩
  · rintro ⟨hf,hx⟩
    exact ⟨funext (fun i => hf i.val i.property),hx⟩

lemma legalSpace_codim (F : Finset (Fin N)) (x : EuclideanSpace ℝ (Fin N)) :
    Module.finrank ℝ (legalSpace F x)ᗮ ≤ F.card+1 := by
  have hr := (constraintMap F x).finrank_range_add_finrank_ker
  have ho := (legalSpace F x).finrank_add_finrank_orthogonal
  have hd := (LinearMap.range (constraintMap F x)).finrank_le
  have hc : Module.finrank ℝ (({i // i∈F} → ℝ) × ℝ)=F.card+1 := by simp
  rw [hc] at hd
  change Module.finrank ℝ (LinearMap.range (constraintMap F x)) + Module.finrank ℝ (legalSpace F x) = _ at hr
  omega

lemma flat_epoch_trace_lower (C : Matrix (Fin N) (Fin N) ℝ) (hC : C.IsHermitian) (hC1 : C≤1)
    (F : Finset (Fin N)) (x : EuclideanSpace ℝ (Fin N)) :
    ((N:ℝ)-2*MatrixSpencer.realTrace (1-C)-(F.card:ℝ)-1)/2 ≤
      MatrixSpencer.realTrace (flatCovariance C (legalSpace F x)) := by
  have hh := flatCovariance_trace_lower hC hC1 (legalSpace F x)
  have hc : (Module.finrank ℝ (legalSpace F x)ᗮ : ℝ) ≤ (F.card:ℝ)+1 := by exact_mod_cast legalSpace_codim F x
  simp only [Fintype.card_fin] at hh
  linarith

lemma flat_epoch_trace_positive (C : Matrix (Fin N) (Fin N) ℝ) (hC : C.IsHermitian) (hC1 : C≤1)
    (F : Finset (Fin N)) (x : EuclideanSpace ℝ (Fin N)) (hN : 32≤N)
    (hloss : MatrixSpencer.realTrace (1-C)≤(N:ℝ)/64+(N:ℝ)/1539)
    (hf : (F.card:ℝ)≤(N:ℝ)/64) :
    (N:ℝ)/16 ≤ MatrixSpencer.realTrace (flatCovariance C (legalSpace F x)) ∧
    0 < MatrixSpencer.realTrace (flatCovariance C (legalSpace F x)) := by
  have hh := flat_epoch_trace_lower C hC hC1 F x
  have hn : (32:ℝ)≤N := by exact_mod_cast hN
  constructor <;> linarith

end SimpleMS
