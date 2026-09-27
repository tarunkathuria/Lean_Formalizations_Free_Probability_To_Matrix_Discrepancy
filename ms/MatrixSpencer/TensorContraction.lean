import MatrixSpencer.Realignment

/-!
# The two explicit tensor flattenings

This module bounds a concrete contraction of three indexed arrays by composing
two Euclidean energy bounds. The complex factors are not conjugated: this is
the transpose flattening used by the high-spectrum Kraus estimate.
-/

open scoped BigOperators ComplexConjugate ComplexOrder MatrixOrder Matrix

noncomputable section

namespace MatrixSpencer

variable {a b i l j : Type*}

/-- Squared Euclidean norm of a finite complex vector. -/
def vectorEnergy {s : Type*} [Fintype s] (v : s → ℂ) : ℝ :=
  ∑ x, Complex.normSq (v x)

theorem vectorEnergy_nonneg {s : Type*} [Fintype s] (v : s → ℂ) :
    0 ≤ vectorEnergy v :=
  Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _

/-- An explicit squared Euclidean operator bound. -/
def EnergyBound {s t : Type*} [Fintype s] [Fintype t]
    (A : Matrix s t ℂ) (κ : ℝ) : Prop :=
  ∀ v : t → ℂ, vectorEnergy (A *ᵥ v) ≤ κ * vectorEnergy v

theorem vectorEnergy_eq_pairing {s : Type*} [Fintype s] (v : s → ℂ) :
    vectorEnergy v = RCLike.re (star v ⬝ᵥ v) := by
  simp only [vectorEnergy, dotProduct, map_sum, Pi.star_apply]
  apply Finset.sum_congr rfl
  intro x _
  change Complex.normSq (v x) = (conj (v x) * v x).re
  rw [← Complex.normSq_eq_conj_mul_self, Complex.ofReal_re]

/-- A matrix Gram cap implies the energy bound used for each flattening. -/
theorem energyBound_of_gram_le {s t : Type*} [Fintype s] [Fintype t]
    [DecidableEq t] (A : Matrix s t ℂ) {κ : ℝ}
    (hcap : Aᴴ * A ≤ κ • (1 : Matrix t t ℂ)) : EnergyBound A κ := by
  intro v
  have h := (Matrix.le_iff.mp hcap).re_dotProduct_nonneg v
  have hp : vectorEnergy (A *ᵥ v) =
      RCLike.re (star v ⬝ᵥ ((Aᴴ * A) *ᵥ v)) := by
    rw [vectorEnergy_eq_pairing, Matrix.star_mulVec, Matrix.dotProduct_mulVec,
      Matrix.vecMul_vecMul, ← Matrix.dotProduct_mulVec]
  rw [hp, vectorEnergy_eq_pairing]
  simpa only [Matrix.sub_mulVec, dotProduct_sub, Matrix.smul_mulVec,
    Matrix.one_mulVec, dotProduct_smul, map_sub, RCLike.smul_re,
    sub_nonneg] using h

variable [Fintype a] [Fintype b] [Fintype i] [Fintype l] [Fintype j]

/-- The first flattening is applied to the coefficient index for each fixed `j`. -/
def firstFlatten (F : Matrix (i × l) b ℂ) (w : Matrix b j ℂ) : i → l × j → ℂ :=
  fun u vz => ∑ c, F (u, vz.1) c * w c vz.2

/-- The second flattening contracts `(l,j)`, leaving the physical output `i`. -/
def doubleFlatten (F : Matrix (i × l) b ℂ) (G : Matrix a (l × j) ℂ)
    (w : Matrix b j ℂ) : Matrix i a ℂ :=
  fun u c => ∑ vz, G c vz * firstFlatten F w u vz

omit [Fintype a] [Fintype i] in
/-- Fully expanded index formula, fixing the complex transpose convention. -/
theorem doubleFlatten_apply (F : Matrix (i × l) b ℂ) (G : Matrix a (l × j) ℂ)
    (w : Matrix b j ℂ) (u : i) (c : a) :
    doubleFlatten F G w u c =
      ∑ v, ∑ z, ∑ r, F (u, v) r * G c (v, z) * w r z := by
  simp only [doubleFlatten, firstFlatten, Fintype.sum_prod_type, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro v _
  apply Finset.sum_congr rfl
  intro z _
  apply Finset.sum_congr rfl
  intro r _
  ring

/-- Tensoring either flattening with an identity does not increase its energy bound. -/
theorem doubleFlatten_energy_le
    (F : Matrix (i × l) b ℂ) (G : Matrix a (l × j) ℂ) (w : Matrix b j ℂ)
    {α β : ℝ} (hβ : 0 ≤ β) (hF : EnergyBound F α) (hG : EnergyBound G β) :
    entryEnergy (doubleFlatten F G w) ≤ (β * α) * entryEnergy w := by
  have hGsum : entryEnergy (doubleFlatten F G w) ≤
      β * ∑ u, vectorEnergy (firstFlatten F w u) := by
    calc
      _ = ∑ u, vectorEnergy (G *ᵥ firstFlatten F w u) := by
        rfl
      _ ≤ ∑ u, β * vectorEnergy (firstFlatten F w u) := by
        exact Finset.sum_le_sum fun u _ => hG _
      _ = _ := (Finset.mul_sum ..).symm
  have hFsum : (∑ u, vectorEnergy (firstFlatten F w u)) ≤ α * entryEnergy w := by
    calc
      _ = ∑ z, vectorEnergy (F *ᵥ (fun c => w c z)) := by
        simp only [vectorEnergy, firstFlatten, Matrix.mulVec, dotProduct,
          Fintype.sum_prod_type]
        calc
          _ = ∑ u, ∑ z, ∑ v, Complex.normSq (∑ c, F (u, v) c * w c z) := by
            apply Finset.sum_congr rfl
            intro u _
            exact Finset.sum_comm
          _ = _ := Finset.sum_comm
      _ ≤ ∑ z, α * vectorEnergy (fun c => w c z) := by
        exact Finset.sum_le_sum fun z _ => hF _
      _ = α * entryEnergy w := by
        rw [← Finset.mul_sum]
        congr 1
        exact Finset.sum_comm
  calc
    _ ≤ β * ∑ u, vectorEnergy (firstFlatten F w u) := hGsum
    _ ≤ β * (α * entryEnergy w) := mul_le_mul_of_nonneg_left hFsum hβ
    _ = _ := (mul_assoc _ _ _).symm

omit [Fintype a] [Fintype i] in
/-- The two flattenings produce the ordinary mixed matrix product, with no conjugation. -/
theorem doubleFlatten_eq_mixedProduct
    (M : b → Matrix i l ℂ) (D : a → Matrix l j ℂ) (w : Matrix b j ℂ) :
    doubleFlatten (fun uv r => M r uv.1 uv.2) (fun c vz => D c vz.1 vz.2) w =
      (fun u c => ∑ r, ((M r * D c) *ᵥ w r) u) := by
  funext u c
  rw [doubleFlatten_apply]
  simp only [Matrix.mulVec, dotProduct, Matrix.mul_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  calc
    _ = ∑ z, ∑ r, ∑ v, M r u v * D c v z * w r z := by
      apply Finset.sum_congr rfl
      intro z _
      exact Finset.sum_comm
    _ = _ := Finset.sum_comm

/-- Concrete tensor contraction from two actual complex Gram caps. -/
theorem mixedProduct_energy_le_of_gram_caps
    [DecidableEq b] [DecidableEq l] [DecidableEq j]
    (M : b → Matrix i l ℂ) (D : a → Matrix l j ℂ) (w : Matrix b j ℂ)
    {α β : ℝ} (hβ : 0 ≤ β)
    (hF : let F : Matrix (i × l) b ℂ := fun uv r => M r uv.1 uv.2
      Fᴴ * F ≤ α • (1 : Matrix b b ℂ))
    (hG : let G : Matrix a (l × j) ℂ := fun c vz => D c vz.1 vz.2
      Gᴴ * G ≤ β • (1 : Matrix (l × j) (l × j) ℂ)) :
    entryEnergy (fun u c => ∑ r, ((M r * D c) *ᵥ w r) u) ≤
      (β * α) * entryEnergy w := by
  rw [← doubleFlatten_eq_mixedProduct]
  exact doubleFlatten_energy_le _ _ _ hβ
    (energyBound_of_gram_le _ hF) (energyBound_of_gram_le _ hG)

end MatrixSpencer
