import MatrixSpencer.MSManuscriptAdaptive


open scoped BigOperators
noncomputable section
namespace MatrixSpencer.MSManuscriptEpochProbability
open MSManuscriptAdaptive
variable {α : Type*}
attribute [local instance] Classical.propDecidable


def Good (N energy paid dust tangent : ℝ) : Prop :=
  energy≤16*Real.sqrt N ∧ tangent≤4*Real.sqrt N ∧ paid+dust≤N/64

def score (N energy paid tangent : ℝ) : ℝ :=
  energy/(16*Real.sqrt N)+(2048/Real.sqrt N*paid)/(30*Real.sqrt N)+tangent^2/(16*N)

theorem score_nonneg {N energy paid tangent : ℝ} (hN : 0<N)
    (he : 0≤energy) (hp : 0≤paid) : 0≤score N energy paid tangent := by
  unfold score
  positivity

theorem one_le_score_of_not_good {N energy paid dust tangent : ℝ} (hN : 0<N)
    (he : 0≤energy) (hp : 0≤paid) (hd : dust≤N/1024)
    (hbad : ¬Good N energy paid dust tangent) : 1≤score N energy paid tangent := by
  have hr := Real.sqrt_pos.mpr hN
  have hs := Real.sq_sqrt hN.le
  have h1 : 0≤energy/(16*Real.sqrt N) := by positivity
  have h2 : 0≤(2048/Real.sqrt N*paid)/(30*Real.sqrt N) := by positivity
  have h3 : 0≤tangent^2/(16*N) := by positivity
  unfold Good at hbad
  rcases not_and_or.mp hbad with hbad | hbad
  · have hx : 1≤energy/(16*Real.sqrt N) := (le_div_iff₀ (by positivity)).mpr (by simpa using (le_of_not_ge hbad))
    unfold score
    linarith
  · rcases not_and_or.mp hbad with hbad | hbad
    · have ht : 4*Real.sqrt N<tangent := lt_of_not_ge hbad
      have ht2 : 16*N≤tangent^2 := by nlinarith
      have hx : 1≤tangent^2/(16*N) := (le_div_iff₀ (by positivity)).mpr (by simpa using ht2)
      unfold score
      linarith
    · have hc : N/64<paid+dust := lt_of_not_ge hbad
      have hp' : (15/1024:ℝ)*N≤paid := by linarith
      have hm := mul_le_mul_of_nonneg_left hp' (by positivity : 0≤(2048:ℝ)/Real.sqrt N)
      have heq : 2048/Real.sqrt N*((15/1024:ℝ)*N)=30*Real.sqrt N := by
        field_simp
        nlinarith
      rw [heq] at hm
      have hx : 1≤(2048/Real.sqrt N*paid)/(30*Real.sqrt N) :=
        (le_div_iff₀ (by positivity)).mpr (by simpa using hm)
      unfold score
      linarith

/-- The coupled account gives both nonnegative marginal moments, so no
independence between energy, paid mass, and tangent is used. -/
theorem score_moment_le (P : Sampler α) (energy paid tangent : α→ℝ) {N : ℝ} (hN : 0<N)
    (he : ∀a,0≤energy a) (hp : ∀a,0≤paid a)
    (hjoint : P.expectation (fun a=>energy a+2048/Real.sqrt N*paid a)≤(151/50:ℝ)*Real.sqrt N)
    (ht : P.expectation (fun a=>(tangent a)^2)≤N) :
    P.expectation (fun a=>score N (energy a) (paid a) (tangent a))≤19/50 := by
  have hr := Real.sqrt_pos.mpr hN
  have he' : P.expectation energy≤(151/50:ℝ)*Real.sqrt N :=
    (P.expectation_mono (fun a=>le_add_of_nonneg_right (mul_nonneg (by positivity) (hp a)))).trans hjoint
  have hp' : P.expectation (fun a=>2048/Real.sqrt N*paid a)≤(151/50:ℝ)*Real.sqrt N :=
    (P.expectation_mono (fun a=>le_add_of_nonneg_left (he a))).trans hjoint
  have heq : P.expectation (fun a=>score N (energy a) (paid a) (tangent a))=
      P.expectation energy/(16*Real.sqrt N)+
      P.expectation (fun a=>2048/Real.sqrt N*paid a)/(30*Real.sqrt N)+
      P.expectation (fun a=>(tangent a)^2)/(16*N) := by
    simp only [Sampler.expectation,score,mul_add,mul_div_assoc,Finset.sum_add_distrib,Finset.sum_div]
  rw [heq]
  have h1 := div_le_div_of_nonneg_right he' (by positivity : 0≤16*Real.sqrt N)
  have h2 := div_le_div_of_nonneg_right hp' (by positivity : 0≤30*Real.sqrt N)
  have h3 := div_le_div_of_nonneg_right ht (by positivity : 0≤16*N)
  have ha : ((151/50:ℝ)*Real.sqrt N)/(16*Real.sqrt N)=151/800 := by field_simp <;> ring
  have hb : ((151/50:ℝ)*Real.sqrt N)/(30*Real.sqrt N)=151/1500 := by field_simp <;> ring
  have hc : N/(16*N)=1/16 := by field_simp <;> ring
  rw [ha] at h1
  rw [hb] at h2
  rw [hc] at h3
  linarith

/-- Literal good-event mass for any normalized finite distribution satisfying
the proved numerical run moment accounts. -/
theorem good_probability_ge (P : Sampler α) (energy paid dust tangent : α→ℝ) {N : ℝ} (hN : 0<N)
    (he : ∀a,0≤energy a) (hp : ∀a,0≤paid a) (hd : ∀a,dust a≤N/1024)
    (hjoint : P.expectation (fun a=>energy a+2048/Real.sqrt N*paid a)≤(151/50:ℝ)*Real.sqrt N)
    (ht : P.expectation (fun a=>(tangent a)^2)≤N) :
    (31/50:ℝ)≤∑z:P.Draws,P.weight z*(if Good N (energy (P.value z)) (paid (P.value z))
      (dust (P.value z)) (tangent (P.value z)) then 1 else 0) := by
  classical
  have hs := score_moment_le P energy paid tangent hN he hp hjoint ht
  have hpw (a : α) : 1-(if Good N (energy a) (paid a) (dust a) (tangent a) then 1 else 0)≤
      score N (energy a) (paid a) (tangent a) := by
    split_ifs with hg
    · simpa using score_nonneg hN (he a) (hp a)
    · simpa using one_le_score_of_not_good hN (he a) (hp a) (hd a) hg
  have hm := P.expectation_mono hpw
  rw [P.expectation_sub,P.expectation_const] at hm
  change _≤P.expectation (fun a=>if Good N (energy a) (paid a) (dust a) (tangent a) then 1 else 0)
  linarith


/-- Excessive cleaning is controlled by the paid-energy moment and the
pathwise dust budget. This discharges the cleaning premise of numerical
acceptance without an independent failure-probability assumption. -/
theorem cleaning_probability_le (P : Sampler α) (energy paid dust : α→ℝ) {N : ℝ} (hN : 0<N)
    (he : ∀a,0≤energy a) (hp : ∀a,0≤paid a) (hd : ∀a,dust a≤N/1024)
    (hjoint : P.expectation (fun a=>energy a+2048/Real.sqrt N*paid a)≤(151/50:ℝ)*Real.sqrt N) :
    P.expectation (fun a=>if N/64<paid a+dust a then 1 else 0)≤1/8 := by
  have hr := Real.sqrt_pos.mpr hN
  have hs := Real.sq_sqrt hN.le
  have hm (a : α) : (if N/64<paid a+dust a then (1:ℝ) else 0)≤
      (energy a+2048/Real.sqrt N*paid a)/(30*Real.sqrt N) := by
    split_ifs with hc
    · have hp' : (15/1024:ℝ)*N≤paid a := by linarith [hd a]
      have hb := mul_le_mul_of_nonneg_left hp' (by positivity : 0≤(2048:ℝ)/Real.sqrt N)
      have heq : 2048/Real.sqrt N*((15/1024:ℝ)*N)=30*Real.sqrt N := by
        field_simp
        nlinarith
      rw [heq] at hb
      apply (le_div_iff₀ (by positivity)).mpr
      linarith [he a]
    · exact div_nonneg (add_nonneg (he a) (mul_nonneg (by positivity) (hp a))) (by positivity)
  have h := P.expectation_mono hm
  have heq : P.expectation (fun a=>(energy a+2048/Real.sqrt N*paid a)/(30*Real.sqrt N))=
      P.expectation (fun a=>energy a+2048/Real.sqrt N*paid a)/(30*Real.sqrt N) := by
    simp only [Sampler.expectation,mul_div_assoc,Finset.sum_div]
  rw [heq] at h
  have hb := div_le_div_of_nonneg_right hjoint (by positivity : 0≤30*Real.sqrt N)
  have hc : ((151/50:ℝ)*Real.sqrt N)/(30*Real.sqrt N)=151/1500 := by field_simp; ring
  rw [hc] at hb
  linarith

/-- The separate energy moment required by the two-test acceptance wrapper. -/
theorem energy_moment_le_of_joint (P : Sampler α) (energy paid : α→ℝ) {N : ℝ} (hN : 0<N)
    (hp : ∀a,0≤paid a)
    (hjoint : P.expectation (fun a=>energy a+2048/Real.sqrt N*paid a)≤(151/50:ℝ)*Real.sqrt N) :
    P.expectation energy≤(151/50:ℝ)*Real.sqrt N :=
  (P.expectation_mono (fun a=>le_add_of_nonneg_right (mul_nonneg (by positivity) (hp a)))).trans hjoint

end MatrixSpencer.MSManuscriptEpochProbability
