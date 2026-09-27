import Mathlib

/-! The exact scalar recipe, with uniform polynomial envelopes for values
and reciprocals. Exponents in an envelope are fixed natural numbers; the
data only enter through N, D, and the dyadic rank parameter q. -/
noncomputable section
namespace AugmentedHigherRankKS.RuntimeParameters
set_option maxHeartbeats 800000

section Envelopes
variable {X : Type*} (T : X → ℝ) (domain : Set X)

def Controlled (f : X → ℝ) : Prop :=
  ∃ C : ℝ, ∃ k : ℕ, 1 ≤ C ∧ ∀ x ∈ domain,
    0 < f x ∧ f x ≤ C * T x ^ k ∧ (f x)⁻¹ ≤ C * T x ^ k

variable {T domain} (hT : ∀ x ∈ domain, 1 ≤ T x)

theorem controlled_const {c : ℝ} (hc : 0 < c) :
    Controlled T domain (fun _ => c) := by
  have hi : 0 < c⁻¹ := inv_pos.mpr hc
  refine ⟨1+c+c⁻¹,0,by linarith,fun x hx => ?_⟩
  simp only [pow_zero, mul_one]
  exact ⟨hc, by linarith, by linarith⟩

include hT in
theorem controlled_base : Controlled T domain T := by
  refine ⟨1,1,le_rfl,fun x hx => ?_⟩
  have ht := hT x hx
  have hpos : 0 < T x := by linarith
  simp only [pow_one, one_mul]
  refine ⟨hpos,le_rfl,?_⟩
  calc _ ≤ 1 := (inv_le_one₀ hpos).2 ht
       _ ≤ _ := ht

include hT in
theorem controlled_between {f : X → ℝ}
    (hf : ∀ x ∈ domain, 1 ≤ f x ∧ f x ≤ T x) : Controlled T domain f := by
  refine ⟨1,1,le_rfl,fun x hx => ?_⟩
  obtain ⟨hl,hu⟩ := hf x hx
  have hp : 0 < f x := by linarith
  simp only [pow_one, one_mul]
  exact ⟨hp,hu,((inv_le_one₀ hp).2 hl).trans (hT x hx)⟩

theorem Controlled.inv {f : X → ℝ} (hf : Controlled T domain f) :
    Controlled T domain (fun x => (f x)⁻¹) := by
  obtain ⟨C,k,hC,hf⟩ := hf
  exact ⟨C,k,hC,fun x hx => by
    obtain ⟨hp,hu,hi⟩ := hf x hx
    simpa only [inv_inv] using And.intro (inv_pos.mpr hp) (And.intro hi hu)⟩

theorem Controlled.mul {f g : X → ℝ}
    (hf : Controlled T domain f) (hg : Controlled T domain g) :
    Controlled T domain (fun x => f x*g x) := by
  obtain ⟨C,k,hC,hf⟩ := hf
  obtain ⟨B,l,hB,hg⟩ := hg
  refine ⟨C*B,k+l,by nlinarith,fun x hx => ?_⟩
  obtain ⟨hfp,hfu,hfi⟩ := hf x hx
  obtain ⟨hgp,hgu,hgi⟩ := hg x hx
  have hCp : 0 ≤ C * T x^k := hfp.le.trans hfu
  have hBp : 0 ≤ B * T x^l := hgp.le.trans hgu
  refine ⟨mul_pos hfp hgp,?_,?_⟩
  · calc _ ≤ (C*T x^k)*(B*T x^l) := mul_le_mul hfu hgu hgp.le hCp
         _ = _ := by rw [pow_add]; ring
  · rw [mul_inv_rev]
    calc _ ≤ (B*T x^l)*(C*T x^k) :=
           mul_le_mul hgi hfi (inv_nonneg.mpr hfp.le) hBp
         _ = _ := by rw [pow_add]; ring

include hT in
theorem Controlled.add {f g : X → ℝ}
    (hf : Controlled T domain f) (hg : Controlled T domain g) :
    Controlled T domain (fun x => f x+g x) := by
  obtain ⟨C,k,hC,hf⟩ := hf
  obtain ⟨B,l,hB,hg⟩ := hg
  refine ⟨C+B,k+l,by linarith,fun x hx => ?_⟩
  obtain ⟨hfp,hfu,hfi⟩ := hf x hx
  obtain ⟨hgp,hgu,hgi⟩ := hg x hx
  have ht := hT x hx
  have hk : T x^k ≤ T x^(k+l) := pow_le_pow_right₀ ht (Nat.le_add_right k l)
  have hl : T x^l ≤ T x^(k+l) := pow_le_pow_right₀ ht (Nat.le_add_left l k)
  have hCp : 0 ≤ C := by linarith
  have hBp : 0 ≤ B := by linarith
  refine ⟨add_pos hfp hgp,?_,?_⟩
  · calc _ ≤ C*T x^k+B*T x^l := add_le_add hfu hgu
         _ ≤ C*T x^(k+l)+B*T x^(k+l) := by gcongr
         _ = _ := by ring
  · calc _ ≤ (f x)⁻¹ := inv_anti₀ hfp (by linarith)
         _ ≤ C*T x^k := hfi
         _ ≤ (C+B)*T x^(k+l) := by
           calc _ ≤ C*T x^(k+l) := mul_le_mul_of_nonneg_left hk hCp
                _ ≤ _ := by gcongr; linarith

theorem Controlled.div {f g : X → ℝ}
    (hf : Controlled T domain f) (hg : Controlled T domain g) :
    Controlled T domain (fun x => f x/g x) := by
  simpa only [div_eq_mul_inv] using hf.mul hg.inv

theorem Controlled.pow {f : X → ℝ} (hf : Controlled T domain f) (k : ℕ) :
    Controlled T domain (fun x => f x^k) := by
  induction k with
  | zero => simpa using (controlled_const (T := T) (domain := domain) (c := 1) one_pos)
  | succ k ih => simpa only [pow_succ] using ih.mul hf

include hT in
theorem Controlled.sqrt {f : X → ℝ} (hf : Controlled T domain f) :
    Controlled T domain (fun x => Real.sqrt (f x)) := by
  obtain ⟨C,k,hC,hf⟩ := hf
  refine ⟨C+1,k,by linarith,fun x hx => ?_⟩
  obtain ⟨hp,hu,hi⟩ := hf x hx
  have htp : 1 ≤ T x^k := one_le_pow₀ (hT x hx)
  have hs (z : ℝ) (hz : 0 ≤ z) : Real.sqrt z ≤ z+1 := by
    nlinarith [Real.sq_sqrt hz, Real.sqrt_nonneg z]
  refine ⟨Real.sqrt_pos.mpr hp,?_,?_⟩
  · calc _ ≤ f x+1 := hs _ hp.le
         _ ≤ C*T x^k+T x^k := add_le_add hu htp
         _ = _ := by ring
  · rw [← Real.sqrt_inv]
    calc _ ≤ (f x)⁻¹+1 := hs _ (inv_nonneg.mpr hp.le)
         _ ≤ C*T x^k+T x^k := add_le_add hi htp
         _ = _ := by ring

include hT in
theorem Controlled.min {f g : X → ℝ}
    (hf : Controlled T domain f) (hg : Controlled T domain g) :
    Controlled T domain (fun x => min (f x) (g x)) := by
  obtain ⟨C,k,hC,hs⟩ := Controlled.add hT hf hg
  obtain ⟨B,l,hB,hf⟩ := hf
  obtain ⟨D,j,hD,hg⟩ := hg
  have hi := (Controlled.add hT (Controlled.inv ⟨B,l,hB,hf⟩)
    (Controlled.inv ⟨D,j,hD,hg⟩))
  obtain ⟨K,q,hK,hi⟩ := hi
  refine ⟨C+K,k+q,by linarith,fun x hx => ?_⟩
  obtain ⟨hfp,hfu,hfi⟩ := hf x hx
  obtain ⟨hgp,hgu,hgi⟩ := hg x hx
  have ht := hT x hx
  have hk : T x^k ≤ T x^(k+q) := pow_le_pow_right₀ ht (Nat.le_add_right k q)
  have hq : T x^q ≤ T x^(k+q) := pow_le_pow_right₀ ht (Nat.le_add_left q k)
  refine ⟨lt_min hfp hgp,?_,?_⟩
  · calc _ ≤ f x+g x := (min_le_left _ _).trans (by linarith)
         _ ≤ C*T x^k := (hs x hx).2.1
         _ ≤ (C+K)*T x^(k+q) := by gcongr <;> linarith
  · have hm : (Min.min (f x) (g x))⁻¹ ≤ (f x)⁻¹+(g x)⁻¹ := by
      rcases le_total (f x) (g x) with h|h
      · rw [min_eq_left h]; have := inv_pos.mpr hgp; linarith
      · rw [min_eq_right h]; have := inv_pos.mpr hfp; linarith
    calc _ ≤ (f x)⁻¹+(g x)⁻¹ := hm
         _ ≤ K*T x^q := (hi x hx).2.1
         _ ≤ (C+K)*T x^(k+q) := by gcongr <;> linarith

end Envelopes

structure Dimensions where
  N : ℝ
  D : ℝ
  q : ℝ

def Domain : Set Dimensions := {z | 1 ≤ z.N ∧ 1 ≤ z.D ∧ 1 ≤ z.q}
def size (z : Dimensions) := 1+z.N+z.D+z.q
def a (z : Dimensions) := 1024*z.q
def theta (z : Dimensions) := (size z ^ 10)⁻¹
abbrev eta := theta
abbrev rho := theta
abbrev zeta := theta
def Bbar (z : Dimensions) := 64*a z*size z
def s0 (z : Dimensions) := (theta z/Bbar z)^2
def p0 (z : Dimensions) := s0 z*eta z
def tau0 (z : Dimensions) := 4*s0 z*eta z^2/Bbar z
def gamma (z : Dimensions) := a z*tau0 z/4
def m (z : Dimensions) := 4*z.D
def C0 (z : Dimensions) := 8*Real.sqrt (a z)
def L0 (z : Dimensions) := 4*a z/zeta z+2/s0 z+1
def H0 (z : Dimensions) := 100*Real.sqrt (m z)*L0 z
def A0 (z : Dimensions) := 1+20*Real.sqrt (m z)+2*C0 z+theta z*Real.sqrt (m z)
def B2 (z : Dimensions) := 4*A0 z*H0 z^2
def B3 (z : Dimensions) := 27*A0 z*H0 z^3
def M (z : Dimensions) := B3 z*(1+B2 z/(theta z/2))^3
def radius (z : Dimensions) := min (rho z/4) (Real.sqrt (zeta z/(4*a z)))
def prep (z : Dimensions) := min (zeta z) (p0 z/(8*a z*M z))
def stencil (z : Dimensions) := min (radius z/4) (gamma z/(64*z.N*M z))
def walk (z : Dimensions) := min (radius z/4) (gamma z/(16*M z))
def accuracy (z : Dimensions) := min 1 (min (prep z*p0 z/(64*a z))
  (min (gamma z*stencil z^2/(256*z.N)) (gamma z*walk z^2/64)))


theorem size_one (z : Dimensions) (hz : z ∈ Domain) : 1 ≤ size z := by
  rcases hz with ⟨hN,hD,hq⟩
  dsimp [size]
  linarith

abbrev Poly (f : Dimensions → ℝ) := Controlled size Domain f

private theorem pc (c : ℝ) (hc : 0 < c) : Poly (fun _ => c) := controlled_const hc
private theorem pa {f g : Dimensions → ℝ} (hf : Poly f) (hg : Poly g) :
    Poly (fun z => f z+g z) := Controlled.add size_one hf hg
private theorem pm {f g : Dimensions → ℝ} (hf : Poly f) (hg : Poly g) :
    Poly (fun z => f z*g z) := hf.mul hg
private theorem pd {f g : Dimensions → ℝ} (hf : Poly f) (hg : Poly g) :
    Poly (fun z => f z/g z) := hf.div hg
private theorem ps {f : Dimensions → ℝ} (hf : Poly f) :
    Poly (fun z => Real.sqrt (f z)) := Controlled.sqrt size_one hf
private theorem pn {f g : Dimensions → ℝ} (hf : Poly f) (hg : Poly g) :
    Poly (fun z => min (f z) (g z)) := Controlled.min size_one hf hg

theorem size_poly : Poly size := controlled_base size_one

theorem N_poly : Poly Dimensions.N := by
  apply controlled_between size_one
  intro z hz
  rcases hz with ⟨hN,hD,hq⟩
  exact ⟨hN,by dsimp [size]; linarith⟩

theorem D_poly : Poly Dimensions.D := by
  apply controlled_between size_one
  intro z hz
  rcases hz with ⟨hN,hD,hq⟩
  exact ⟨hD,by dsimp [size]; linarith⟩

theorem q_poly : Poly Dimensions.q := by
  apply controlled_between size_one
  intro z hz
  rcases hz with ⟨hN,hD,hq⟩
  exact ⟨hq,by dsimp [size]; linarith⟩

theorem a_poly : Poly a := pm (pc 1024 (by norm_num)) q_poly

theorem theta_poly : Poly theta := (size_poly.pow 10).inv

theorem Bbar_poly : Poly Bbar := pm (pm (pc 64 (by norm_num)) a_poly) size_poly

theorem s0_poly : Poly s0 := (pd theta_poly Bbar_poly).pow 2

theorem p0_poly : Poly p0 := pm s0_poly theta_poly

theorem tau0_poly : Poly tau0 := pd (pm (pm (pc 4 (by norm_num)) s0_poly) (theta_poly.pow 2)) Bbar_poly

theorem gamma_poly : Poly gamma := pd (pm a_poly tau0_poly) (pc 4 (by norm_num))

theorem m_poly : Poly m := pm (pc 4 (by norm_num)) D_poly

theorem C0_poly : Poly C0 := pm (pc 8 (by norm_num)) (ps a_poly)

theorem L0_poly : Poly L0 := pa (pa (pd (pm (pc 4 (by norm_num)) a_poly) theta_poly) (pd (pc 2 (by norm_num)) s0_poly)) (pc 1 (by norm_num))

theorem H0_poly : Poly H0 := pm (pm (pc 100 (by norm_num)) (ps m_poly)) L0_poly

theorem A0_poly : Poly A0 := pa (pa (pa (pc 1 (by norm_num)) (pm (pc 20 (by norm_num)) (ps m_poly))) (pm (pc 2 (by norm_num)) C0_poly)) (pm theta_poly (ps m_poly))

theorem B2_poly : Poly B2 := pm (pm (pc 4 (by norm_num)) A0_poly) (H0_poly.pow 2)

theorem B3_poly : Poly B3 := pm (pm (pc 27 (by norm_num)) A0_poly) (H0_poly.pow 3)

theorem M_poly : Poly M := pm B3_poly ((pa (pc 1 (by norm_num)) (pd B2_poly (pd theta_poly (pc 2 (by norm_num))))).pow 3)

theorem radius_poly : Poly radius := pn (pd theta_poly (pc 4 (by norm_num))) (ps (pd theta_poly (pm (pc 4 (by norm_num)) a_poly)))

theorem prep_poly : Poly prep := pn theta_poly (pd p0_poly (pm (pm (pc 8 (by norm_num)) a_poly) M_poly))

theorem stencil_poly : Poly stencil := pn (pd radius_poly (pc 4 (by norm_num))) (pd gamma_poly (pm (pm (pc 64 (by norm_num)) N_poly) M_poly))

theorem walk_poly : Poly walk := pn (pd radius_poly (pc 4 (by norm_num))) (pd gamma_poly (pm (pc 16 (by norm_num)) M_poly))

theorem accuracy_poly : Poly accuracy := pn (pc 1 (by norm_num)) (pn (pd (pm prep_poly p0_poly) (pm (pc 64 (by norm_num)) a_poly)) (pn (pd (pm gamma_poly (stencil_poly.pow 2)) (pm (pc 256 (by norm_num)) N_poly)) (pd (pm gamma_poly (walk_poly.pow 2)) (pc 64 (by norm_num)))))


/-- A conservative bound for all successful updates and cleanup events in
one epoch, including one final scan. -/
def eventBound (z : Dimensions) := z.N/walk z^2+z.N*a z*4/prep z+2*z.N+1

theorem eventBound_poly : Poly eventBound :=
  pa (pa (pa (pd N_poly (walk_poly.pow 2))
    (pd (pm (pm N_poly a_poly) (pc 4 (by norm_num))) prep_poly))
    (pm (pc 2 (by norm_num)) N_poly)) (pc 1 (by norm_num))

/-- At most N epochs, each with a quadratic number of queries per event. -/
def queryBound (z : Dimensions) := z.N*(8*(z.N+1)^2)*(eventBound z+1)

theorem queryBound_poly : Poly queryBound :=
  pm (pm N_poly (pm (pc 8 (by norm_num)) ((pa N_poly (pc 1 (by norm_num))).pow 2)))
    (pa eventBound_poly (pc 1 (by norm_num)))

theorem Controlled.positive {X : Type*} {T : X → ℝ} {domain : Set X} {f : X → ℝ}
    (hf : Controlled T domain f) (x : X) (hx : x ∈ domain) : 0 < f x := by
  obtain ⟨C,k,hC,hf⟩ := hf
  exact (hf x hx).1

theorem all_positive (z : Dimensions) (hz : z ∈ Domain) :
    0 < a z ∧ 0 < theta z ∧ 0 < Bbar z ∧ 0 < s0 z ∧ 0 < p0 z ∧
    0 < tau0 z ∧ 0 < gamma z ∧ 0 < M z ∧ 0 < radius z ∧ 0 < prep z ∧
    0 < stencil z ∧ 0 < walk z ∧ 0 < accuracy z :=
  ⟨a_poly.positive z hz, theta_poly.positive z hz, Bbar_poly.positive z hz,
   s0_poly.positive z hz,p0_poly.positive z hz,tau0_poly.positive z hz,
   gamma_poly.positive z hz,M_poly.positive z hz,radius_poly.positive z hz,
   prep_poly.positive z hz,stencil_poly.positive z hz,walk_poly.positive z hz,
   accuracy_poly.positive z hz⟩

theorem prep_le_zeta (z : Dimensions) : prep z ≤ zeta z := min_le_left _ _
theorem prep_le (z : Dimensions) : prep z ≤ p0 z/(8*a z*M z) := min_le_right _ _
theorem radius_le_rho (z : Dimensions) : radius z ≤ rho z/4 := min_le_left _ _
theorem radius_le_sqrt (z : Dimensions) : radius z ≤ Real.sqrt (zeta z/(4*a z)) := min_le_right _ _
theorem stencil_le_radius (z : Dimensions) : stencil z ≤ radius z/4 := min_le_left _ _
theorem stencil_le (z : Dimensions) : stencil z ≤ gamma z/(64*z.N*M z) := min_le_right _ _
theorem walk_le_radius (z : Dimensions) : walk z ≤ radius z/4 := min_le_left _ _
theorem walk_le (z : Dimensions) : walk z ≤ gamma z/(16*M z) := min_le_right _ _
theorem accuracy_le_one (z : Dimensions) : accuracy z ≤ 1 := min_le_left _ _
theorem accuracy_le_prep (z : Dimensions) : accuracy z ≤ prep z*p0 z/(64*a z) :=
  (min_le_right _ _).trans (min_le_left _ _)
theorem accuracy_le_stencil (z : Dimensions) : accuracy z ≤ gamma z*stencil z^2/(256*z.N) :=
  (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
theorem accuracy_le_walk (z : Dimensions) : accuracy z ≤ gamma z*walk z^2/64 :=
  (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))


theorem theta_le_one (z : Dimensions) (hz : z ∈ Domain) : theta z ≤ 1 := by
  have ht : 0 < size z := by linarith [size_one z hz]
  apply (inv_le_one₀ (by positivity : 0 < size z^10)).2
  exact one_le_pow₀ (size_one z hz)

theorem a_ge (z : Dimensions) (hz : z ∈ Domain) : 1024 ≤ a z := by
  have hq := hz.2.2
  dsimp [a]
  linarith

theorem cap_slack (z : Dimensions) (hz : z ∈ Domain) : 9/a z < 1/48 := by
  apply (div_lt_iff₀ (a_poly.positive z hz)).2
  have ha := a_ge z hz
  linarith

theorem prep_product (z : Dimensions) (hz : z ∈ Domain) :
    M z*prep z ≤ p0 z/(8*a z) := by
  have ha := a_poly.positive z hz
  have hM := M_poly.positive z hz
  have hh := (le_div_iff₀ (show 0 < 8*a z*M z by positivity)).mp (prep_le z)
  apply (le_div_iff₀ (by positivity : 0 < 8*a z)).2
  nlinarith

theorem walk_product (z : Dimensions) (hz : z ∈ Domain) :
    M z*walk z ≤ gamma z/16 := by
  have hM := M_poly.positive z hz
  have hh := (le_div_iff₀ (show 0 < 16*M z by positivity)).mp (walk_le z)
  linarith

theorem radius_quadratic (z : Dimensions) (hz : z ∈ Domain) :
    a z*radius z^2 ≤ zeta z/4 := by
  have ha := a_poly.positive z hz
  have hzeta := theta_poly.positive z hz
  have hr := radius_poly.positive z hz
  have hdiv : 0 ≤ zeta z/(4*a z) := by positivity
  have hsq : radius z^2 ≤ zeta z/(4*a z) := by
    calc _ ≤ (Real.sqrt (zeta z/(4*a z)))^2 := by
           gcongr; exact radius_le_sqrt z
         _ = _ := Real.sq_sqrt hdiv
  have hh := (le_div_iff₀ (show 0 < 4*a z by positivity)).mp hsq
  nlinarith

theorem stencil_query_radius (z : Dimensions) (hz : z ∈ Domain) :
    2*stencil z ≤ radius z ∧ 2*stencil z ≤ rho z/2 ∧
    a z*(2*stencil z)^2 ≤ zeta z/4 := by
  have ht := stencil_poly.positive z hz
  have hr := radius_poly.positive z hz
  have ha := a_poly.positive z hz
  have hh := stencil_le_radius z
  have hrad := radius_le_rho z
  have hsmall : 2*stencil z ≤ radius z := by linarith
  refine ⟨hsmall,by linarith,?_⟩
  calc _ ≤ a z*radius z^2 := by gcongr
       _ ≤ _ := radius_quadratic z hz

theorem walk_query_radius (z : Dimensions) (hz : z ∈ Domain) :
    walk z ≤ radius z ∧ walk z ≤ rho z/2 ∧
    a z*walk z^2 ≤ zeta z/4 := by
  have hh := walk_le_radius z
  have hr := radius_poly.positive z hz
  have hw := walk_poly.positive z hz
  have ha := a_poly.positive z hz
  have hrad := radius_le_rho z
  have hsmall : walk z ≤ radius z := by linarith
  refine ⟨hsmall,by linarith,?_⟩
  calc _ ≤ a z*radius z^2 := by gcongr
       _ ≤ _ := radius_quadratic z hz

/-- Eliminate q from the complexity variable once its elementary rank
bound has been established. The exponent and constant are uniform over
all dimensions, ranks, and matrix entries. -/
theorem Poly.input_polynomial {f : Dimensions → ℝ} (hf : Poly f) :
    ∃ C : ℝ, ∃ k : ℕ, 0 < C ∧ ∀ z ∈ Domain, z.q ≤ 4*z.D →
      f z ≤ C*(1+z.N+z.D)^k ∧ (f z)⁻¹ ≤ C*(1+z.N+z.D)^k := by
  obtain ⟨C,k,hC,hf⟩ := hf
  refine ⟨C*5^k,k,by positivity,fun z hz hq => ?_⟩
  have hsize : size z ≤ 5*(1+z.N+z.D) := by
    rcases hz with ⟨hN,hD,hq'⟩
    dsimp [size]
    linarith
  have hsizepos : 0 ≤ size z := (by linarith [size_one z hz])
  have hCp : 0 ≤ C := by linarith
  have he : C*size z^k ≤ C*5^k*(1+z.N+z.D)^k := by
    calc _ ≤ C*(5*(1+z.N+z.D))^k := by gcongr
         _ = _ := by rw [mul_pow]; ring
  exact ⟨(hf z hz).2.1.trans he,(hf z hz).2.2.trans he⟩

end AugmentedHigherRankKS.RuntimeParameters
