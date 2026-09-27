import SimpleMS.Movement

/-! The isolated revised MS walk: scaled projection covariance and uniform
signed orthonormal-basis increments. This compatibility namespace lets the
existing epoch accounting be reproved for the changed concrete algorithm. -/
open Matrix
open scoped BigOperators MatrixOrder
noncomputable section
namespace MatrixSpencer.MSManuscriptNumericalMovement
variable {d : ℕ}
abbrev covariance := @SimpleMS.Movement.covariance d
abbrev Draws := @SimpleMS.Movement.Draws d
abbrev weight := @SimpleMS.Movement.weight d
abbrev increment := @SimpleMS.Movement.increment d
abbrev nextPoint := @SimpleMS.Movement.nextPoint d
abbrev nextOwner := @SimpleMS.Movement.nextOwner d

def sample (C : Matrix (Fin d) (Fin d) ℝ) (_hC : C.PosSemidef) (F : Finset (Fin d))
    (x : EuclideanSpace ℝ (Fin d)) (hq : 0<realTrace (covariance C F x)) :
    MSManuscriptAdaptive.Sampler (EuclideanSpace ℝ (Fin d)) :=
  SimpleMS.Movement.sample C F x hq

theorem weight_positive (C : Matrix (Fin d) (Fin d) ℝ) (F : Finset (Fin d))
    (x : EuclideanSpace ℝ (Fin d)) (hq : 0<realTrace (covariance C F x)) (s : Draws C F x) :
    0<weight C F x s :=
  SimpleMS.Movement.weight_positive C F x hq s

theorem weights_sum (C : Matrix (Fin d) (Fin d) ℝ) (hC : C.PosSemidef) (F : Finset (Fin d))
    (x : EuclideanSpace ℝ (Fin d)) (hq : 0<realTrace (covariance C F x)) :
    (∑s : Draws C F x,weight C F x s)=1 :=
  SimpleMS.Movement.weights_sum C F x hq

theorem mean_zero (C : Matrix (Fin d) (Fin d) ℝ) (F : Finset (Fin d)) (x : EuclideanSpace ℝ (Fin d)) :
    (∑s : Draws C F x,weight C F x s • increment C F x s)=0 :=
  SimpleMS.Movement.mean_zero C F x

theorem covariance_exact (C : Matrix (Fin d) (Fin d) ℝ) (hC : C.PosSemidef) (F : Finset (Fin d))
    (x : EuclideanSpace ℝ (Fin d)) (hq : 0<realTrace (covariance C F x)) :
    (∑s : Draws C F x,weight C F x s • realRankOne (WithLp.ofLp (increment C F x s)))=covariance C F x :=
  SimpleMS.Movement.covariance_exact C F x hq

theorem increment_constraints (C : Matrix (Fin d) (Fin d) ℝ) (hC : C.PosSemidef) (F : Finset (Fin d))
    (x : EuclideanSpace ℝ (Fin d)) (s : Draws C F x) :
    (∀i∈F,increment C F x s i=0) ∧ inner ℝ x (increment C F x s)=0 :=
  SimpleMS.Movement.increment_constraints C F x s

theorem increment_norm_sq (C : Matrix (Fin d) (Fin d) ℝ) (hC : C.PosSemidef) (F : Finset (Fin d))
    (x : EuclideanSpace ℝ (Fin d)) (s : Draws C F x) :
    ‖increment C F x s‖^2=realTrace (covariance C F x) :=
  SimpleMS.Movement.increment_norm_sq C F x s

theorem norm_gain (C : Matrix (Fin d) (Fin d) ℝ) (hC : C.PosSemidef) (F : Finset (Fin d))
    (x : EuclideanSpace ℝ (Fin d)) (h : ℝ) (s : Draws C F x) :
    ‖nextPoint C F x h s‖^2=‖x‖^2+h^2*realTrace (covariance C F x) :=
  SimpleMS.Movement.norm_gain C F x h s

theorem frozen_preserved (C : Matrix (Fin d) (Fin d) ℝ) (hC : C.PosSemidef) (F : Finset (Fin d))
    (x : EuclideanSpace ℝ (Fin d)) (h : ℝ) (s : Draws C F x) (i : Fin d) (hi : i∈F) :
    nextPoint C F x h s i=x i :=
  SimpleMS.Movement.frozen_preserved C F x h s i hi

theorem nextOwner_valid (C : Matrix (Fin d) (Fin d) ℝ) (hC : C.PosSemidef) (F : Finset (Fin d))
    (x : EuclideanSpace ℝ (Fin d)) {h : ℝ} (hh : h^2<1) :
    (nextOwner C F x h).PosSemidef ∧ nextOwner C F x h≤C ∧
      LinearMap.range (Matrix.toEuclideanCLM (𝕜 := ℝ) (nextOwner C F x h)).toLinearMap=
        LinearMap.range (Matrix.toEuclideanCLM (𝕜 := ℝ) C).toLinearMap :=
  SimpleMS.Movement.nextOwner_valid C hC F x hh

theorem nextOwner_trace (C : Matrix (Fin d) (Fin d) ℝ) (F : Finset (Fin d))
    (x : EuclideanSpace ℝ (Fin d)) (h : ℝ) :
    realTrace (nextOwner C F x h)=realTrace C-h^2*realTrace (covariance C F x) :=
  SimpleMS.Movement.nextOwner_trace C F x h

theorem nextOwner_matched (C : Matrix (Fin d) (Fin d) ℝ) (hC : C.PosSemidef) (F : Finset (Fin d))
    (x : EuclideanSpace ℝ (Fin d)) (hq : 0<realTrace (covariance C F x)) (h : ℝ) :
    nextOwner C F x h=C-h^2 • (∑s : Draws C F x,weight C F x s • realRankOne (WithLp.ofLp (increment C F x s))) :=
  SimpleMS.Movement.nextOwner_matched C F x hq h

theorem nextPoint_mem_cube (C : Matrix (Fin d) (Fin d) ℝ) (hC : C.PosSemidef) (F : Finset (Fin d))
    (x : EuclideanSpace ℝ (Fin d)) (hx : ∀i,|x i|≤1) {ρ h : ℝ}
    (hmargin : ∀i,i∉F→|x i|≤1-ρ) (hstep : |h| *Real.sqrt (realTrace (covariance C F x))≤ρ)
    (s : Draws C F x) : ∀i,|nextPoint C F x h s i|≤1 :=
  SimpleMS.Movement.nextPoint_mem_cube C F x hx hmargin hstep s

theorem trace_positive_of_ledger (C : Matrix (Fin d) (Fin d) ℝ) (hC : C.PosSemidef) (hC1 : C≤1)
    (F : Finset (Fin d)) (x : EuclideanSpace ℝ (Fin d)) (hd : 32≤d)
    (htrace : realTrace (1-C)≤(d:ℝ)/64+(d:ℝ)/1539) (hF : (F.card:ℝ)≤(d:ℝ)/64) :
    (d:ℝ)/16≤realTrace (covariance C F x) ∧ 0<realTrace (covariance C F x) :=
  SimpleMS.flat_epoch_trace_positive C hC.isHermitian hC1 F x hd htrace hF

end MatrixSpencer.MSManuscriptNumericalMovement
