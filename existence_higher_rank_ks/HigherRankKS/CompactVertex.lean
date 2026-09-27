import MatrixSpencer.KSEndpointCube
import MatrixSpencer.KSLocalDescent
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs

/-!
# The compact cube argument for a vertex minimum

This file supplies only the topological and finite-coordinate part of the
higher-rank existence proof.  In particular, the endpoint-or-descent
hypothesis below is an analytic obligation, not an assumption of a claimed
unconditional signing theorem.

Continuity gives a cube minimum.  The bounded number of endpoint coordinates
has a maximum among all minimizers.  At that maximizer a nonincreasing update
of a live coordinate contradicts maximality; a strictly decreasing feasible
point contradicts minimality.
-/

open Set Filter MatrixSpencer
open scoped Topology

noncomputable section

namespace HigherRankKS.CompactVertex

variable {N : ℕ}

/-- The elementary alternative needed at nonvertex cube points.  The first
branch freezes one live coordinate and leaves every other coordinate fixed.
The second branch supplies an actual strictly better feasible point. -/
def EndpointOrDescent (a : ℝ) (F : (Fin N → ℝ) → ℝ) (x : Fin N → ℝ) : Prop :=
  (∃ i : Fin N, |x i| < a ∧ ∃ s : ℝ,
    (s = -a ∨ s = a) ∧ F (Function.update x i s) ≤ F x) ∨
  (∃ y ∈ ksCube a, F y < F x)

/-- A curve which remains in the cube near its basepoint and fails to
minimize the potential locally supplies a strictly better feasible point. -/
theorem exists_cube_descent_of_not_isLocalMin_curve {a : ℝ}
    (F : (Fin N → ℝ) → ℝ) {x : Fin N → ℝ}
    (γ : ℝ → Fin N → ℝ) (hbase : γ 0 = x)
    (hfeasible : ∀ᶠ t in 𝓝 (0 : ℝ), γ t ∈ ksCube a)
    (hnotmin : ¬ IsLocalMin (fun t => F (γ t)) 0) :
    ∃ y ∈ ksCube a, F y < F x := by
  by_contra hnone
  push_neg at hnone
  apply hnotmin
  filter_upwards [hfeasible] with t ht
  change F (γ 0) ≤ F (γ t)
  rw [hbase]
  exact hnone (γ t) ht

/-- Smoothness is needed only along the feasible curve.  Negative second
derivative there implies actual descent; no gradient hypothesis is needed,
since a hypothetical local minimum already forces the gradient to vanish. -/
theorem exists_cube_descent_of_negative_second {a : ℝ}
    (F : (Fin N → ℝ) → ℝ) {x : Fin N → ℝ}
    (γ : ℝ → Fin N → ℝ) (hbase : γ 0 = x)
    (hfeasible : ∀ᶠ t in 𝓝 (0 : ℝ), γ t ∈ ksCube a)
    (hsmooth : ContDiffAt ℝ 2 (fun t => F (γ t)) 0)
    (hnegative : iteratedDeriv 2 (fun t => F (γ t)) 0 < 0) :
    ∃ y ∈ ksCube a, F y < F x := by
  apply exists_cube_descent_of_not_isLocalMin_curve F γ hbase hfeasible
  apply ks_not_isLocalMin_of_hessian_neg (fun t => F (γ t)) 0 1 hsmooth
  simpa only [iteratedDeriv, iteratedFDeriv_two_apply] using hnegative

/-- A direction which vanishes at all frozen coordinates remains in the
current cube face for all sufficiently small positive and negative times. -/
theorem eventually_mem_cube_along_live_direction {a : ℝ} {x : Fin N → ℝ}
    (hx : x ∈ ksCube a) (v : Fin N → ℝ)
    (hfrozen : ∀ i, |x i| = a → v i = 0) :
    ∀ᶠ t in 𝓝 (0 : ℝ), x + t • v ∈ ksCube a := by
  have hcoord : ∀ i, ∀ᶠ t in 𝓝 (0 : ℝ), |(x + t • v) i| ≤ a := by
    intro i
    by_cases hi : |x i| < a
    · have hc : Continuous (fun t : ℝ => |(x + t • v) i|) := by fun_prop
      have hzero : |(x + (0 : ℝ) • v) i| < a := by simpa using hi
      filter_upwards [hc.continuousAt.eventually (isOpen_Iio.mem_nhds hzero)] with t ht
      exact ht.le
    · have heq : |x i| = a :=
        le_antisymm (abs_le.mpr ⟨hx.1 i, hx.2 i⟩) (not_lt.mp hi)
      filter_upwards [] with t
      change |x i + t * v i| ≤ a
      rw [hfrozen i heq, mul_zero, add_zero, heq]
  have hall : ∀ᶠ t in 𝓝 (0 : ℝ), ∀ i, |(x + t • v) i| ≤ a :=
    Filter.eventually_all.mpr hcoord
  filter_upwards [hall] with t ht
  exact ⟨fun i => (abs_le.mp (ht i)).1, fun i => (abs_le.mp (ht i)).2⟩

/-- Negative curvature in an original-label direction tangent to the live
face yields descent at a feasible point of the same cube. -/
theorem exists_cube_descent_of_live_negative_second {a : ℝ}
    (F : (Fin N → ℝ) → ℝ) {x : Fin N → ℝ} (hx : x ∈ ksCube a)
    (v : Fin N → ℝ) (hfrozen : ∀ i, |x i| = a → v i = 0)
    (hsmooth : ContDiffAt ℝ 2 (fun t : ℝ => F (x + t • v)) 0)
    (hnegative : iteratedDeriv 2 (fun t : ℝ => F (x + t • v)) 0 < 0) :
    ∃ y ∈ ksCube a, F y < F x :=
  exists_cube_descent_of_negative_second F (fun t => x + t • v) (by simp)
    (eventually_mem_cube_along_live_direction hx v hfrozen) hsmooth hnegative

/-- A continuous potential on a nonempty compact cube attains its minimum. -/
theorem exists_cube_minimum {a : ℝ} (ha : 0 ≤ a)
    (F : (Fin N → ℝ) → ℝ) (hcont : ContinuousOn F (ksCube a)) :
    ∃ x ∈ ksCube a, IsMinOn F (ksCube a) x :=
  (ksCube_compact a).exists_isMinOn ⟨0, ksCube_zero ha⟩ hcont

/-- The compactness argument only requires the endpoint-or-descent
alternative at global minimizers.  Choosing a minimizer with the maximum
number of frozen coordinates proves that one of the minimizers is a vertex. -/
theorem exists_vertex_minimum_of_minimizer_alternative {a : ℝ} (ha : 0 ≤ a)
    (F : (Fin N → ℝ) → ℝ) (hcont : ContinuousOn F (ksCube a))
    (halternative : ∀ x ∈ ksCube a, IsMinOn F (ksCube a) x →
      ¬ ksVertex a x → EndpointOrDescent a F x) :
    ∃ x ∈ ksCube a, ksVertex a x ∧ IsMinOn F (ksCube a) x := by
  apply ks_exists_terminal_minimum (ksCube a) F (fun x => (ksFrozen a x).card)
    N (ksVertex a) (exists_cube_minimum ha F hcont)
    (fun x _ => ksFrozen_card_le a x)
  intro x hx hmin hnonvertex
  rcases halternative x hx hmin hnonvertex with hendpoint | hdescent
  · left
    obtain ⟨i, hi, s, hs, hvalue⟩ := hendpoint
    refine ⟨Function.update x i s, ksCube_update_endpoint ha hx i hs, hvalue, ?_⟩
    apply ksFrozen_lt_update x i hi s
    rcases hs with rfl | rfl
    · simpa only [abs_neg] using abs_of_nonneg ha
    · exact abs_of_nonneg ha
  · exact Or.inr hdescent

/-- A continuous cube potential with the endpoint-or-descent alternative
at every nonvertex state has a globally minimizing vertex. -/
theorem exists_vertex_minimum_of_endpoint_or_descent {a : ℝ} (ha : 0 ≤ a)
    (F : (Fin N → ℝ) → ℝ) (hcont : ContinuousOn F (ksCube a))
    (halternative : ∀ x ∈ ksCube a, ¬ ksVertex a x → EndpointOrDescent a F x) :
    ∃ x ∈ ksCube a, ksVertex a x ∧ IsMinOn F (ksCube a) x :=
  exists_vertex_minimum_of_minimizer_alternative ha F hcont
    (fun x hx _ hnonvertex => halternative x hx hnonvertex)

/-- The minimizing vertex has potential at most its value at the center. -/
theorem exists_vertex_le_center {a : ℝ} (ha : 0 ≤ a)
    (F : (Fin N → ℝ) → ℝ) (hcont : ContinuousOn F (ksCube a))
    (halternative : ∀ x ∈ ksCube a, IsMinOn F (ksCube a) x →
      ¬ ksVertex a x → EndpointOrDescent a F x) :
    ∃ x ∈ ksCube a, ksVertex a x ∧ F x ≤ F 0 := by
  obtain ⟨x, hx, hv, hm⟩ :=
    exists_vertex_minimum_of_minimizer_alternative ha F hcont halternative
  exact ⟨x, hx, hv, hm (ksCube_zero ha)⟩

/-- For the unit cube, vertex coordinates are signs on all original labels.
This conclusion does not alter or split the original coordinate index set. -/
theorem exists_full_signing_minimum
    (F : (Fin N → ℝ) → ℝ) (hcont : ContinuousOn F (ksCube 1))
    (halternative : ∀ x ∈ ksCube 1, IsMinOn F (ksCube 1) x →
      ¬ ksVertex 1 x → EndpointOrDescent 1 F x) :
    ∃ s : Fin N → ℝ, IsFullSigning s ∧ IsMinOn F (ksCube 1) s ∧ F s ≤ F 0 := by
  obtain ⟨s, hs, hv, hm⟩ :=
    exists_vertex_minimum_of_minimizer_alternative (by norm_num : (0 : ℝ) ≤ 1)
      F hcont halternative
  refine ⟨s, ?_, hm, hm (ksCube_zero (by norm_num))⟩
  simpa only [div_one] using ksVertex_div_fullSigning (by norm_num : (0 : ℝ) < 1) hv

end HigherRankKS.CompactVertex
