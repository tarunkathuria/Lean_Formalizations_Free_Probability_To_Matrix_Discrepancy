import MatrixSpencer.FiniteSelection
import MatrixSpencer.FiniteProcessMoments
import Mathlib.Order.RelClasses
import Mathlib.Tactic

/-!
# Actually finite weighted trees from lexicographic termination

Every node has a finite positive normalized transition family and records its
legal transition. The existence proof is well-founded induction, so arbitrary
fuel resets after strict rank decreases do not require a global mesh or depth.
These are generic construction and finite-sum lemmas; an epoch must supply its
actual states, transitions, terminal predicate, rank, and fuel.
-/

open scoped BigOperators

noncomputable section
namespace MatrixSpencer
namespace FiniteBranchingTermination

universe u
variable {State : Type u}

/-- A genuinely finite transition family with no zero-weight children. -/
structure Transition (State : Type u) where
  arity : ℕ
  child : Fin arity → State
  weight : Fin arity → ℝ
  weight_pos : ∀ i, 0 < weight i
  weight_sum : (∑ i, weight i) = 1

/-- Reindex any finite positive sampler into the tree's canonical finite child index. -/
def Transition.ofFintype {Ω : Type*} [Fintype Ω] (child : Ω → State) (weight : Ω → ℝ)
    (hwpos : ∀ i, 0 < weight i) (hwsum : (∑ i, weight i) = 1) : Transition State where
  arity := Fintype.card Ω
  child i := child ((Fintype.equivFin Ω).symm i)
  weight i := weight ((Fintype.equivFin Ω).symm i)
  weight_pos i := hwpos _
  weight_sum := by simpa only [Equiv.sum_comp] using hwsum

lemma Transition.ofFintype_expectation {Ω : Type*} [Fintype Ω]
    (child : Ω → State) (weight : Ω → ℝ) (hwpos : ∀ i, 0 < weight i)
    (hwsum : (∑ i, weight i) = 1) (f : State → ℝ) :
    (∑ i, (Transition.ofFintype child weight hwpos hwsum).weight i *
      f ((Transition.ofFintype child weight hwpos hwsum).child i)) =
      ∑ i, weight i * f (child i) := by
  exact (Fintype.equivFin Ω).symm.sum_comp (fun i => weight i * f (child i))

lemma Transition.ofFintype_sum_smul {Ω E : Type*} [Fintype Ω]
    [AddCommMonoid E] [Module ℝ E]
    (child : Ω → State) (weight : Ω → ℝ) (hwpos : ∀ i, 0 < weight i)
    (hwsum : (∑ i, weight i) = 1) (f : State → E) :
    (∑ i, (Transition.ofFintype child weight hwpos hwsum).weight i •
      f ((Transition.ofFintype child weight hwpos hwsum).child i)) =
      ∑ i, weight i • f (child i) := by
  exact (Fintype.equivFin Ω).symm.sum_comp (fun i => weight i • f (child i))

/-- An inductive finite derivation tree, indexed by its actual root state. -/
inductive Tree (terminal : State → Prop) (legal : State → Transition State → Prop) : State → Type u
  | leaf {s : State} (hs : terminal s) : Tree terminal legal s
  | node {s : State} (b : Transition State) (hb : legal s b)
      (children : ∀ i : Fin b.arity, Tree terminal legal (b.child i)) : Tree terminal legal s

variable {terminal : State → Prop} {legal : State → Transition State → Prop}

/-- Any well-founded child relation with finite legal branching gives a finite tree. -/
theorem exists_tree_of_wellFounded (r : State → State → Prop) (hr : WellFounded r)
    (step : ∀ s, ¬terminal s → ∃ b : Transition State, legal s b ∧ ∀ i, r (b.child i) s)
    (start : State) : Nonempty (Tree terminal legal start) := by
  induction start using hr.induction with
  | h s ih =>
    by_cases hs : terminal s
    · exact ⟨Tree.leaf hs⟩
    · obtain ⟨b, hb, hchild⟩ := step s hs
      exact ⟨Tree.node b hb (fun i => Classical.choice (ih (b.child i) (hchild i)))⟩

/-- The actual rank/fuel child relation; fuel is unrestricted on a strict rank drop. -/
def RankFuelDecrease (rank fuel : State → ℕ) (child parent : State) : Prop :=
  rank child < rank parent ∨ rank child = rank parent ∧ fuel child < fuel parent

lemma rankFuelDecrease_wellFounded (rank fuel : State → ℕ) :
    WellFounded (RankFuelDecrease rank fuel) := by
  have hw := InvImage.wf (fun s => (rank s, fuel s))
    (Nat.lt_wfRel.wf.prod_lex Nat.lt_wfRel.wf)
  apply Subrelation.wf (fun {a b} h => Prod.lex_def.mpr h) hw

/-- Finite branching plus lexicographic rank/fuel descent constructs an actual finite tree. -/
theorem exists_tree_of_rank_fuel (rank fuel : State → ℕ)
    (step : ∀ s, ¬terminal s → ∃ b : Transition State, legal s b ∧
      ∀ i, rank (b.child i) < rank s ∨
        rank (b.child i) = rank s ∧ fuel (b.child i) < fuel s)
    (start : State) : Nonempty (Tree terminal legal start) :=
  exists_tree_of_wellFounded (RankFuelDecrease rank fuel)
    (rankFuelDecrease_wellFounded rank fuel) step start

namespace Tree

/-- Leaves are path occurrences, so different branches ending in the same state remain distinct. -/
def Leaves : {s : State} → Tree terminal legal s → Type
  | _, .leaf _ => PUnit
  | _, .node b _ children => (i : Fin b.arity) × Leaves (children i)

instance leavesFintype : {s : State} → (t : Tree terminal legal s) → Fintype t.Leaves
  | _, .leaf _ => inferInstanceAs (Fintype PUnit)
  | _, .node _ _ children =>
    @Sigma.instFintype _ _ (fun i => leavesFintype (children i)) inferInstance

def leafState : {s : State} → (t : Tree terminal legal s) → t.Leaves → State
  | s, .leaf _ => fun _ => s
  | _, .node _ _ children => fun l => leafState (children l.1) l.2

def leafWeight : {s : State} → (t : Tree terminal legal s) → t.Leaves → ℝ
  | _, .leaf _ => fun _ => 1
  | _, .node b _ children => fun l => b.weight l.1 * leafWeight (children l.1) l.2

def nodeCount : {s : State} → Tree terminal legal s → ℕ
  | _, .leaf _ => 1
  | _, .node _ _ children => 1 + ∑ i, nodeCount (children i)

lemma nodeCount_pos {s : State} (t : Tree terminal legal s) : 0 < t.nodeCount := by
  cases t <;> simp only [nodeCount] <;> omega

lemma leaf_terminal {s : State} (t : Tree terminal legal s) (l : t.Leaves) :
    terminal (t.leafState l) := by
  induction t with
  | leaf hs => exact hs
  | node b hb children ih => exact ih l.1 l.2

lemma leafWeight_pos {s : State} (t : Tree terminal legal s) (l : t.Leaves) :
    0 < t.leafWeight l := by
  induction t with
  | leaf hs => exact zero_lt_one
  | node b hb children ih => exact mul_pos (b.weight_pos l.1) (ih l.1 l.2)

lemma leafWeight_sum {s : State} (t : Tree terminal legal s) :
    (∑ l : t.Leaves, t.leafWeight l) = 1 := by
  induction t with
  | leaf hs => simp [Leaves, leafWeight]
  | node b hb children ih =>
    change (∑ l : (i : Fin b.arity) × (children i).Leaves,
      b.weight l.1 * (children l.1).leafWeight l.2) = 1
    rw [Fintype.sum_sigma]
    simp only [← Finset.mul_sum, ih, mul_one, b.weight_sum]

/-- A tree's leaf type is nonempty, as follows from its proved normalization. -/
lemma leaves_nonempty {s : State} (t : Tree terminal legal s) : Nonempty t.Leaves := by
  by_contra h
  haveI : IsEmpty t.Leaves := not_nonempty_iff.mp h
  have hw := t.leafWeight_sum
  simp at hw

def expectation {s : State} (t : Tree terminal legal s) (f : State → ℝ) : ℝ :=
  ∑ l : t.Leaves, t.leafWeight l * f (t.leafState l)

lemma expectation_leaf {s : State} (hs : terminal s) (f : State → ℝ) :
    (Tree.leaf (legal := legal) hs).expectation f = f s := by
  simp [expectation, Leaves, leafWeight, leafState]

lemma expectation_node {s : State} (b : Transition State) (hb : legal s b)
    (children : ∀ i, Tree terminal legal (b.child i)) (f : State → ℝ) :
    (Tree.node b hb children).expectation f = ∑ i, b.weight i * (children i).expectation f := by
  change (∑ l : (i : Fin b.arity) × (children i).Leaves,
    (b.weight l.1 * (children l.1).leafWeight l.2) * f ((children l.1).leafState l.2)) = _
  rw [Fintype.sum_sigma]
  simp only [expectation, Finset.mul_sum, mul_assoc]

lemma expectation_const {s : State} (t : Tree terminal legal s) (c : ℝ) :
    t.expectation (fun _ => c) = c := by
  simp only [expectation, ← Finset.sum_mul, t.leafWeight_sum, one_mul]

lemma expectation_neg {s : State} (t : Tree terminal legal s) (f : State → ℝ) :
    t.expectation (fun s => -f s) = -t.expectation f := by
  simp only [expectation, mul_neg, Finset.sum_neg_distrib]

/-- Local expected inequalities telescope over the constructed finite tree. -/
lemma expectation_le_of_local {s : State} (t : Tree terminal legal s) (f : State → ℝ)
    (hlocal : ∀ s b, legal s b → (∑ i, b.weight i * f (b.child i)) ≤ f s) :
    t.expectation f ≤ f s := by
  induction t with
  | leaf hs => exact (expectation_leaf hs f).le
  | node b hb children ih =>
    rw [expectation_node]
    exact (Finset.sum_le_sum (fun i _ =>
      mul_le_mul_of_nonneg_left (ih i) (b.weight_pos i).le)).trans (hlocal _ b hb)

/-- Accumulated edge cost on a particular leaf path. -/
def pathCost (cost : State → State → ℝ) : {s : State} → (t : Tree terminal legal s) → t.Leaves → ℝ
  | _, .leaf _ => fun _ => 0
  | s, .node b _ children => fun l => cost s (b.child l.1) + pathCost cost (children l.1) l.2

def expectedCost {s : State} (t : Tree terminal legal s) (cost : State → State → ℝ) : ℝ :=
  ∑ l : t.Leaves, t.leafWeight l * t.pathCost cost l

lemma pathCost_nonneg {s : State} (t : Tree terminal legal s) (cost : State → State → ℝ)
    (hcost : ∀ s b, legal s b → ∀ i, 0 ≤ cost s (b.child i)) (l : t.Leaves) :
    0 ≤ t.pathCost cost l := by
  induction t with
  | leaf hs => exact le_rfl
  | node b hb children ih => exact add_nonneg (hcost _ b hb l.1) (ih l.1 l.2)

lemma expectedCost_nonneg {s : State} (t : Tree terminal legal s) (cost : State → State → ℝ)
    (hcost : ∀ s b, legal s b → ∀ i, 0 ≤ cost s (b.child i)) : 0 ≤ t.expectedCost cost :=
  Finset.sum_nonneg (fun l _ => mul_nonneg (t.leafWeight_pos l).le (t.pathCost_nonneg cost hcost l))

lemma expectedCost_leaf {s : State} (hs : terminal s) (cost : State → State → ℝ) :
    (Tree.leaf (legal := legal) hs).expectedCost cost = 0 := by
  simp [expectedCost, pathCost, Leaves, leafWeight]

lemma expectedCost_node {s : State} (b : Transition State) (hb : legal s b)
    (children : ∀ i, Tree terminal legal (b.child i)) (cost : State → State → ℝ) :
    (Tree.node b hb children).expectedCost cost =
      ∑ i, b.weight i * (cost s (b.child i) + (children i).expectedCost cost) := by
  change (∑ l : (i : Fin b.arity) × (children i).Leaves,
    (b.weight l.1 * (children l.1).leafWeight l.2) *
      (cost s (b.child l.1) + (children l.1).pathCost cost l.2)) = _
  rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro i _
  simp only [mul_add, mul_assoc, ← Finset.mul_sum, Finset.sum_add_distrib,
    ← Finset.sum_mul, (children i).leafWeight_sum, one_mul, expectedCost]

/-- Paid edge costs and the terminal potential telescope together. -/
lemma expectation_add_cost_le_of_local {s : State} (t : Tree terminal legal s)
    (f : State → ℝ) (cost : State → State → ℝ)
    (hlocal : ∀ s b, legal s b →
      (∑ i, b.weight i * (f (b.child i) + cost s (b.child i))) ≤ f s) :
    t.expectation f + t.expectedCost cost ≤ f s := by
  induction t with
  | leaf hs => simp only [expectation_leaf, expectedCost_leaf, add_zero, le_refl]
  | node b hb children ih =>
    rw [expectation_node, expectedCost_node]
    calc
      _ = ∑ i, b.weight i *
          ((children i).expectation f + (children i).expectedCost cost + cost _ (b.child i)) := by
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ ≤ ∑ i, b.weight i * (f (b.child i) + cost _ (b.child i)) :=
        Finset.sum_le_sum (fun i _ =>
          mul_le_mul_of_nonneg_left (add_le_add_right (ih i) _) (b.weight_pos i).le)
      _ ≤ _ := hlocal _ b hb

lemma pathCost_neg {s : State} (t : Tree terminal legal s) (cost : State → State → ℝ)
    (l : t.Leaves) : t.pathCost (fun a b => -cost a b) l = -t.pathCost cost l := by
  induction t with
  | leaf hs => exact neg_zero.symm
  | node b hb children ih =>
    change -cost _ _ + (children l.1).pathCost (fun a b => -cost a b) l.2 = _
    rw [ih l.1 l.2]
    exact (neg_add _ _).symm

lemma expectedCost_neg {s : State} (t : Tree terminal legal s) (cost : State → State → ℝ) :
    t.expectedCost (fun a b => -cost a b) = -t.expectedCost cost := by
  simp only [expectedCost, pathCost_neg, mul_neg, Finset.sum_neg_distrib]

/-- Local drift allowances telescope to the expected sum of the actual edge allowances. -/
lemma expectation_le_add_cost_of_local {s : State} (t : Tree terminal legal s)
    (f : State → ℝ) (cost : State → State → ℝ)
    (hlocal : ∀ s b, legal s b →
      (∑ i, b.weight i * f (b.child i)) ≤ f s + ∑ i, b.weight i * cost s (b.child i)) :
    t.expectation f ≤ f s + t.expectedCost cost := by
  have hpaid : ∀ s b, legal s b →
      (∑ i, b.weight i * (f (b.child i) + -cost s (b.child i))) ≤ f s := by
    intro s b hb
    have h := hlocal s b hb
    simp only [mul_add, mul_neg, Finset.sum_add_distrib, Finset.sum_neg_distrib]
    linarith
  have h := t.expectation_add_cost_le_of_local f (fun a b => -cost a b) hpaid
  rw [expectedCost_neg] at h
  linarith

/-- Exact local moment identities give exact finite-tree moment identities. -/
lemma expectation_eq_add_cost_of_local {s : State} (t : Tree terminal legal s)
    (f : State → ℝ) (cost : State → State → ℝ)
    (hlocal : ∀ s b, legal s b →
      (∑ i, b.weight i * f (b.child i)) = f s + ∑ i, b.weight i * cost s (b.child i)) :
    t.expectation f = f s + t.expectedCost cost := by
  apply le_antisymm (t.expectation_le_add_cost_of_local f cost (fun s b hb => (hlocal s b hb).le))
  have hneg : ∀ s b, legal s b →
      (∑ i, b.weight i * -f (b.child i)) ≤ -f s + ∑ i, b.weight i * -cost s (b.child i) := by
    intro s b hb
    simp only [mul_neg, Finset.sum_neg_distrib]
    rw [hlocal s b hb, neg_add]
  have h := t.expectation_le_add_cost_of_local (fun s => -f s) (fun a b => -cost a b) hneg
  rw [expectation_neg, expectedCost_neg] at h
  linarith

/-- The legal one-edge relation exposed by the stored transition families. -/
def Edge (legal : State → Transition State → Prop) (s t : State) : Prop :=
  ∃ b, legal s b ∧ ∃ i, b.child i = t

lemma leaf_reachable {s : State} (t : Tree terminal legal s) (l : t.Leaves) :
    Relation.ReflTransGen (Edge legal) s (t.leafState l) := by
  induction t with
  | leaf hs => exact Relation.ReflTransGen.refl
  | node b hb children ih =>
    exact (ih l.1 l.2).head ⟨b, hb, l.1, rfl⟩

/-- Any state invariant preserved by each legal edge holds at all leaves. -/
lemma leaf_invariant {s : State} (t : Tree terminal legal s) (invariant : State → Prop)
    (hstart : invariant s)
    (hpreserve : ∀ s b, legal s b → invariant s → ∀ i, invariant (b.child i))
    (l : t.Leaves) : invariant (t.leafState l) := by
  induction t with
  | leaf hs => exact hstart
  | node b hb children ih => exact ih l.1 (hpreserve _ b hb hstart l.1) l.2

/-- The finite-process local Euclidean second-moment identity applies directly to tree leaves. -/
lemma expectation_norm_sq_eq {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {s : State} (t : Tree terminal legal s) (X : State → E)
    (hcenter : ∀ s b, legal s b →
      (∑ i, b.weight i • (X (b.child i) - X s)) = 0) :
    t.expectation (fun s => ‖X s‖ ^ 2) = ‖X s‖ ^ 2 +
      t.expectedCost (fun a b => ‖X b - X a‖ ^ 2) := by
  apply t.expectation_eq_add_cost_of_local
  intro s b hb
  simpa only [add_sub_cancel] using FiniteProcessMoments.weighted_norm_sq_add
    b.weight (fun i => X (b.child i) - X s) (X s) b.weight_sum (hcenter s b hb)

/-- Scalar martingale tangent fluctuations have the expected accumulated square increment. -/
lemma expectation_scalar_sq_eq {s : State} (t : Tree terminal legal s) (M : State → ℝ)
    (hcenter : ∀ s b, legal s b →
      (∑ i, b.weight i * (M (b.child i) - M s)) = 0) :
    t.expectation (fun s => M s ^ 2) = M s ^ 2 +
      t.expectedCost (fun a b => (M b - M a) ^ 2) := by
  simpa only [Real.norm_eq_abs, sq_abs] using t.expectation_norm_sq_eq M
    (fun s b hb => by simpa only [smul_eq_mul] using hcenter s b hb)

end Tree
end FiniteBranchingTermination
end MatrixSpencer
