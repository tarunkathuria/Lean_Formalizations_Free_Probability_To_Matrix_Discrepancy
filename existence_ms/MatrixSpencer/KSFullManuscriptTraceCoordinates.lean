import MatrixSpencer.KSFullManuscriptHermitianCoordinates

/-!
# Explicit trace-zero entry coordinates

Remove one diagonal coordinate and recover it as minus the sum of the other
diagonal coordinates. This gives exactly all trace-zero Hermitian matrices,
using finite sums and the fixed entry chart. No null-space basis is chosen.
-/

open Matrix
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section
namespace MatrixSpencer.KSFullManuscriptTraceCoordinates

open KSFullManuscriptHermitianCoordinates
variable {n : Type*} [Fintype n] [LinearOrder n]

abbrev Index (a : n) := {p : n × n // p ≠ (a, a)}

def embed (a : n) (x : Index a → ℝ) (p : n × n) : ℝ :=
  if h : p ≠ (a, a) then x ⟨p, h⟩ else 0

def complete (a : n) (x : Index a → ℝ) (p : n × n) : ℝ :=
  embed a x p - if p = (a, a) then ∑ i, embed a x (i, i) else 0

theorem complete_sum (a : n) (x : Index a → ℝ) : ∑ i, complete a x (i, i) = 0 := by
  simp only [complete, Finset.sum_sub_distrib, Prod.mk.injEq, and_self]
  simp

theorem complete_restrict (a : n) (x : n × n → ℝ) :
    complete a (fun p => x p.val) = fun p => x p - if p = (a, a) then ∑ i, x (i, i) else 0 := by
  have he (p : n × n) : embed a (fun p => x p.val) p = x p - if p = (a, a) then x (a,a) else 0 := by
    by_cases hp : p = (a,a)
    · subst p; simp [embed]
    · simp [embed, hp]
  have hsum : ∑ i, embed a (fun p => x p.val) (i, i) = (∑ i, x (i, i)) - x (a, a) := by
    simp only [he, Finset.sum_sub_distrib, Prod.mk.injEq, and_self]
    simp
  funext p
  rw [complete, he, hsum]
  split_ifs with hp
  · subst p; ring
  · simp only [sub_zero]

theorem complete_trace_zero (a : n) (x : Index a → ℝ) : realTrace (decode (complete a x)) = 0 := by
  rw [decode_trace, complete_sum]

theorem complete_add (a : n) (x y : Index a → ℝ) : complete a (x + y) = complete a x + complete a y := by
  have he : embed a (x + y) = embed a x + embed a y := by
    funext p
    simp only [embed, Pi.add_apply]
    split_ifs <;> simp
  funext p
  simp only [complete, he, Pi.add_apply, Finset.sum_add_distrib]
  split_ifs <;> ring

theorem complete_smul (a : n) (r : ℝ) (x : Index a → ℝ) : complete a (r • x) = r • complete a x := by
  have he : embed a (r • x) = r • embed a x := by
    funext p
    simp only [embed, Pi.smul_apply, smul_eq_mul]
    split_ifs <;> simp
  funext p
  simp only [complete, he, Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum]
  split_ifs <;> ring

def linear (a : n) : (Index a → ℝ) →ₗ[ℝ] selfAdjoint (Matrix n n ℂ) where
  toFun x := ⟨decode (complete a x), decode_isHermitian _⟩
  map_add' x y := by
    apply Subtype.ext
    change decode (complete a (x + y)) = decode (complete a x) + decode (complete a y)
    rw [complete_add, decode_add]
  map_smul' r x := by
    apply Subtype.ext
    change decode (complete a (r • x)) = r • decode (complete a x)
    rw [complete_smul, decode_smul]

theorem linear_trace (a : n) (x : Index a → ℝ) : realTrace (linear a x : Matrix n n ℂ) = 0 :=
  complete_trace_zero a x

theorem linear_injective (a : n) : Function.Injective (linear a) := by
  intro x y hxy
  have he : complete a x = complete a y := by
    have hh := congrArg (fun A : selfAdjoint (Matrix n n ℂ) => encode (A : Matrix n n ℂ)) hxy
    change encode (decode (complete a x)) = encode (decode (complete a y)) at hh
    simpa only [encode_decode] using hh
  funext p
  have hp := congrFun he p.val
  simpa only [complete, if_neg p.property, sub_zero, embed, dif_pos p.property] using hp

/-- Every physical trace-zero Hermitian matrix has the explicit coordinates
obtained by reading its entries, with the removed diagonal omitted. -/
theorem linear_onto_trace_zero (a : n) (A : selfAdjoint (Matrix n n ℂ))
    (htr : realTrace (A : Matrix n n ℂ) = 0) :
    linear a (fun p => encode (A : Matrix n n ℂ) p.val) = A := by
  have hs : ∑ i, encode (A : Matrix n n ℂ) (i, i) = 0 := by
    rw [← decode_trace, decode_encode _ A.property, htr]
  apply Subtype.ext
  change decode (complete a (fun p => encode (A : Matrix n n ℂ) p.val)) = _
  rw [complete_restrict]
  simp only [hs, ite_self, sub_zero]
  exact decode_encode _ A.property

end MatrixSpencer.KSFullManuscriptTraceCoordinates
