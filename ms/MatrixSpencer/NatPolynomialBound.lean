import Mathlib.Algebra.Order.Monoid.Unbundled.Pow
import Mathlib.Tactic

/-! Fixed polynomial majorants for three natural size parameters. All
exponents and coefficients in a witness are independent of those parameters. -/
namespace MatrixSpencer.NatPolynomialBound

def Bounded (f : ℕ → ℕ → ℕ → ℕ) : Prop :=
  ∃ C e : ℕ, ∀ n d k, f n d k ≤ C * (n + d + k + 2) ^ e

theorem constant (c : ℕ) : Bounded (fun _ _ _ => c) :=
  ⟨c, 0, by intros; simp⟩

theorem first : Bounded (fun n _ _ => n) :=
  ⟨1, 1, by intros; simp; omega⟩

theorem second : Bounded (fun _ d _ => d) :=
  ⟨1, 1, by intros; simp; omega⟩

theorem third : Bounded (fun _ _ k => k) :=
  ⟨1, 1, by intros; simp; omega⟩

theorem add {f g : ℕ → ℕ → ℕ → ℕ} (hf : Bounded f) (hg : Bounded g) :
    Bounded (fun n d k => f n d k + g n d k) := by
  obtain ⟨C, e, hf⟩ := hf
  obtain ⟨D, v, hg⟩ := hg
  refine ⟨C + D, e + v, ?_⟩
  intro n d k
  have hx : 1 ≤ n + d + k + 2 := by omega
  have hp := pow_le_pow_right₀ hx (show e ≤ e + v by omega)
  have hq := pow_le_pow_right₀ hx (show v ≤ e + v by omega)
  have ha := (hf n d k).trans (Nat.mul_le_mul_left C hp)
  have hb := (hg n d k).trans (Nat.mul_le_mul_left D hq)
  nlinarith

theorem mul {f g : ℕ → ℕ → ℕ → ℕ} (hf : Bounded f) (hg : Bounded g) :
    Bounded (fun n d k => f n d k * g n d k) := by
  obtain ⟨C, e, hf⟩ := hf
  obtain ⟨D, v, hg⟩ := hg
  refine ⟨C * D, e + v, ?_⟩
  intro n d k
  have hh := Nat.mul_le_mul (hf n d k) (hg n d k)
  convert hh using 1
  simp only [pow_add]
  ring

theorem pow {f : ℕ → ℕ → ℕ → ℕ} (hf : Bounded f) (p : ℕ) :
    Bounded (fun n d k => f n d k ^ p) := by
  obtain ⟨C, e, hf⟩ := hf
  refine ⟨C ^ p, e * p, ?_⟩
  intro n d k
  have hh := Nat.pow_le_pow_left (hf n d k) p
  simpa only [mul_pow, pow_mul] using hh

theorem of_le {f g : ℕ → ℕ → ℕ → ℕ} (hf : Bounded f)
    (hg : ∀ n d k, g n d k ≤ f n d k) : Bounded g := by
  obtain ⟨C, e, hf⟩ := hf
  exact ⟨C, e, fun n d k => (hg n d k).trans (hf n d k)⟩

end MatrixSpencer.NatPolynomialBound
