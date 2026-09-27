import MatrixSpencer.RealRAMProgram

/-! Register renaming compiles a primitive program into a larger register bank.
It preserves every primitive count and touches no address outside the image.
This is a syntax transformation, not an opaque subroutine instruction. -/
namespace MatrixSpencer.RealRAM
namespace Expr
variable {ι κ : Type*}
def rename (f : ι → κ) : Expr ι → Expr κ
  | .input i => .input (f i)
  | .constant r => .constant r
  | .add a b => .add (rename f a) (rename f b)
  | .sub a b => .sub (rename f a) (rename f b)
  | .mul a b => .mul (rename f a) (rename f b)
  | .div a b => .div (rename f a) (rename f b)
  | .sqrt a => .sqrt (rename f a)
@[simp] theorem eval_rename (f : ι → κ) (e : Expr ι) (v : κ → ℝ) :
    (e.rename f).eval v=e.eval (v ∘ f) := by
  induction e <;> simp_all [rename,eval]
@[simp] theorem cost_rename (f : ι → κ) (e : Expr ι) : (e.rename f).cost=e.cost := by
  induction e <;> simp_all [rename,cost]
@[simp] theorem valid_rename (f : ι → κ) (e : Expr ι) (v : κ → ℝ) :
    (e.rename f).Valid v ↔ e.Valid (v ∘ f) := by
  induction e <;> simp_all [rename,Valid]
end Expr
namespace Program
variable {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
def rename (f : ι → κ) : Program ι → Program κ
  | .skip => .skip
  | .assign i e => .assign (f i) (e.rename f)
  | .seq p q => .seq (rename f p) (rename f q)
  | .branchLE a b p q => .branchLE (a.rename f) (b.rename f) (rename f p) (rename f q)
  | .repeat n p => .repeat n (rename f p)

omit [DecidableEq ι] [DecidableEq κ] in
@[simp] theorem bound_rename (f : ι → κ) (p : Program ι) : (p.rename f).bound=p.bound := by
  induction p <;> simp_all [rename,bound]

theorem run_rename (f : ι → κ) (hf : Function.Injective f) (p : Program ι) (v : κ → ℝ) :
    (p.rename f).run v ∘ f=p.run (v ∘ f) := by
  induction p generalizing v with
  | skip => rfl
  | assign i e =>
    funext j
    simp only [rename,run,Expr.eval_rename,Function.comp_apply]
    by_cases h : j=i
    · subst j; simp
    · have hfi : f j≠f i := fun he => h (hf he)
      simp [h,hfi]
  | seq p q ip iq =>
    change (q.rename f).run ((p.rename f).run v) ∘ f = _
    rw [iq,ip]; rfl
  | branchLE a b p q ip iq =>
    simp only [rename,run,Expr.eval_rename]
    split_ifs <;> first | exact ip v | exact iq v
  | «repeat» n p ip =>
    change ((p.rename f).run)^[n] v ∘ f = (p.run)^[n] (v ∘ f)
    induction n generalizing v with
    | zero => rfl
    | succ n ih =>
      rw [Function.iterate_succ_apply,Function.iterate_succ_apply,ih,ip]

omit [DecidableEq ι] in
theorem run_rename_outside (f : ι → κ) (p : Program ι) (v : κ → ℝ) (j : κ)
    (hj : ∀i,f i≠j) : (p.rename f).run v j=v j := by
  induction p generalizing v with
  | skip => rfl
  | assign i e => simp [rename,run,Ne.symm (hj i)]
  | seq p q ip iq =>
    change (q.rename f).run ((p.rename f).run v) j=v j
    rw [iq,ip]
  | branchLE a b p q ip iq =>
    simp only [rename,run]
    split_ifs <;> first | exact ip v | exact iq v
  | «repeat» n p ip =>
    change ((p.rename f).run)^[n] v j=v j
    induction n generalizing v with
    | zero => rfl
    | succ n ih => rw [Function.iterate_succ_apply,ih,ip]

theorem safe_rename (f : ι → κ) (hf : Function.Injective f) (p : Program ι) (v : κ → ℝ) :
    (p.rename f).Safe v ↔ p.Safe (v ∘ f) := by
  induction p generalizing v with
  | skip => rfl
  | assign i e => exact Expr.valid_rename f e v
  | seq p q ip iq =>
    simp only [rename,Safe,ip,iq,run_rename f hf p v]
  | branchLE a b p q ip iq =>
    simp only [rename,Safe,Expr.valid_rename,Expr.eval_rename]
    split_ifs <;> simp only [ip,iq]
  | «repeat» n p ip =>
    simp only [rename,Safe,ip]
    have hiter : ∀k, ((p.rename f).run)^[k] v ∘ f=(p.run)^[k] (v ∘ f) := by
      intro k
      exact run_rename f hf (.repeat k p) v
    simp only [hiter]
end Program
end MatrixSpencer.RealRAM
