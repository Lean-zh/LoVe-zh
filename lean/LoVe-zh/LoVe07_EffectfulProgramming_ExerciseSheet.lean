/- Copyright © 2018–2025 Anne Baanen, Alexander Bentkamp, Jasmin Blanchette,
Xavier Généreux, Johannes Hölzl, and Jannis Limperg. See `LICENSE.txt`. -/

import LoVe.LoVe07_EffectfulProgramming_Demo


/- # LoVe 练习 7：带副作用的编程

将占位符（例如，`:= sorry`）替换为你的解决方案。 -/


set_option autoImplicit false
set_option tactic.hygienic false

namespace LoVe


/- ## 问题1：带有失败处理的状态单子（State Monad with Failure）

我们引入了一种更为丰富的合法单子（lawful monad）概念，它提供了一个满足某些定律的`orelse`操作符，具体定律如下所示。`emp`表示失败。`orelse x y`首先尝试执行`x`，如果`x`失败，则回退执行`y`。 -/

class LawfulMonadWithOrelse (m : Type → Type)
  extends LawfulMonad m where
  emp {α : Type} : m α
  orelse {α : Type} : m α → m α → m α
  emp_orelse {α : Type} (a : m α) :
    orelse emp a = a
  orelse_emp {α : Type} (a : m α) :
    orelse a emp = a
  orelse_assoc {α : Type} (a b c : m α) :
    orelse (orelse a b) c = orelse a (orelse b c)
  emp_bind {α β : Type} (f : α → m β) :
    (emp >>= f) = emp
  bind_emp {α β : Type} (f : m α) :
    (f >>= (fun a ↦ (emp : m β))) = emp

/- 1.1. 我们将 `Option` 类型构造器设置为一个
`LawfulMonad_with_orelse`。请完成证明。

提示：使用 `simp [Bind.bind]` 来展开绑定操作符的定义，
并使用 `simp [Option.orelse]` 来展开 `orelse` 操作符的定义。 -/

def Option.orelse {α : Type} : Option α → Option α → Option α
  | Option.none,   ma' => ma'
  | Option.some a, _   => Option.some a

instance Option.LawfulMonadWithOrelse :
  LawfulMonadWithOrelse Option :=
  { Option.LawfulMonad with
    emp          := Option.none
    orelse       := Option.orelse
    emp_orelse   :=
      sorry
    orelse_emp   :=
      by
        intro α ma
        simp [Option.orelse]
        cases ma
        { rfl }
        { rfl }
    orelse_assoc :=
      sorry
    emp_bind     :=
      by
        intro α β f
        simp [Bind.bind]
        rfl
    bind_emp     :=
      sorry
  }

@[simp] theorem Option.some_bind {α β : Type} (a : α) (g : α → Option β) :
    (Option.some a >>= g) = g a :=
  sorry

/- 1.2. 现在我们已经准备好定义 `FAction σ`：一个具有内部状态类型为 `σ` 且可能失败的单子（与 `Action σ` 不同）。

我们首先定义 `FAction σ α`，其中 `σ` 是内部状态的类型，`α` 是单子中存储的值的类型。我们使用 `Option` 来模拟失败。这意味着在定义 `FAction` 上的单子操作时，我们也可以使用 `Option` 的单子操作。

提示：

* 请记住，`FAction σ α` 是一个函数类型的别名，因此你可以使用模式匹配和 `fun s ↦ …` 来定义类型为 `FAction σ α` 的值。

* `FAction` 与课程演示中的 `Action` 非常相似。你可以参考那里的内容以获取灵感。 -/

def FAction (σ : Type) (α : Type) : Type :=
  sorry

/- 1.3. 为 `FAction` 定义 `get` 和 `set` 函数，其中 `get` 返回通过状态单子传递的状态，而 `set s` 将状态更改为 `s`。 -/

def get {σ : Type} : FAction σ σ :=
  sorry

def set {σ : Type} (s : σ) : FAction σ Unit :=
  sorry

/- 我们在 `FAction` 上设置了 `>>=` 语法。 -/

def FAction.bind {σ α β : Type} (f : FAction σ α) (g : α → FAction σ β) :
  FAction σ β
  | s => f s >>= (fun (a, s) ↦ g a s)

instance FAction.Bind {σ : Type} : Bind (FAction σ) :=
  { bind := FAction.bind }

theorem FAction.bind_apply {σ α β : Type} (f : FAction σ α)
      (g : α → FAction σ β) (s : σ) :
    (f >>= g) s = (f s >>= (fun as ↦ g (Prod.fst as) (Prod.snd as))) :=
  by rfl

/- 1.4. 为 `FAction` 定义 `pure` 操作符，使其满足以下三条定律。 -/

def FAction.pure {σ α : Type} (a : α) : FAction σ α :=
  sorry

/- 我们为 `FAction` 上的 `pure` 设置了语法： -/

instance FAction.Pure {σ : Type} : Pure (FAction σ) :=
  { pure := FAction.pure }

theorem FAction.pure_apply {σ α : Type} (a : α) (s : σ) :
    (pure a : FAction σ α) s = Option.some (a, s) :=
  by rfl

/- 1.5. 将 `FAction` 注册为单子（monad）。

提示：

* 当你需要证明两个函数相等时，`funext` 定理可能会很有用。

* 定理 `FAction.pure_apply` 或 `FAction.bind_apply` 可能会派上用场。 -/

instance FAction.LawfulMonad {σ : Type} : LawfulMonad (FAction σ) :=
  { FAction.Bind, FAction.Pure with
    pure_bind :=
      by
      sorry
    bind_pure :=
      by
        intro α ma
        apply funext
        intro s
        have bind_pure_helper :
          (do
             let x ← ma s
             pure (Prod.fst x) (Prod.snd x)) =
          ma s :=
          by apply LawfulMonad.bind_pure
        aesop
    bind_assoc :=
      sorry
  }


/- ## 问题 2（**可选**）：Kleisli 运算符

Kleisli 运算符 `>=>`（不要与 `>>=` 混淆）在管道化具有副作用（effectful）的函数时非常有用。需要注意的是，`fun a ↦ f a >>= g` 应解析为 `fun a ↦ (f a >>= g)`，而不是 `(fun a ↦ f a) >>= g`。 -/

def kleisli {m : Type → Type} [LawfulMonad m] {α β γ : Type} (f : α → m β)
    (g : β → m γ) : α → m γ :=
  fun a ↦ f a >>= g

infixr:90 (priority := high) " >=> " => kleisli

/- 2.1 （**可选**）。证明 `pure` 是 Kleisli 运算符的左单位和右单位。 -/

theorem pure_kleisli {m : Type → Type} [LawfulMonad m] {α β : Type}
      (f : α → m β) :
    (pure >=> f) = f :=
  sorry

theorem kleisli_pure {m : Type → Type} [LawfulMonad m] {α β : Type}
      (f : α → m β) :
    (f >=> pure) = f :=
  sorry

/- 2.2 （**可选**）。证明Kleisli运算符满足结合律。 -/

theorem kleisli_assoc {m : Type → Type} [LawfulMonad m] {α β γ δ : Type}
      (f : α → m β) (g : β → m γ) (h : γ → m δ) :
    ((f >=> g) >=> h) = (f >=> (g >=> h)) :=
  sorry

end LoVe
