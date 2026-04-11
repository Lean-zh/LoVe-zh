/- Copyright © 2018–2025 Anne Baanen, Alexander Bentkamp, Jasmin Blanchette,
Xavier Généreux, Johannes Hölzl, and Jannis Limperg. See `LICENSE.txt`. -/

import LoVe.LoVe09_OperationalSemantics_Demo


/- # LoVe 练习 9：操作语义

将占位符（例如，`:= sorry`）替换为您的解答。 -/


set_option autoImplicit false
set_option tactic.hygienic false

namespace LoVe


/- ## 问题 1：守护命令语言（Guarded Command Language）

1976年，E. W. Dijkstra 提出了守护命令语言（GCL），这是一种内置非确定性的极简命令式语言。以下是其一种变体的语法：

    S  ::=  x := e       -- 赋值
         |  assert B     -- 断言
         |  S ; S        -- 顺序组合
         |  S | ⋯ | S    -- 非确定性选择
         |  loop S       -- 非确定性迭代

赋值和顺序组合与 WHILE 语言中的相同。其他语句的语义如下：

* `assert B` 如果 `B` 求值为假，则中止；否则，该命令不执行任何操作。

* `S | ⋯ | S` 选择任意一个分支执行，忽略其他分支。

* `loop S` 执行 `S` 任意次数。

在 Lean 中，GCL 通过以下归纳类型来捕获： -/s `S` any number of times.

In Lean, GCL is captured by the following inductive type: -/

namespace GCL

inductive Stmt : Type
  | assign : String → (State → ℕ) → Stmt
  | assert : (State → Prop) → Stmt
  | seq    : Stmt → Stmt → Stmt
  | choice : List Stmt → Stmt
  | loop   : Stmt → Stmt

infixr:90 "; " => Stmt.seq

/- 1.1. 根据上述GCL的非正式规范，完成以下大步语义（big-step semantics）的补充。 -/

inductive BigStep : (Stmt × State) → State → Prop
  -- 在此处输入缺失的 `assign` 规则  | assert (B s) (hB : B s) :
    BigStep (Stmt.assert B, s) s
  -- 在此处输入缺失的 `seq` 规则  -- 以下内容中，`Ss[i]'hless` 返回 `Ss` 的第 `i` 个元素，该元素的存在得益于  -- 条件 `hless`  | choice (Ss s t i) (hless : i < List.length Ss)
      (hbody : BigStep (Ss[i]'hless, s) t) :
    BigStep (Stmt.choice Ss, s) t
  -- 在此处输入缺失的 `loop` 规则
infixl:110 " ⟹ " => BigStep

/- 1.2. 证明以下的反演规则，正如我们在课堂上为WHILE语言所做的那样。 -/

@[simp] theorem BigStep_assign_iff {x a s t} :
    (Stmt.assign x a, s) ⟹ t ↔ t = s[x ↦ a s] :=
  sorry

@[simp] theorem BigStep_assert {B s t} :
    (Stmt.assert B, s) ⟹ t ↔ t = s ∧ B s :=
  sorry

@[simp] theorem BigStep_seq_iff {S₁ S₂ s t} :
    (Stmt.seq S₁ S₂, s) ⟹ t ↔ (∃u, (S₁, s) ⟹ u ∧ (S₂, u) ⟹ t) :=
  sorry

theorem BigStep_loop {S s u} :
    (Stmt.loop S, s) ⟹ u ↔
    (s = u ∨ (∃t, (S, s) ⟹ t ∧ (Stmt.loop S, t) ⟹ u)) :=
  sorry

/- 这个任务更具挑战性： -/

@[simp] theorem BigStep_choice {Ss s t} :
    (Stmt.choice Ss, s) ⟹ t ↔
    (∃(i : ℕ) (hless : i < List.length Ss), (Ss[i]'hless, s) ⟹ t) :=
  sorry

end GCL

/- 1.3. 完成以下确定性程序到GCL（Guarded Command Language，守卫命令语言）程序的翻译，通过填补下面的`sorry`占位符来实现。 -/

def gcl_of : Stmt → GCL.Stmt
  | Stmt.skip =>
    GCL.Stmt.assert (fun _ ↦ True)
  | Stmt.assign x a =>
    sorry
  | S; T =>
    sorry
  | Stmt.ifThenElse B S T  =>
    sorry
  | Stmt.whileDo B S =>
    sorry

/- 1.4. 在上述 `gcl_of` 的定义中，`skip` 被翻译为 `assert (fun _ ↦ True)`。通过观察这两种结构的大步语义，我们可以确信这种翻译是合理的。你能想到其他正确的方式来定义 `skip` 的情况吗？ -/

-- 请将以下技术文档翻译成中文，保持专业术语准确：

**原文：**
The system architecture is designed to support high availability and scalability. It consists of multiple microservices that communicate via RESTful APIs. Each microservice is deployed in a Docker container and orchestrated using Kubernetes. The database layer utilizes a distributed SQL database to ensure data consistency and fault tolerance. Additionally, the system integrates with third-party services through OAuth 2.0 for secure authentication and authorization.

**翻译：**
系统架构设计旨在支持高可用性和可扩展性。它由多个通过RESTful API进行通信的微服务组成。每个微服务都部署在Docker容器中，并使用Kubernetes进行编排。数据库层采用分布式SQL数据库，以确保数据一致性和容错性。此外，系统通过OAuth 2.0与第三方服务集成，以实现安全的身份验证和授权。

/- ## 问题2：程序等价性

在本问题中，我们引入程序等价性的概念：`S₁ ~ S₂`。 -/

def BigStepEquiv (S₁ S₂ : Stmt) : Prop :=
  ∀s t, (S₁, s) ⟹ t ↔ (S₂, s) ⟹ t

infix:50 (priority := high) " ~ " => BigStepEquiv

/- 程序等价性是一种等价关系，即它具有自反性、对称性和传递性。 -/

theorem BigStepEquiv.refl {S} :
    S ~ S :=
  fix s t : State
  show (S, s) ⟹ t ↔ (S, s) ⟹ t from
    by rfl

theorem BigStepEquiv.symm {S₁ S₂} :
    S₁ ~ S₂ → S₂ ~ S₁ :=
  assume h : S₁ ~ S₂
  fix s t : State
  show (S₂, s) ⟹ t ↔ (S₁, s) ⟹ t from
    Iff.symm (h s t)

theorem BigStepEquiv.trans {S₁ S₂ S₃} (h₁₂ : S₁ ~ S₂) (h₂₃ : S₂ ~ S₃) :
    S₁ ~ S₃ :=
  fix s t : State
  show (S₁, s) ⟹ t ↔ (S₃, s) ⟹ t from
    Iff.trans (h₁₂ s t) (h₂₃ s t)

/- 2.1. 证明以下程序等价性。 -/

theorem BigStepEquiv.skip_assign_id {x} :
    Stmt.assign x (fun s ↦ s x) ~ Stmt.skip :=
  sorry

theorem BigStepEquiv.seq_skip_left {S} :
    Stmt.skip; S ~ S :=
  sorry

theorem BigStepEquiv.seq_skip_right {S} :
    S; Stmt.skip ~ S :=
  sorry

theorem BigStepEquiv.if_seq_while_skip {B S} :
    Stmt.ifThenElse B (S; Stmt.whileDo B S) Stmt.skip ~ Stmt.whileDo B S :=
  sorry

/- 2.2 （**可选**）。程序等价性可用于将子程序替换为具有相同语义的其他子程序。证明以下所谓的同余规则，这些规则有助于此类替换： -/

theorem BigStepEquiv.seq_congr {S₁ S₂ T₁ T₂} (hS : S₁ ~ S₂)
      (hT : T₁ ~ T₂) :
    S₁; T₁ ~ S₂; T₂ :=
  sorry

theorem BigStepEquiv.if_congr {B S₁ S₂ T₁ T₂} (hS : S₁ ~ S₂) (hT : T₁ ~ T₂) :
    Stmt.ifThenElse B S₁ T₁ ~ Stmt.ifThenElse B S₂ T₂ :=
  sorry

end LoVe
