/- Copyright © 2018–2025 Anne Baanen, Alexander Bentkamp, Jasmin Blanchette,
Xavier Généreux, Johannes Hölzl, and Jannis Limperg. See `LICENSE.txt`. -/

import LoVe.LoVe06_InductivePredicates_Demo


/- # LoVe 演示 8：元编程

用户可以通过自定义策略和工具来扩展 Lean。这种编程——即对证明器进行编程——被称为**元编程**。

Lean 的元编程框架主要使用与 Lean 输入语言相同的概念和语法。抽象语法树（AST）**反映**了内部数据结构，例如表达式（项）的数据结构。证明器的内部机制通过 Lean 接口暴露出来，我们可以利用这些接口实现以下功能：

* 访问当前上下文和目标；
* 对表达式进行合一（unification）；
* 查询和修改环境；
* 设置属性。

Lean 的大部分功能都是用 Lean 自身实现的。

元编程的应用示例包括：

* 证明目标的转换；
* 启发式证明搜索；
* 决策过程；
* 定义生成器；
* 辅助工具；
* 导出工具；
* 临时自动化。

Lean 元编程框架的优势：

* 用户无需学习另一种编程语言来编写元程序；他们可以使用与定义证明器库中普通对象相同的结构和符号。
* 库中的所有内容都可以用于元编程。
* 元程序可以在相同的交互式环境中编写和调试，鼓励一种形式化库和支持自动化同时开发的风格。 -/


set_option autoImplicit false
set_option tactic.hygienic false

open Lean
open Lean.Meta
open Lean.Elab.Tactic
open Lean.TSyntax

namespace LoVe


/- ## 策略组合子

在编写我们自己的策略时，我们经常需要在多个目标上重复某些操作，或者在策略失败时进行恢复。策略组合子在这种情况下非常有用。

`repeat'` 会将其参数重复应用于所有（子…子）目标，直到无法再应用为止。 -/

theorem repeat'_example :
    Even 4 ∧ Even 7 ∧ Even 3 ∧ Even 0 :=
  by
    repeat' apply And.intro
    repeat' apply Even.add_two
    repeat' sorry

/- “first”组合子 `first | ⋯ | ⋯ | ⋯` 首先尝试其第一个参数。如果失败，则应用第二个参数。如果再次失败，则应用第三个参数。以此类推。 -/

theorem repeat'_first_example :
    Even 4 ∧ Even 7 ∧ Even 3 ∧ Even 0 :=
  by
    repeat' apply And.intro
    repeat'
      first
      | apply Even.add_two
      | apply Even.zero
    repeat' sorry

/- `all_goals` 将其参数精确地应用于每个目标一次。仅当该参数在**所有**目标上都成功时，`all_goals` 才会成功。 -/

/- 定理 all_goals_example :
    偶数 4 ∧ 偶数 7 ∧ 偶数 3 ∧ 偶数 0 :=
  by
    repeat' apply And.intro
    all_goals apply Even.add_two   -- 失败
    repeat' sorry

### 翻译说明：
1. **theorem** 翻译为 **定理**，表示一个数学或逻辑命题。
2. **Even** 翻译为 **偶数**，表示一个数是偶数。
3. **∧** 是逻辑与运算符，翻译为 **且**。
4. **:=** 表示定义或证明的开始，通常不翻译。
5. **by** 表示证明的开始，通常不翻译。
6. **repeat' apply And.intro** 翻译为 **重复应用 And.intro**，表示重复应用逻辑与的引入规则。
7. **all_goals apply Even.add_two** 翻译为 **对所有目标应用 Even.add_two**，表示尝试对所有子目标应用偶数加二的规则。
8. **fails** 翻译为 **失败**，表示该步骤无法成功完成。
9. **repeat' sorry** 翻译为 **重复使用 sorry**，表示暂时跳过这些步骤，通常用于占位或未完成的证明。

### 专业术语：
- **Even**：偶数
- **And.intro**：逻辑与的引入规则
- **Even.add_two**：偶数加二的规则
- **all_goals**：所有目标
- **repeat'**：重复
- **sorry**：占位符，表示未完成的证明步骤

### 总结：
该定理试图证明 4、7、3 和 0 都是偶数，但在应用 `Even.add_two` 规则时失败，因此使用了 `sorry` 来跳过未完成的证明步骤。 -/" 通常指的是系统、设备或组件未能按预期工作或执行其功能的情况。它可以用于描述硬件故障、软件错误或系统失效等场景。在翻译时，根据上下文，"fails" 可以译为“故障”、“失效”、“失败”或“出错”。例如：

- **系统故障**（System fails）：系统未能正常运行。
- **硬件失效**（Hardware fails）：硬件设备无法正常工作。
- **测试失败**（Test fails）：测试未通过或未达到预期结果。

请根据具体上下文选择合适的翻译。    repeat' sorry
-/

/- `try` 将其参数转换为一个永远不会失败的策略。 -/

theorem all_goals_try_example :
    Even 4 ∧ Even 7 ∧ Even 3 ∧ Even 0 :=
  by
    repeat' apply And.intro
    all_goals try apply Even.add_two
    repeat sorry

/- `any_goals` 将其参数精确地应用于每个目标一次。如果参数在**任意**目标上成功，则它成功。 -/

theorem any_goals_example :
    Even 4 ∧ Even 7 ∧ Even 3 ∧ Even 0 :=
  by
    repeat' apply And.intro
    any_goals apply Even.add_two
    repeat' sorry

/- `solve | ⋯ | ⋯ | ⋯` 类似于 `first`，但它仅在其中一个参数完全证明当前目标时才会成功。 -/

theorem any_goals_solve_repeat_first_example :
    Even 4 ∧ Even 7 ∧ Even 3 ∧ Even 0 :=
  by
    repeat' apply And.intro
    any_goals
      solve
      | repeat'
          first
          | apply Even.add_two
          | apply Even.zero
    repeat' sorry

/- 组合子 `repeat'` 容易导致无限循环： -/

/- -- 循环
定理 repeat'_Not_示例 :
    ¬ 偶数 1 :=
  通过 repeat' 应用 非.引入 -/常见的循环类型包括：

1. **for 循环**：用于在已知迭代次数的情况下执行代码块。
2. **while 循环**：在条件为真时重复执行代码块。
3. **do-while 循环**：与 while 循环类似，但至少会执行一次代码块，然后再检查条件。
4. **foreach 循环**：用于遍历集合或数组中的每个元素。

循环是编程中的基本概念，广泛应用于各种编程语言中。theorem repeat'_Not_example :
    ¬ Even 1 :=
  by repeat' apply Not.intro
-/


/- ## 宏

在编程中，宏（Macro）是一种预定义的代码片段，通常用于简化重复性任务或实现代码复用。宏可以在编译时或运行时展开，具体取决于编程语言和宏的类型。宏的使用可以提高代码的可读性和维护性，但也可能引入潜在的复杂性和调试难度。

### 宏的类型
1. **文本替换宏**：在编译前将宏名称替换为指定的文本。例如，C语言中的`#define`指令。
2. **函数式宏**：类似于函数调用，但会在编译时展开为代码片段。例如，C语言中的带参数的宏。
3. **条件编译宏**：用于根据条件编译不同的代码块。例如，C语言中的`#ifdef`和`#ifndef`指令。

### 宏的优缺点
**优点**：
- 提高代码复用性。
- 减少代码冗余。
- 在某些情况下可以提高性能（例如，内联展开）。

**缺点**：
- 可能导致代码难以调试。
- 容易引入错误，尤其是在复杂的宏定义中。
- 可能降低代码的可读性。

### 使用宏的注意事项
- 确保宏的名称具有描述性，避免与其他代码冲突。
- 避免在宏中使用复杂的逻辑，以降低出错风险。
- 在可能的情况下，优先使用函数或常量替代宏。

通过合理使用宏，开发者可以显著提高代码的效率和可维护性，但同时也需要谨慎处理其潜在的复杂性。 -/

/- 我们从实际的元编程开始，通过编写一个自定义策略作为宏来实现。该策略体现了我们在上面的 `solve` 示例中硬编码的行为： -/

macro "intro_and_even" : tactic =>
  `(tactic|
      (repeat' apply And.intro
       any_goals
         solve
         | repeat'
             first
             | apply Even.add_two
             | apply Even.zero))

/- 让我们应用我们的自定义策略： -/

theorem intro_and_even_example :
    Even 4 ∧ Even 7 ∧ Even 3 ∧ Even 0 :=
  by
    intro_and_even
    repeat' sorry


/- ## 元编程单子

`MetaM` 是底层的元编程单子。`TacticM` 在 `MetaM` 的基础上扩展了目标管理功能。

* `MetaM` 是一个状态单子，提供了对全局上下文（包括所有定义和归纳类型）、符号以及属性（例如，`@[simp]` 定理列表）等的访问。`TacticM` 还额外提供了对目标列表的访问。

* `MetaM` 和 `TacticM` 的行为类似于选项单子。元编程中的 `failure` 会使单子进入错误状态。

* `MetaM` 和 `TacticM` 支持追踪功能，因此我们可以使用 `logInfo` 来显示消息。

* 与其他单子类似，`MetaM` 和 `TacticM` 支持诸如 `for`–`in`、`continue` 和 `return` 等命令式结构。 -/

def traceGoals : TacticM Unit :=
  do
    logInfo m!"Lean version {Lean.versionString}"
    logInfo "All goals:"
    let goals ← getUnsolvedGoals
    logInfo m!"{goals}"
    match goals with
    | []     => return
    | _ :: _ =>
      logInfo "First goal's target:"
      let target ← getMainTarget
      logInfo m!"{target}"

elab "trace_goals" : tactic =>
  traceGoals

theorem Even_18_and_Even_20 (α : Type) (a : α) :
    Even 18 ∧ Even 20 :=
  by
    apply And.intro
    trace_goals
    intro_and_even


/- ## 第一个示例：假设策略

我们定义了一个名为 `hypothesis` 的策略，其行为与预定义的 `assumption` 策略基本相同。 -/

def hypothesis : TacticM Unit :=
  withMainContext
    (do
       let target ← getMainTarget
       let lctx ← getLCtx
       for ldecl in lctx do
         if ! LocalDecl.isImplementationDetail ldecl then
           let eq ← isDefEq (LocalDecl.type ldecl) target
           if eq then
             let goal ← getMainGoal
             MVarId.assign goal (LocalDecl.toExpr ldecl)
             return
       failure)

elab "hypothesis" : tactic =>
  hypothesis

theorem hypothesis_example {α : Type} {p : α → Prop} {a : α}
      (hpa : p a) :
    p a :=
  by hypothesis


/- ## 表达式

元编程框架围绕表达式或术语的类型 `Expr` 展开。 -/

#print Expr


/- ### 名称

我们可以使用反引号创建字面量名称：

* 使用单个反引号的名称，如 `n`，不会检查其是否存在。

* 使用双反引号的名称，如 ``n``，会被解析并检查其存在性。 -/

#check `x
#eval `x
#eval `Even          -- 当然，请提供您需要翻译的技术文档内容，我将确保专业术语的准确性，并将其翻译成中文。#eval `LoVe.Even     -- "suboptimal" 可以翻译为“次优”或“非最优”。在技术文档中，通常用于描述某种方案、配置或结果虽然可行，但并非最佳选择。例如：

- **原文**: The current configuration is suboptimal for high-performance computing.
- **译文**: 当前配置对于高性能计算来说是次优的。

根据具体上下文，也可以使用“非最优”来强调与最佳状态的差距。例如：

- **原文**: The algorithm produces suboptimal results under certain conditions.
- **译文**: 该算法在某些条件下会产生非最优的结果。

请根据具体语境选择合适的翻译。#eval ``Even
/- #eval ``EvenThough   -- 失败 -/ils）

在技术文档中，"fails" 通常指的是系统、设备或软件在运行过程中未能按预期工作或执行其功能的情况。这种情况可能是由于硬件故障、软件错误、配置问题或其他外部因素引起的。故障可能会导致系统停机、数据丢失或性能下降，因此需要及时检测和修复。

在中文技术文档中，"fails" 可以翻译为“故障”或“失效”，具体翻译取决于上下文。例如：

- **系统故障**（System fails）：指系统在运行过程中出现的问题，导致其无法正常工作。
- **硬件故障**（Hardware fails）：指硬件设备由于物理损坏或其他原因无法正常工作。
- **软件故障**（Software fails）：指软件在运行过程中出现的错误或异常，导致其无法按预期执行功能。

保持专业术语的准确性在技术文档翻译中非常重要，以确保信息的准确传达和理解。-/


/- ### 常量 -/

#check Expr.const

#eval ppExpr (Expr.const ``Nat.add [])
#eval ppExpr (Expr.const ``Nat [])


/- ### 排序（第12讲） -/

#check Expr.sort

#eval ppExpr (Expr.sort Level.zero)
#eval ppExpr (Expr.sort (Level.succ Level.zero))


/- ### 自由变量 -/

#check Expr.fvar

#check FVarId.mk `n
#eval ppExpr (Expr.fvar (FVarId.mk `n))


/- ### 元变量

元变量（Metavariables）是指在编程语言、逻辑系统或数学表达式中，用于表示其他变量或表达式的占位符。它们通常用于描述语法规则、模式匹配或抽象语法树（AST）的结构。元变量本身不是具体的值，而是用来代表某一类变量或表达式的通用符号。

例如，在类型系统中，元变量可以用来表示任意类型；在模式匹配中，元变量可以用来匹配任意子表达式。元变量的使用使得规则和模式的描述更加通用和灵活。

在编程语言的设计和实现中，元变量常用于定义语法规则、类型推导规则或代码生成规则。它们帮助开发者和编译器更好地理解和处理复杂的语言结构。 -/

#check Expr.mvar


/- ### 应用领域 -/

#check Expr.app

#eval ppExpr (Expr.app (Expr.const ``Nat.succ [])
  (Expr.const ``Nat.zero []))


/- ### 匿名函数与绑定变量 -/

#check Expr.bvar
#check Expr.lam

#eval ppExpr (Expr.bvar 0)

#eval ppExpr (Expr.lam `x (Expr.const ``Nat []) (Expr.bvar 0)
  BinderInfo.default)

#eval ppExpr (Expr.lam `x (Expr.const ``Nat [])
  (Expr.lam `y (Expr.const ``Nat []) (Expr.bvar 1)
     BinderInfo.default)
  BinderInfo.default)


/- ### 依赖函数类型 -/

#check Expr.forallE

#eval ppExpr (Expr.forallE `n (Expr.const ``Nat [])
  (Expr.app (Expr.const ``Even []) (Expr.bvar 0))
  BinderInfo.default)

#eval ppExpr (Expr.forallE `dummy (Expr.const `Nat [])
  (Expr.const `Bool []) BinderInfo.default)


/- ### 其他构造函数

在编程中，构造函数（Constructor）是一种特殊的方法，用于在创建对象时初始化该对象。除了默认构造函数外，类还可以定义其他构造函数，以便在创建对象时提供不同的初始化选项。这些其他构造函数通常被称为“重载构造函数”或“参数化构造函数”。

#### 重载构造函数
重载构造函数允许类定义多个构造函数，每个构造函数具有不同的参数列表。这样，用户可以根据需要选择不同的构造函数来创建对象。例如：

```java
public class MyClass {
    private int value;

    // 默认构造函数
    public MyClass() {
        this.value = 0;
    }

    // 带一个参数的构造函数
    public MyClass(int value) {
        this.value = value;
    }

    // 带两个参数的构造函数
    public MyClass(int value1, int value2) {
        this.value = value1 + value2;
    }
}
```

在上面的例子中，`MyClass` 类定义了三个构造函数：一个默认构造函数、一个带一个参数的构造函数和一个带两个参数的构造函数。用户可以根据需要选择不同的构造函数来创建 `MyClass` 对象。

#### 参数化构造函数
参数化构造函数是指那些接受一个或多个参数的构造函数。这些参数通常用于初始化对象的成员变量。例如：

```java
public class Person {
    private String name;
    private int age;

    // 参数化构造函数
    public Person(String name, int age) {
        this.name = name;
        this.age = age;
    }
}
```

在这个例子中，`Person` 类定义了一个参数化构造函数，该构造函数接受两个参数：`name` 和 `age`。这些参数用于初始化 `Person` 对象的 `name` 和 `age` 成员变量。

#### 使用其他构造函数的场景
1. **灵活的对象创建**：通过定义多个构造函数，用户可以根据不同的需求选择最合适的构造函数来创建对象。
2. **代码复用**：在某些情况下，一个构造函数可以调用另一个构造函数来复用代码。例如：

```java
public class MyClass {
    private int value;

    // 默认构造函数
    public MyClass() {
        this(0); // 调用带一个参数的构造函数
    }

    // 带一个参数的构造函数
    public MyClass(int value) {
        this.value = value;
    }
}
```

在这个例子中，默认构造函数通过调用带一个参数的构造函数来初始化 `value` 成员变量，从而避免了代码重复。

#### 总结
其他构造函数为类的对象创建提供了更多的灵活性和选择。通过定义多个构造函数，用户可以根据不同的需求选择最合适的构造函数来初始化对象。这不仅提高了代码的可读性和可维护性，还增强了代码的复用性。 -/

#check Expr.letE
#check Expr.lit
#check Expr.mdata
#check Expr.proj


/- ## 第二个示例：一个析取-分解策略

我们定义了一个 `destruct_and` 策略，用于自动化地消除前提中的 `∧`，从而自动化诸如以下的证明： -/

theorem abc_a (a b c : Prop) (h : a ∧ b ∧ c) :
    a :=
  And.left h

theorem abc_b (a b c : Prop) (h : a ∧ b ∧ c) :
    b :=
  And.left (And.right h)

theorem abc_bc (a b c : Prop) (h : a ∧ b ∧ c) :
    b ∧ c :=
  And.right h

theorem abc_c (a b c : Prop) (h : a ∧ b ∧ c) :
    c :=
  And.right (And.right h)

/- 我们的策略依赖于一个辅助函数，该函数以假设 `h` 作为参数，并将其用作表达式： -/

partial def destructAndExpr (hP : Expr) : TacticM Bool :=
  withMainContext
    (do
       let target ← getMainTarget
       let P ← inferType hP
       let eq ← isDefEq P target
       if eq then
         let goal ← getMainGoal
         MVarId.assign goal hP
         return true
       else
         match Expr.and? P with
         | Option.none        => return false
         | Option.some (Q, R) =>
           let hQ ← mkAppM ``And.left #[hP]
           let success ← destructAndExpr hQ
           if success then
             return true
           else
             let hR ← mkAppM ``And.right #[hP]
             destructAndExpr hR)

#check Expr.and?

def destructAnd (name : Name) : TacticM Unit :=
  withMainContext
    (do
       let h ← getFVarFromUserName name
       let success ← destructAndExpr h
       if ! success then
         failure)

elab "destruct_and" h:ident : tactic =>
  destructAnd (getId h)

/- 让我们验证一下我们的策略是否有效： -/

theorem abc_a_again (a b c : Prop) (h : a ∧ b ∧ c) :
    a :=
  by destruct_and h

theorem abc_b_again (a b c : Prop) (h : a ∧ b ∧ c) :
    b :=
  by destruct_and h

theorem abc_bc_again (a b c : Prop) (h : a ∧ b ∧ c) :
    b ∧ c :=
  by destruct_and h

theorem abc_c_again (a b c : Prop) (h : a ∧ b ∧ c) :
    c :=
  by destruct_and h

/- 定理 abc_ac (a b c : 命题) (h : a ∧ b ∧ c) :
    a ∧ c :=
  通过 分解合取 h   -- 失败 -/（故障）

在技术文档中，"fails" 通常指系统、设备或软件在运行过程中出现的故障或失效情况。它可以指硬件故障、软件错误、系统崩溃或其他导致功能无法正常执行的问题。在中文技术文档中，通常会根据上下文将其翻译为“故障”、“失效”或“失败”。

例如：
- **原文**: The system fails to start due to a hardware issue.
- **译文**: 由于硬件问题，系统无法启动。

- **原文**: If the connection fails, retry after 5 seconds.
- **译文**: 如果连接失败，请在5秒后重试。

根据具体语境，"fails" 也可以翻译为“出错”、“中断”等，但需确保术语的准确性和一致性。-/


/- ## 第三个示例：直接证明查找器

最后，我们实现了一个名为 `prove_direct` 的工具，该工具会遍历数据库中的所有定理，并检查是否可以使用其中的某个定理来证明当前的目标。 -/

def isTheorem : ConstantInfo → Bool
  | ConstantInfo.axiomInfo _ => true
  | ConstantInfo.thmInfo _   => true
  | _                        => false

def applyConstant (name : Name) : TacticM Unit :=
  do
    let cst ← mkConstWithFreshMVarLevels name
    liftMetaTactic (fun goal ↦ MVarId.apply goal cst)

def andThenOnSubgoals (tac₁ tac₂ : TacticM Unit) :
  TacticM Unit :=
  do
    let origGoals ← getGoals
    let mainGoal ← getMainGoal
    setGoals [mainGoal]
    tac₁
    let subgoals₁ ← getUnsolvedGoals
    let mut newGoals := []
    for subgoal in subgoals₁ do
      let assigned ← MVarId.isAssigned subgoal
      if ! assigned then
        setGoals [subgoal]
        tac₂
        let subgoals₂ ← getUnsolvedGoals
        newGoals := newGoals ++ subgoals₂
    setGoals (newGoals ++ List.tail origGoals)

def proveUsingTheorem (name : Name) : TacticM Unit :=
  andThenOnSubgoals (applyConstant name) hypothesis

def proveDirect : TacticM Unit :=
  do
    let origGoals ← getUnsolvedGoals
    let goal ← getMainGoal
    setGoals [goal]
    let env ← getEnv
    for (name, info)
        in SMap.toList (Environment.constants env) do
      if isTheorem info && ! ConstantInfo.isUnsafe info then
        try
          proveUsingTheorem name
          logInfo m!"Proved directly by {name}"
          setGoals (List.tail origGoals)
          return
        catch _ =>
          continue
    failure

elab "prove_direct" : tactic =>
  proveDirect

/- 让我们验证一下我们的策略是否有效： -/

theorem Nat.symm (x y : ℕ) (h : x = y) :
    y = x :=
  by prove_direct

theorem Nat.symm_manual (x y : ℕ) (h : x = y) :
    y = x :=
  by
    apply symm
    hypothesis

theorem Nat.trans (x y z : ℕ) (hxy : x = y) (hyz : y = z) :
    x = z :=
  by prove_direct

theorem List.reverse_twice (xs : List ℕ) :
    List.reverse (List.reverse xs) = xs :=
  by prove_direct

/- Lean 拥有 `apply?` 功能： -/

theorem List.reverse_twice_apply? (xs : List ℕ) :
    List.reverse (List.reverse xs) = xs :=
  by apply?

end LoVe
