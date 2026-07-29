# P0054 G4.2 隔离兼容 Referee B 审稿报告

最终 verdict：`ACCEPT`

## 一、审查范围、隔离与输入完整性

专用 Referee B launcher 在读取材料前因固定模型不可用而失败；本报告由兼容
Referee B 在相同只读证明边界下完成。数学审查全程离线，未读取 G4.2 Referee
A、任何 G4.2 Prover/Experimentalist 报告或其源代码/结果文件，未运行 Lean、
Formalizer、SAT/SMT solver，也未把有限搜索当作证明。

起始 `HEAD`：

```text
d2c8e3eb81466a3743c736319ef1874920590abc
```

候选证明在任何实质材料审查前通过受保护哈希门：

```text
EXPECTED_SHA256: ef87bce75e3db5a8a46d99318c6b4c5e8bc769f33ef61be4e6adee55372c5a1e
ACTUAL_SHA256:   ef87bce75e3db5a8a46d99318c6b4c5e8bc769f33ef61be4e6adee55372c5a1e
RESULT: MATCH
```

实质证明输入及 SHA-256：

| 文件 | SHA-256 |
|---|---|
| `AGENTS.md` | `5ec4fe8a019a5c52efe2a382989d58782abfc6242240f77f9a0f5f8a7a39f4c1` |
| `Problems/P0054/statement.md` | `c09275667570ef827939625d7e82560ad8eeb5a448efca3ba251af3208d57990` |
| `Problems/P0054/status.md` | `bc8e3a16b9b14d54200ce95b90c34e77b2c6611e181c3828888d6f0b3f4d0d70` |
| `Problems/P0054/claims.yaml` | `92fd910d59d6f2cd4a4f0b0fd526a77e24a080ed09a288ab676efeb627128564` |
| `Problems/P0054/proof/g4-global-lower/candidate-proof.md` | `9e0821e821458ee390d809d03e5fd927ae661222b4712c2c679b02a26d6ed448` |
| `Problems/P0054/proof/audits/g4-global-lower/referee-a.md` | `0996bc5bd64941554f3b0e6d36f3d29ffc36a5c1c32e203802092dc81c6acba4` |
| `Problems/P0054/proof/audits/g4-global-lower/referee-b.md` | `b1a40729e21ce51e52739cd5e06cb4417fb7cb399cb43edeffbfdc142852b57a` |
| `Problems/P0054/proof/g4.2-stronger-lower/candidate-proof.md` | `ef87bce75e3db5a8a46d99318c6b4c5e8bc769f33ef61be4e6adee55372c5a1e` |
| `Problems/P0054/experiments/g4.2-stronger-lower/section0-freeze.md` | `6551eda020048d809f5cd9f8d85908cc821a1adc2c9d8c026960354533d9d5d4` |

除本报告外，没有修改 candidate、`status.md`、`claims.yaml` 或任何旧文件。

## 二、冻结依赖与目标量词

本审查把已由两份冻结 G4 Referee 接受的 P0054-C17 框架作为输入，而不重新扩张
其文献包：在 eventual stable 区间内选取充分大的有限底集 `X`，再选 endpoint-
normal 的最小 saturated 7-Sperner family `F`。P0054-C7 的已证上界 55 只用于
保证 `|X|>2^55>=2^|F|`，从而取得 homogeneous all-or-none block `H`；它不使用
待证下界，故没有循环。

冻结 G4 结论给出不交且耗尽 `F` 的七个 saturated-antichain canonical layers：

```text
|A0|=1, |A1|>=6, |A2|>=7, |A3|>=9,
|A4|>=7, |A5|>=6, |A6|=1.
```

令 `U=X\H`。对内部层，small 成员 `S` 与 large trace `K` 满足

\[
|S|\ge i,\qquad |U\setminus K|\ge6-i,
\]

并且对每个 `R\subseteq U` 有精确 oriented cover

\[
\sum_S 1[S\subseteq R]+\sum_K1[R\subseteq K]\ge1. \tag{1}
\]

这组量词是“任意有限 `U`、每个 `R\subseteq U`”，不是固定 core 枚举。证明只需
`H` 是继承的 all-or-none block 和每层自身饱和，不偷用 `H` 在每层仍为极大
atom。

目标是分别把 `A_2,A_4` 的冻结下界 7 提升为 8，然后与其余冻结层界求和；并非
证明所有有限 `n` 上的同一不等式，也不是固定模板类结论。

## 三、七成员 `A_2` 的精确概率分类

反设 `|A_2|=7`。记 small 侧数量为 `a`，large-complement 族
`C_j=U\setminus K_j` 的数量为 `b`。则

\[
a+b=7,\qquad |S_i|\ge2,\quad |C_j|\ge4. \tag{2}
\]

将 `R` 按 Bernoulli(`p`) 生成，对 (1) 取期望，严格得到

\[
1\le\sum_i p^{|S_i|}+\sum_j(1-p)^{|C_j|}
 \le ap^2+b(1-p)^4. \tag{3}
\]

方向正确：因为 `0<p<1`，实际集合更大只会减小事件概率上界。事件允许重叠；
这里只用期望线性性，不假设事件互斥。

逐项重算八种整数 split：

| `(a,b)` | 精确反证值 |
|---|---|
| `(0,7)` | `p=1/2`: `7/16<1` |
| `(1,6)` | `p=1/2`: `10/16<1` |
| `(2,5)` | `p=1/2`: `13/16<1` |
| `(3,4)` | `p=2/5`: `624/625<1` |
| `(5,2)` | `p=1/3`: `77/81<1` |
| `(6,1)` | `p=1/3`: `70/81<1` |
| `(7,0)` | `p=1/3`: `63/81<1` |

唯一未被 count-only 不等式排除的是 `(a,b)=(4,3)`。候选对该 split 的“确实
存活”核查也正确。令 `q=1-p,r=5/8`，恒等式

\[
q^4-4r^3q+3r^4=(q-r)^2((q+r)^2+2r^2)\ge0
\]

给出

\[
4p^2+3(1-p)^4
\ge1+4\left(p-\frac{375}{1024}\right)^2
  +\frac{5231}{262144}>1.
\]

因此概率步骤没有错误地宣称 `(4,3)` 不存在；它只把结构证明需要处理的残余
split 精确隔离出来。

## 四、blocker 识别与残余 split 排除

写

\[
\mathcal S=\{S_1,S_2,S_3,S_4\},\qquad
\mathcal C=\{C_1,C_2,C_3\}.
\]

层的 cross-antichain 条件为 `S_i\nsubseteq K_j`，等价于
`S_i\cap C_j\ne\varnothing`。所以每个 `S_i` 是 `\mathcal C` 的 transversal，
每个 `C_j` 是 `\mathcal S` 的 transversal。

对任意 `\mathcal C` 的 transversal `R`，不存在 `R\subseteq K_j`，故 (1) 强制
某个 `S_i\subseteq R`。结合 small 侧为 antichain，blocker recognition lemma
给出

\[
\mathcal S=B(\mathcal C). \tag{4}
\]

反向地，对任意 `\mathcal S` 的 transversal `D`，在 (1) 取
`R=U\setminus D`。此时不存在 `S_i\subseteq R`，所以某个
`R\subseteq K_j`，等价于 `C_j\subseteq D`。large traces 的 antichain 经互补
后仍为 antichain，故

\[
\mathcal C=B(\mathcal S). \tag{5}
\]

两次 recognition 都检查了 minimality：若 blocker 候选的真子集仍为
transversal，containment 性会在同侧 antichain 中产生严格包含；反之极小
transversal 包含候选成员后只能与其相等。

由 (5) 和 `|C_j|>=4`，`\mathcal S` 的每个 transversal 都至少有四点：有限 `U`
保证任意 transversal 含一个 inclusion-minimal transversal，而后者必是某个
`C_j`。

若某点同时属于两个 `S_i`，再从另两个非空 `S_i` 各取一点，就得到至多三点的
transversal，矛盾。因此四个 `S_i` 两两不交。每次从四个 `S_i` 各取一点所成
四点集都是 inclusion-minimal transversal；不同选择可由它与四个互不交
`S_i` 的交恢复，故确实是不同集合。于是

\[
|B(\mathcal S)|\ge\prod_{i=1}^4|S_i|\ge2^4=16.
\]

这与 (5) 的 `|B(\mathcal S)|=|\mathcal C|=3` 矛盾。残余 `(4,3)` 被任意有限
`U` 上的结构论证排除，因此 `|A_2|>=8`。

## 五、A4 变换的独立核查

对 `A_4`，原接口满足 small `S` 有 `|S|>=4`，large complement
`C=U\setminus K` 有 `|C|>=2`。令 `R'=U\setminus R`，构造辅助接口：

```text
new small generators: C=U\K
new large traces:     U\S
```

则 new small 大小至少 2，new large trace 的补集恰为 `S`，大小至少 4；并且

\[
S\subseteq R\iff R'\subseteq U\setminus S,
\qquad
R\subseteq K\iff U\setminus K\subseteq R'.
\]

所以 (1) 对所有 `R` 成立，当且仅当变换后 `A_2` 型 cover 对所有 `R'` 成立。
同侧互补反转包含关系，故 antichain 保持；cross 条件在两边都等价于
`S\cap(U\setminus K)\ne\varnothing`。变换保持成员总数，并且做两次恢复原接口。

这只是对局部接口的逐项 involution，不声称原 `A_4` 是某个 `A_2` 的族级补集，
也不假设 `F` 具有 complement symmetry。因此同一个局部定理合法给出
`|A_4|>=8`。

## 六、主动边界、反例与量词攻击

- **任意大有限 `U`**：blocker 论证只用有限性来抽取极小 transversal；没有
  `|U|` 上界、稳定后的有限核假设或有限搜索外推。
- **`U` 为空或很小**：若 `|U|<4`，不存在满足 (2) 的 large complement；取
  `R=empty` 时也没有大小至少 2 的 small generator 可覆盖。若 `|U|=4`，唯一
  可能的四点 complement 是 `U`；对任意单点 `R`，large down-event 失败且
  small up-event不可能。故小 `U` 不产生漏掉的七成员例。
- **空侧**：large 侧为空时 `R=empty` 无法覆盖；small 侧为空时 `R=U` 无法
  覆盖。概率表也分别包含 `(7,0)` 与 `(0,7)`。
- **`R=empty,U`**：均在 universal cover 的量词中；投影事件使用非严格包含，
  而原底集上的可比因测试集只取 `H` 的真非空部分而仍为严格。
- **重复 incidence**：点可具有重复 incidence pattern，证明未假设 pattern
  唯一。两两不交结论只禁止一个点落入两个 small 集；每个实际选点四元组仍
  对应不同的四点 transversal。
- **重复成员、可比成员**：集合族不是 multiset，完全重复成员不会产生额外
  计数；同侧严格包含由 antichain 排除。互补后不可比性保持。
- **非均匀与严格大小**：`|S_i|>2` 或 `|C_j|>4` 只降低 (3) 的概率项；残余
  blocker 论证只使用下界，且更大的 `S_i` 只提高乘积下界。
- **blocker minimality**：两侧 recognition 均先证明每个列出的成员极小，再
  证明任意极小 transversal 必与一个列出成员相等；没有把普通 transversal
  误当 blocker 成员。
- **transversal 计数**：计数的是 actual subsets of `U`，不是 incidence
  quotient 或带重数元组；两两不交使选择到集合的映射单射且所得 transversal
  逐点极小。
- **概率方向**：所有概率上界方向均由 `0<p<1` 和指数下界产生；没有从
  `E[Z]>=1` 错推事件互斥，也没有浮点比较。
- **双对偶**：`S -> U\S -> S`、`K -> U\K -> K`，cover 的两个方向交换两次
  后复原；没有量词丢失。
- **eventual 量词**：先取一个位于稳定区间且足够大的有限 `n`，再对其最小族
  证明 39；因 `sat(n,7)=sat(7)`，这足以证明 eventual value 的下界，不需要
  对稳定区间外的所有 `n` 断言。
- **有限 solver**：候选中关于其他角色有限计算的段落未被本审查验证或依赖；
  即使全部删除，Sections 2--7 的证明仍依赖闭合。

未找到最小反例。若存在七成员反例，概率分类强迫它首先具有 `(4,3)` split；
这是所有可能反例的第一必要形态，而上述 16-versus-3 blocker 矛盾在该形态的
第一处结构步骤即将其排除。

## 七、依赖闭包与 39 求和

依赖链为：

```text
P0054-C7 (sat(7)<=55)
  -> sufficiently large stable minimum family has H
  -> accepted P0054-C17 canonical framework and layer bounds
  -> A2 local equality exclusion gives |A2|>=8
  -> complemented local interface gives |A4|>=8
  -> disjoint seven-layer sum.
```

P0054-C7 只服务于 atom 阈值；P0054-C17 已由两份冻结 G4 Referee 接受。新下界
不反过来证明任何输入，故依赖无环。求和逐项为

\[
|F|\ge1+6+8+9+8+6+1=39.
\]

所选 `F` 满足 `|F|=sat(n,7)=sat(7)`，所以候选结论确为

\[
sat(7)\ge39.
\]

当前 `claims.yaml` 只到 P0054-C17、`status.md` 仍记录 G4 接受状态；候选明确要求
两份 G4.2 Referee 都接受后才可创建 P0054-C18，因此这不是 statement mismatch。
本 verdict 不授权更新它们，也不支持 exact value、novelty、priority、publication、
release、commit 或 push。

## 八、结论与操作声明

候选证明中的第一失效步骤：`NONE`。

```text
ROLE: P0054_G4_2_REFEREE_B_COMPAT
VERDICT: ACCEPT
FIRST_INVALID_STEP: NONE
MINIMAL_COUNTEREXAMPLE: NONE
UNRESOLVED_MATHEMATICAL_DEPENDENCIES: NONE
CANDIDATE_SHA256_MATCH: YES
NETWORK_USED: NO
G4_2_REFEREE_A_READ: NO
G4_2_PROVER_REPORTS_READ: NO
G4_2_EXPERIMENTALIST_REPORT_READ: NO
FINITE_SOLVER_USED_AS_PROOF: NO
FORMALIZATION_PERFORMED: NO
LEAN_RUN: NO
CANDIDATE_STATUS_CLAIMS_OLD_FILES_MODIFIED: NO
FILES_WRITTEN: Problems/P0054/proof/audits/g4.2-stronger-lower/referee-b.md
REPAIR_EDIT_PERFORMED: NO
PUBLICATION_COMMIT_PUSH_PERFORMED: NO
```

最终 verdict：`ACCEPT`
