# P0054 G4.2 隔离兼容 Referee A 审稿报告

最终 verdict：`ACCEPT`

## 1. 隔离范围与冻结输入

`COMPUTED`：审查开始时的 `HEAD` 为
`d2c8e3eb81466a3743c736319ef1874920590abc`。目标报告原先不存在。

`COMPUTED`：指定候选的 SHA-256 已在读取证明内容前核验为

```text
ef87bce75e3db5a8a46d99318c6b4c5e8bc769f33ef61be4e6adee55372c5a1e
```

与门控要求精确一致。实质读取的旧证明输入及哈希如下：

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

未打开或依赖任何 G4.2 Prover/Experimentalist 报告，也未读取 G4.2
Referee B。候选文件中对这些隔离路线的摘要不作为本审查的证明依赖。

## 2. 全局稳定最小族与 canonical decomposition

`PROVED`：从冻结 G4 依赖重新构造如下。取稳定区间内满足
`n>2^55` 的有限底集 `X`，并取一个含 `empty,X` 的最小基数饱和
7-Sperner 族 `F`。既有全局上界 P0054-C7 给出

```text
|F|=sat(n,7)=sat(7)<=55,
```

故 `|X|>2^55>=2^|F|`，冻结 homogeneous-atom 定理强制产生一个
`|H|>=2` 的 all-or-none block。这里使用的是既有上界 55，而不是待证下界
39，因此不存在循环。令 `U=X\H`。

`PROVED`：`F` 是 `2^X` 的真子族。对任意遗漏集合应用饱和性，从所得八元链
删除该遗漏集合，得到 `F` 中的七元严格链；7-Sperner 性排除八元严格链，故
`F` 的高度恰为七。逐次删除极小元的 canonical decomposition 因而是

```text
F=A_0 disjoint-union A_1 disjoint-union ... disjoint-union A_6,
```

七层均非空、两两不交并耗尽 `F`。冻结层定理给出每个 `A_i` 都是整个
`2^X` 中的饱和反链。同一 `H` 在每层仍为 all-or-none block；证明不要求
它在单层内仍是极大 atom。

`PROVED`：端点正规化给出 `A_0={empty}` 和 `A_6={X}`。Canonical level
给每个非首层成员一个前一层严格前驱；对非末层成员，下一层的饱和反链先给出
一个严格可比成员，若方向向下，则再取其 canonical 前驱会在当前反链中产生
严格可比的两个成员，矛盾。因此每个非末层成员都有下一层严格后继。

`PROVED`：称对 `H` 全不含的成员为 small，将全含成员写成 `K union H`。
沿前驱链和后继链分别得到

```text
small S in A_i       => |S|>=i,
large K union H in A_i => |U\K|>=6-i.
```

取固定 `empty != Q proper-subset H`，对每个 `R subseteq U` 测试
`T_R=R union Q`。它不属于任何层，而层饱和性强制存在可比成员；方向检查给出

```text
sum_small 1[S subseteq R] + sum_large 1[R subseteq K] >= 1       (1)
```

对所有 `R subseteq U` 成立。层反链还给出 small、large trace 各自为反链，
以及每个 cross pair 满足 `S not-subseteq K`。

## 3. `A_2` 七成员情形的精确有理分类

`PROVED`：假设 `|A_2|=7`。令 small 数为 `a`，large 数为 `b`，并对
large trace 写 `C_j=U\K_j`。则

```text
a+b=7,  |S_i|>=2,  |C_j|>=4.
```

让 `R` 按 Bernoulli(`p`) 生成。由 (1) 和线性期望，对每个有理
`0<p<1` 有

```text
1 <= sum_i p^|S_i| + sum_j (1-p)^|C_j|
  <= a p^2 + b(1-p)^4.                                      (2)
```

下列七种分拆均由精确有理数排除：

| `(a,b)` | `p` | (2) 的右端上界 |
|---|---:|---:|
| `(0,7)` | `1/2` | `7/16<1` |
| `(1,6)` | `1/2` | `10/16<1` |
| `(2,5)` | `1/2` | `13/16<1` |
| `(3,4)` | `2/5` | `624/625<1` |
| `(5,2)` | `1/3` | `77/81<1` |
| `(6,1)` | `1/3` | `70/81<1` |
| `(7,0)` | `1/3` | `63/81<1` |

`PROVED`：唯一未被纯计数排除的是 `(a,b)=(4,3)`，而且这不是固定某个
`p` 漏检的结果。令 `q=1-p`、`r=5/8`，则

```text
q^4-4r^3 q+3r^4
  =(q-r)^2((q+r)^2+2r^2)>=0.
```

所以

```text
4p^2+3(1-p)^4
 >= 4p^2+12r^3(1-p)-9r^4
  = 1+4(p-375/1024)^2+5231/262144
  > 1.
```

因此 `(4,3)` 对全部 `0<p<1` 确实通过 count-only 必要条件，但这不构成
存在性结论。实际生成元或补集更大只会减小 (2) 中的事件概率，不能挽救已被
上述见证排除的分拆。

## 4. 双方 blocker recognition

`PROVED`：设 surviving split 的四个 small 集组成 `mathcal S`，三个
large complement 组成 `mathcal C`。Cross 条件
`S not-subseteq K=U\C` 等价于 `S intersect C` 非空，所以每个
`S` 都横截 `mathcal C`，每个 `C` 都横截 `mathcal S`。

`PROVED`：若 `R` 是 `mathcal C` 的任意 transversal，则它不包含于任何
`K_j`；(1) 强制某个 `S_i subseteq R`。由于 `mathcal S` 是反链，这正是
blocker recognition 的两个条件，故

```text
mathcal S = B(mathcal C).                                    (3)
```

`PROVED`：若 `D` 是 `mathcal S` 的任意 transversal，对
`R=U\D` 应用 (1)。没有 `S_i subseteq R`，所以某个
`R subseteq K_j`，等价于 `C_j subseteq D`。`mathcal C` 是 large traces
之补集所成的反链，故同一 recognition 引理给出

```text
mathcal C = B(mathcal S).                                    (4)
```

两次识别都量化任意有限 `U` 上的全部 transversal，并非有限 atom-pattern
枚举。

## 5. 不交性与 `16` 个 blocker

`PROVED`：由 (4)，任意 `mathcal S`-transversal 都包含一个 inclusion-
minimal transversal，而后者是某个 `C_j`，其大小至少四。因此
`mathcal S` 的横截数至少为四。

`PROVED`：四个 `S_i` 两两不交。否则若一点同时属于某两个 `S_i`，再从另外
两个非空 `S_i` 各取一点，就得到一个至多三点的 transversal，矛盾。于是从
每个 `S_i` 各取一点所成的四点集都是极小 transversal：删去来自 `S_i` 的点
后恰好漏掉 `S_i`。两两不交还保证不同选择产生不同集合，故

```text
|B(mathcal S)| >= product_i |S_i| >= 2^4 = 16.               (5)
```

但 (4) 又给出 `|B(mathcal S)|=|mathcal C|=3`，矛盾。故七成员的最后一种
分拆也不存在。结合冻结的 `|A_2|>=7`，得到

```text
|A_2|>=8.                                                    (6)
```

同样地，若从局部接口直接覆盖“至多六成员”的边界，取 `p=2/5`，每个事件
概率至多 `4/25`，总和至多 `24/25<1`；故局部定理对所有小于八的基数完整。

## 6. `A_4` 补集与 side swap

`PROVED`：在 `A_4` 接口中，small generator 满足 `|S|>=4`，large
complement `C=U\K` 满足 `|C|>=2`。对 `R'=U\R` 定义变换后接口

```text
new small generators: C=U\K,
new large traces:     U\S.
```

新 small 大小至少二，新 large trace 的补集大小至少四。原 large-trace
反链经补集成为新 small 反链，原 small 反链经补集成为新 large-trace
反链；cross 条件等价保持。并且

```text
S subseteq R  iff R' subseteq U\S,
R subseteq K  iff U\K subseteq R'.
```

因此原覆盖的两个 side 恰好交换为对所有 `R' subseteq U` 的 `A_2` 覆盖。
应用已经证明的局部定理，得到

```text
|A_4|>=8.                                                    (7)
```

这是任意有限 `U` 上的直接变换，不是对某个候选族预设补集对称。

## 7. 层和、依赖与 statement audit

`PROVED`：冻结 G4 其余层界与 (6)--(7) 给出

```text
|F| >= 1+6+8+9+8+6+1 = 39.
```

所选 `n` 在稳定区间且 `F` 为最小族，所以

```text
sat(7)=sat(n,7)=|F|>=39.
```

这是 eventual stable saturation number 的全局下界，不是固定 core、固定
`q=|U|`、G0--G3 模板类或有限 SMT 类的下界。

`PROVED`：依赖链为

```text
P0054-C7 / 冻结文献
  -> 冻结 P0054-C17 全局 canonical framework
  -> 任意 U 的 A_2 equality exclusion
  -> 直接 A_4 dual interface
  -> layer sum 39.
```

P0054-C7 仅用于 homogeneous-atom 阈值；待证 39 未反向用于建立任何前提，
没有循环依赖。`status.md` 与 `claims.yaml` 当前只记录到已接受的 P0054-C17，
而候选明确要求两份 G4.2 Referee 均 `ACCEPT` 后才可创建 P0054-C18；因此当前
元数据是门控中的预期状态，不是 statement mismatch。

`PROVED`：候选的解析证明没有依赖 Section 9 的有限 `q=0,...,10` 搜索、
UNSAT 结果、语义 validator 或 incidence-pattern quotient。它们保持
`COMPUTED`，未被升级为证明。证明也没有从某个固定 `q` 外推到任意 `U`。

## 8. 边界审计

- `PROVED`：`|H|=2` 仍有非空真子集 `Q`，oriented cover 完整。
- `PROVED`：`U` 只要求有限，不设大小上界；所有 `R subseteq U`，包括
  `empty`、`U` 和成员自身 trace，均在覆盖量词内。
- `PROVED`：`a=0` 或 `b=0` 已由七分拆表精确覆盖；小于七成员由
  `p=2/5` 直接覆盖。
- `PROVED`：非均匀 generator/complement 大小及严格大于下界的情形均被
  概率上界和 blocker 证明允许。
- `PROVED`：`S_i` 和 `C_j` 在 surviving split 中都非空；选择点步骤没有
  空集漏洞。
- `PROVED`：同侧反链在两次 blocker recognition 中明确使用；cross 条件
  只转换为双方横截，不暗含更强的不交条件。
- `PROVED`：四个 small 集的不交性来自 transversal number 至少四；不同
  单点选择的可区分性来自两两不交，不把 multiset 或重复成员计入 16。
- `PROVED`：A4 变换同时保留大小、同侧反链、cross 条件、全称覆盖和总成员
  数，未漏换事件方向。
- `PROVED`：所有数值步骤均为精确整数或有理数；没有浮点、极限、除以变量、
  紧致性、Formalizer 或不可核验计算。

## 9. 第一失效/不确定步骤与操作声明

```text
FIRST_INVALID_STEP: NONE
FIRST_UNCERTAIN_MATHEMATICAL_STEP: NONE_WITHIN_FROZEN_DEPENDENCIES
UNRESOLVED_MATHEMATICAL_DEPENDENCIES: NONE
STATEMENT_MISMATCH: NO
COUNTEREXAMPLE_FOUND: NO

ROLE: P0054_G4_2_REFEREE_A_COMPAT
NETWORK_USED: NO
G4_2_REFEREE_B_READ: NO
G4_2_PROVER_OR_EXPERIMENTALIST_REPORT_FILES_OPENED: NO
G4_2_PROVER_OR_EXPERIMENTALIST_CONCLUSIONS_RELIED_ON: NO
FROZEN_G4_REFEREE_REPORTS_READ: YES_AS_AUTHORIZED_INPUT
FINITE_COMPUTATION_USED_AS_PROOF: NO
FORMALIZATION_PERFORMED: NO
LEAN_RUN: NO
CANDIDATE_STATUS_CLAIMS_OLD_FILES_MODIFIED: NO
FILES_WRITTEN: Problems/P0054/proof/audits/g4.2-stronger-lower/referee-a.md ONLY
REPAIR_EDIT_PERFORMED: NO
```

最终 verdict：`ACCEPT`
