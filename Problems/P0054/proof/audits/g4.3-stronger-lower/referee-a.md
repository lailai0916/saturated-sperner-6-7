# P0054 G4.3 隔离兼容 Referee A 审稿报告

最终 verdict：`ACCEPT`

## 1. 隔离范围与输入完整性

`COMPUTED`：审查全程离线、只读；未读取任何 G4.3 Prover/Experimentalist 输出或 G4.3 Referee B，未运行 Formalizer、Lean、SAT/SMT solver，也未写入任何文件。

所有指定输入均在实质阅读前通过 SHA-256 门，并在审查结束时再次核验为相同字节：

| 文件 | SHA-256 |
|---|---|
| `AGENTS.md` | `5ec4fe8a019a5c52efe2a382989d58782abfc6242240f77f9a0f5f8a7a39f4c1` |
| `Problems/P0054/experiments/g4.3-stronger-lower/section0-freeze.md` | `759e7b6a2bbad8853f2baa7424c8b19ac06e6ecaf07b3c3758a30d57a9a99aaf` |
| `Problems/P0054/proof/g4.3-stronger-lower/frozen-subproblem.md` | `cc64e1e376196355b68266abcfdf228d38836b6fc05c170204397efc67a8ddaa` |
| `Problems/P0054/proof/g4.3-stronger-lower/candidate-proof.md` | `ff1271a9552f5eaf82f6d44ac19edfa0e5f550d383d2157e0d16b0eac591a684` |
| `Problems/P0054/proof/g4-global-lower/candidate-proof.md` | `9e0821e821458ee390d809d03e5fd927ae661222b4712c2c679b02a26d6ed448` |
| `Problems/P0054/proof/audits/g4-global-lower/referee-a.md` | `0996bc5bd64941554f3b0e6d36f3d29ffc36a5c1c32e203802092dc81c6acba4` |
| `Problems/P0054/proof/audits/g4-global-lower/referee-b.md` | `b1a40729e21ce51e52739cd5e06cb4417fb7cb399cb43edeffbfdc142852b57a` |
| `Problems/P0054/proof/g4.2-stronger-lower/candidate-proof.md` | `ef87bce75e3db5a8a46d99318c6b4c5e8bc769f33ef61be4e6adee55372c5a1e` |
| `Problems/P0054/proof/audits/g4.2-stronger-lower/referee-a.md` | `664bdb20b8b9c86fac80a2d2fac654b4b91e95eed2d50512534ea45c88d627a0` |
| `Problems/P0054/proof/audits/g4.2-stronger-lower/referee-b.md` | `5a4866c494d123f6478b2164a314749e5b66f2b92f1ec80db4fb52fca5f79bfc` |

候选所证明的局部陈述与冻结子问题一致：

```text
对任意有限 U，若 (mathcal S,mathcal C) 是 admissible (2,4) blocker pair，
则 |mathcal S|+|mathcal C|>=9。
```

其全局应用是 eventual stable 参数 `sat(7)>=41`，不是固定 core 或有限模板类结论。未发现 statement mismatch。

## 2. 空侧、private witness 与数量下界

`PROVED`：双方均非空。若 `mathcal C=empty family`，则

```text
mathcal S=B(mathcal C)={empty set},
```

违反每个 `S` 大小至少二；反向同理违反每个 `C` 大小至少四。

`PROVED`（private-witness lemma）：若 `T in B(mathcal H)` 且 `x in T`，则 `T\{x}` 不是 transversal，故存在 `E_x in mathcal H` 与 `T\{x}` 不交。由于 `T` 本身横截 `E_x`，必有

```text
T intersect E_x={x}.
```

若 `x!=y` 而 `E_x=E_y`，同一个交集将同时等于 `{x}` 与 `{y}`，矛盾。因此 `x -> E_x` 单射并给出

```text
|T|<=|mathcal H|.
```

`T=empty set` 时结论为真空成立，没有边界例外。

令

```text
a=|mathcal S|,  b=|mathcal C|.
```

任取 `C in mathcal C=B(mathcal S)`，有

```text
4<=|C|<=a,
```

故 `a>=4`。任取 `S in mathcal S=B(mathcal C)`，有

```text
2<=|S|<=b,
```

故 `b>=2`。于是 `a+b=8` 只剩

```text
(4,4), (5,3), (6,2).
```

## 3. 排除 `(a,b)=(6,2)`

写 `mathcal C={C_1,C_2}`。

`PROVED`：`C_1` 与 `C_2` 不交。若 `x` 同时属于二者，则 `{x}` 是 inclusion-minimal transversal，因而属于 `B(mathcal C)=mathcal S`，违反 `|S|>=2`。

二者不交后，每个

```text
{x,y},  x in C_1, y in C_2
```

都是 inclusion-minimal transversal。不同选择因不交性产生不同二元集合。因此

```text
a=|B(mathcal C)|
 >=|C_1||C_2|
 >=4*4
 =16,
```

与 `a=6` 矛盾。

## 4. 三集合 blocker 下界的独立重建

设

```text
mathcal C={C_1,C_2,C_3},  |C_i|>=4,
```

且 `B(mathcal C)` 无 singleton。

`PROVED`：三重交为空，否则三重交中的一点本身就是 singleton minimal transversal。

除去与 `C_1 union C_2 union C_3` 不交、因而不可能出现在极小 transversal 中的点，恰有六种 incidence pattern：

| incidence support | 类 | 记号 |
|---|---|---:|
| `{1}` | `C_1\(C_2 union C_3)` | `A_1`, `alpha_1` |
| `{2}` | `C_2\(C_1 union C_3)` | `A_2`, `alpha_2` |
| `{3}` | `C_3\(C_1 union C_2)` | `A_3`, `alpha_3` |
| `{2,3}` | `(C_2 intersect C_3)\C_1` | `P_1`, `pi_1` |
| `{1,3}` | `(C_1 intersect C_3)\C_2` | `P_2`, `pi_2` |
| `{1,2}` | `(C_1 intersect C_2)\C_3` | `P_3`, `pi_3` |

其中

```text
|C_i|=alpha_i+pi_j+pi_k>=4
```

对 `{i,j,k}={1,2,3}` 成立。

`PROVED`：每个 inclusion-minimal transversal 大小至多三。从该 transversal 与每个 `C_i` 的交中各选一点，所得至多三点的子集仍为 transversal；极小性强迫它等于原集合。

逐 incidence support 分类：

- 二元极小 transversal 恰为 `A_i` 中一点配 `P_i` 中一点，或两个不同 `P_i,P_j` 中各一点。
- 三元极小 transversal 恰为 `A_1,A_2,A_3` 中各一点。

第二项的正向证明可由 private-witness lemma 得到：三点 transversal 的三个 private witnesses 必与三个 `C_i` 一一对应；每一点只能属于自己的 witness set，故三点的 support 分别为 `{1},{2},{3}`。

因此 blocker 数恰为

```text
B
 =alpha_1 alpha_2 alpha_3
  +alpha_1 pi_1+alpha_2 pi_2+alpha_3 pi_3
  +pi_1 pi_2+pi_1 pi_3+pi_2 pi_3.                    (*)
```

若某个 `pi_i>=3`，则取 `(*)` 中含 `pi_i` 的项：

```text
B
 >=pi_i(alpha_i+pi_j+pi_k)
 =pi_i|C_i|
 >=3*4
 =12.
```

余下只需处理 `0<=pi_i<=2`。此时

```text
alpha_i>=alpha_i^(0):=4-pi_j-pi_k>=0.
```

`(*)` 对每个 `alpha_i` 单调不减，因为将 `alpha_i` 增加一，`B` 增加

```text
alpha_j alpha_k+pi_i>=0.
```

按对称性令 `pi_1<=pi_2<=pi_3`。以下十行穷尽 `{0,1,2}` 的所有三元多重集；表中三项依次为 `alpha_1 alpha_2 alpha_3`、`sum alpha_i pi_i` 与 `sum_{i<j}pi_i pi_j`：

| `(pi_1,pi_2,pi_3)` | `(alpha_1^(0),alpha_2^(0),alpha_3^(0))` | 三次项 | 线性项 | `pi` 对项 | `B_0` |
|---|---:|---:|---:|---:|---:|
| `(0,0,0)` | `(4,4,4)` | 64 | 0 | 0 | 64 |
| `(0,0,1)` | `(3,3,4)` | 36 | 4 | 0 | 40 |
| `(0,0,2)` | `(2,2,4)` | 16 | 8 | 0 | 24 |
| `(0,1,1)` | `(2,3,3)` | 18 | 6 | 1 | 25 |
| `(0,1,2)` | `(1,2,3)` | 6 | 8 | 2 | 16 |
| `(0,2,2)` | `(0,2,2)` | 0 | 8 | 4 | 12 |
| `(1,1,1)` | `(2,2,2)` | 8 | 6 | 3 | 17 |
| `(1,1,2)` | `(1,1,2)` | 2 | 6 | 5 | 13 |
| `(1,2,2)` | `(0,1,1)` | 0 | 4 | 8 | 12 |
| `(2,2,2)` | `(0,0,0)` | 0 | 0 | 12 | 12 |

故任意有限 `U` 上均有

```text
|B(mathcal C)|>=12.
```

这十行是由已证明的任意 multiplicity 归约得到的精确有限分类，不是对有限 `U` 的 solver 搜索或外推。

在 `(a,b)=(5,3)` 中，`mathcal S=B(mathcal C)` 的所有成员大小至少二，因此 blocker 无 singleton；上述定理给出 `a>=12`，与 `a=5` 矛盾。

## 5. 排除 `(a,b)=(4,4)`

`PROVED`：每个 `C in mathcal C=B(mathcal S)` 满足

```text
4<=|C|<=|mathcal S|=4,
```

故所有 `C` 恰有四点。有限性保证 `mathcal S` 的任意 transversal 含有 inclusion-minimal transversal；后者属于 `mathcal C`，故每个 transversal 至少四点。

若两个 `S` 在一点 `x` 相交，再从另外两个非空 `S` 中各选一点，即得到至多三点的 `mathcal S`-transversal，矛盾。因此四个 `S` 两两不交。

从每个 `S` 各选一点所得四点集是极小 transversal；删除来自某个 `S` 的点后，该 `S` 未被任何其余选点命中。两两不交还保证不同选择得到不同集合。因此

```text
|B(mathcal S)|
 >=product_(S in mathcal S)|S|
 >=2^4
 =16,
```

与 `|B(mathcal S)|=|mathcal C|=4` 矛盾。

## 6. 局部定理及较小总数

`PROVED`：不仅等号八被排除，所有小于八的总数也被覆盖。由 `a>=4,b>=2`：

- `b=2` 时，二集合不交乘积论证给出 `a>=16`；
- `b=3` 时，三集合 blocker 定理给出 `a>=12`；
- `b>=4` 且 `a+b<=8` 时只能为 `(a,b)=(4,4)`，已经排除。

因此对任意有限 `U`：

```text
|mathcal S|+|mathcal C|>=9,
m(2,4)>=9.
```

本证明不判断九是否可达，也不判断 `m(2,4)` 的精确值。

## 7. `A_2` mutual blockers 与 `A_4` side swap

`PROVED`：冻结 G4.2 接口可不依赖成员数量重新识别 blocker。对 `A_2`，令 `mathcal S` 为 small members，令 `K` 为 large traces，并令

```text
mathcal C={U\K}.
```

同层反链给出每个 `S` 都满足 `S not-subseteq K`，即 `S` 横截每个 `C`。冻结 oriented cover 对所有 `R subseteq U` 给出：

```text
某个 S subseteq R，或某个 R subseteq K。
```

若 `R` 是 `mathcal C` 的 transversal，则第二种情形对所有 `K` 均不可能，故 `R` 包含某个 `S`。结合 `mathcal S` 为 antichain，blocker recognition 给出

```text
mathcal S=B(mathcal C).
```

反向地，若 `D` 是 `mathcal S` 的 transversal，对 `R=U\D` 应用 cover。此时不存在 `S subseteq R`，故某个

```text
U\D subseteq K,
```

等价于 `U\K subseteq D`。`mathcal C` 也是 antichain，因此

```text
mathcal C=B(mathcal S).
```

前驱、后继尺寸界给出 `|S|>=2,|C|>=4`，故局部定理适用。Large trace 取补集为双射，所以

```text
|A_2|=|mathcal S|+|mathcal C|>=9.
```

`PROVED`：对 `A_4`，原接口满足

```text
mathcal S_4=B(mathcal C_4),
mathcal C_4=B(mathcal S_4),
|S_4|>=4,
|C_4|>=2.
```

交换两侧：

```text
mathcal S'=mathcal C_4,
mathcal C'=mathcal S_4.
```

立即得到

```text
mathcal S'=B(mathcal C'),
mathcal C'=B(mathcal S'),
|S'|>=2,
|C'|>=4.
```

交换保持总成员数，故

```text
|A_4|=|mathcal S'|+|mathcal C'|>=9.
```

这只是 blocker pair 的 side swap，不要求原全局族具有补集对称性。

## 8. 全局求和与 eventual 量词

`PROVED`：冻结 G4/G4.2 框架已经给出七个两两不交且耗尽最小族 `F` 的 canonical layers，以及

```text
(|A_0|,...,|A_6|)>=(1,6,8,9,8,6,1).
```

以刚证明的 `|A_2|,|A_4|>=9` 替换相应两项：

```text
|F|
 >=1+6+9+9+9+6+1
 =41.
```

冻结上游量词为：先由 eventual stability 取稳定阈值 `N_stab`，再选择满足

```text
n>=N_stab, n>=7, n>2^55
```

的有限底集，并取 endpoint-normal 的最小 saturated 7-Sperner family `F`。已证上界 55 强制 homogeneous all-or-none block，且

```text
|F|=sat(n,7)=sat(7).
```

因此

```text
sat(7)=sat(n,7)=|F|>=41.
```

候选只需在一个充分大的稳定区间底集上证明该式；没有把结论误写成稳定区间外所有有限 `n` 的统一断言。

## 9. 边界与反例审计

- `PROVED`：`U` 任意且有限，不设大小上界；若 `U` 太小以致不存在四点成员，则 admissible pair 不存在，定理真空成立。
- `PROVED`：两侧为空及 `T=empty set` 的 private-witness 边界已单独处理。
- `PROVED`：所有成员大小只使用下界；非均匀或严格更大的成员不会破坏任何计数。
- `PROVED`：三集合证明允许任意多个点共享同一 incidence pattern；`alpha_i,pi_i` 是实际点的任意 multiplicity。
- `PROVED`：集合族不是 multiset；同一成员不重复计数，clutter 条件排除同侧严格包含。
- `PROVED`：三重 incidence `111` 由无 singleton 排除；`000` 点不可能出现在极小 transversal 中。
- `PROVED`：blocker minimality 在 private witnesses、二/三元 transversal 分类及乘积计数中均明确使用。
- `PROVED`：二集合与四集合的选择计数均由已证明的不交性保证选择到集合的映射单射。
- `PROVED`：`A_4` 操作交换的是已识别的 mutual-blocker 两侧，不偷用全局 complement symmetry。
- `PROVED`：局部 theorem 对任意有限 `U` 成立，再应用于冻结全局接口；不存在固定 core 到任意 `U` 的外推。
- `PROVED`：没有概率、浮点、除以变量、极限、紧致性、Formalizer、solver 或有限底集枚举作为证明依赖。
- `COMPUTED`：本次只进行了文件哈希核验；数学 verdict 不依赖任何有限计算输出。

## 10. 依赖闭包

| 节点 | 状态 | 依赖 |
|---|---|---|
| eventual endpoint-normal minimum family与七层框架 | `PROVED`（冻结） | 已接受 G4、P0054-C7 与冻结文献接口 |
| G4.2 层界 `(1,6,8,9,8,6,1)` | `PROVED`（冻结） | 两份冻结 G4.2 `ACCEPT` |
| `A_2` mutual-blocker recognition | `PROVED` | 同层 antichain、cross intersection、universal oriented cover |
| private-witness lemma | `PROVED` | blocker inclusion-minimality |
| `a>=4,b>=2` | `PROVED` | 非空侧与 private-witness lemma |
| `(6,2)` exclusion | `PROVED` | 无 singleton、二集合不交及乘积计数 |
| 三集合 blocker 下界 12 | `PROVED` | 六 incidence patterns、精确 blocker 分类、十行整数审计 |
| `(5,3)` exclusion | `PROVED` | 三集合 blocker 下界 |
| `(4,4)` exclusion | `PROVED` | transversal number 至少四、两两不交、乘积计数 |
| `m(2,4)>=9` | `PROVED` | 全部 `a+b<=8` 分支 |
| `|A_2|,|A_4|>=9` | `PROVED` | 局部定理、冻结 mutual-blocker 接口与 side swap |
| `sat(7)>=41` | `PROVED` | 七层求和及冻结 eventual quantifier |

```text
ROLE: P0054_G4_3_REFEREE_A_COMPAT
VERDICT: ACCEPT
FIRST_INVALID_STEP: NONE
FIRST_UNCERTAIN_MATHEMATICAL_STEP: NONE_WITHIN_FROZEN_DEPENDENCIES
UNRESOLVED_MATHEMATICAL_DEPENDENCIES: NONE
STATEMENT_MISMATCH: NO
COUNTEREXAMPLE_FOUND: NO
CANDIDATE_SHA256_MATCH: YES
NETWORK_USED: NO
FORMALIZER_USED: NO
LEAN_RUN: NO
FINITE_COMPUTATION_USED_AS_PROOF: NO
G4_3_REFEREE_B_READ: NO
G4_3_PROVER_OR_EXPERIMENTALIST_OUTPUT_READ: NO
FILES_WRITTEN: NONE
REPOSITORY_MODIFIED: NO
REPAIR_EDIT_PERFORMED: NO
```

最终 verdict：`ACCEPT`
