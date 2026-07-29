# P0054 G4.3 隔离兼容 Referee B 审稿报告

最终 verdict：`ACCEPT`

## 1. 隔离范围与输入完整性

`COMPUTED`：全部材料在实质读取前通过 SHA-256 门，并在审稿结束后再次复核，前后结果一致。

| 文件 | SHA-256 |
|---|---|
| `AGENTS.md` | `5ec4fe8a019a5c52efe2a382989d58782abfc6242240f77f9a0f5f8a7a39f4c1` |
| `section0-freeze.md` | `759e7b6a2bbad8853f2baa7424c8b19ac06e6ecaf07b3c3758a30d57a9a99aaf` |
| `frozen-subproblem.md` | `cc64e1e376196355b68266abcfdf228d38836b6fc05c170204397efc67a8ddaa` |
| G4.3 `candidate-proof.md` | `ff1271a9552f5eaf82f6d44ac19edfa0e5f550d383d2157e0d16b0eac591a684` |
| G4 `candidate-proof.md` | `9e0821e821458ee390d809d03e5fd927ae661222b4712c2c679b02a26d6ed448` |
| G4 `referee-a.md` | `0996bc5bd64941554f3b0e6d36f3d29ffc36a5c1c32e203802092dc81c6acba4` |
| G4 `referee-b.md` | `b1a40729e21ce51e52739cd5e06cb4417fb7cb399cb43edeffbfdc142852b57a` |
| G4.2 `candidate-proof.md` | `ef87bce75e3db5a8a46d99318c6b4c5e8bc769f33ef61be4e6adee55372c5a1e` |
| G4.2 `referee-a.md` | `664bdb20b8b9c86fac80a2d2fac654b4b91e95eed2d50512534ea45c88d627a0` |
| G4.2 `referee-b.md` | `5a4866c494d123f6478b2164a314749e5b66f2b92f1ec80db4fb52fca5f79bfc` |

`COMPUTED`：未读取 G4.3 Referee A、任何 G4.3 Prover/Experimentalist 输出、源代码或结果文件。冻结 G4/G4.2 Referee 报告仅作为获准上游输入；本审查仍独立重构了实际使用的接口。

## 2. 命题与空侧边界

`PROVED`：候选证明处理的命题与冻结子问题一致。底集 `U` 任意有限，两侧是普通 set families，并满足相互 blocker 与成员大小下界。

`PROVED`：两侧必非空：

- 若 `mathcal C=empty family`，则 `mathcal S=B(mathcal C)={empty set}`，违反 `|S|>=2`。
- 若 `mathcal S=empty family`，则 `mathcal C=B(mathcal S)={empty set}`，违反 `|C|>=4`。

没有遗漏 `B(empty family)={empty set}` 约定，也没有把 set family 当作 multiset。

## 3. Private-witness 与分拆归约

`PROVED`：若 `T in B(mathcal H)` 且 `x in T`，则 `T\{x}` 不是 transversal，所以存在 `E_x in mathcal H` 满足

```text
T intersect E_x = {x}.
```

`PROVED`：若 `x!=y`，则 `E_x!=E_y`；否则同一个交集同时等于 `{x}` 与 `{y}`。故

```text
|T| <= |mathcal H|.
```

`PROVED`：任取 `C in mathcal C=B(mathcal S)` 和 `S in mathcal S=B(mathcal C)`，得到

```text
4 <= |C| <= |mathcal S| = a,
2 <= |S| <= |mathcal C| = b.
```

因此在 `a+b=8` 下仅有

```text
(a,b)=(4,4),(5,3),(6,2).
```

此归约没有假设 uniformity、不同 incidence pattern 或待证结论。

## 4. `(6,2)` 攻击

`PROVED`：写 `mathcal C={C_1,C_2}`。若两者相交，则交点给出 singleton minimal transversal，与 `|S|>=2` 矛盾。因此 `C_1,C_2` 必须不交。

`PROVED`：每个 `x in C_1,y in C_2` 给出不同的 inclusion-minimal transversal `{x,y}`。不交性同时保证极小性和选择到实际子集的单射性。因此

```text
|B(mathcal C)| >= |C_1||C_2| >= 16,
```

与 `a=6` 矛盾。这里的不交性是推导结果，并非预设。

## 5. 三集合 exact-count 攻击

`PROVED`：设 `mathcal C={C_1,C_2,C_3}`，各自大小至少四，且 blocker 无 singleton。于是三重交为空。

定义实际点的六个 incidence classes：

```text
A_i = C_i \ (C_j union C_k),
P_i = (C_j intersect C_k) \ C_i,
alpha_i=|A_i|, pi_i=|P_i|.
```

`PROVED`：任意极小 transversal 至多三点。两点极小 transversal 恰为：

- `A_i` 与 `P_i` 各取一点；
- 两个不同的 `P_i,P_j` 各取一点。

三点极小 transversal 恰为从 `A_1,A_2,A_3` 各取一点。其正向证明由三个不同 private witnesses 强制三个点分别具有 singleton incidence support。

因此得到实际子集的精确计数

```text
|B(mathcal C)|
 = alpha_1 alpha_2 alpha_3
   + sum_i alpha_i pi_i
   + pi_1 pi_2 + pi_1 pi_3 + pi_2 pi_3.
```

`PROVED`：若某个 `pi_i>=3`，则

```text
|B(mathcal C)|
 >= pi_i(alpha_i+pi_j+pi_k)
 = pi_i|C_i|
 >= 12.
```

`PROVED`：若所有 `pi_i<=2`，由

```text
alpha_i >= 4-pi_j-pi_k
```

以及计数式对各 `alpha_i` 单调不减，十个无序 `pi` 三元组的下界依次为

```text
64, 40, 24, 25, 16, 12, 17, 13, 12, 12.
```

故始终有 `|B(mathcal C)|>=12`。

该分类允许：

- 任意重复 incidence pattern；
- incidence class 为空；
- 非均匀的 `|C_i|`；
- 任意两两相交；
- 任意有限且无大小上界的 `U`。

计数对象是不同的实际子集，不是 pattern quotient 或带重数元组。

`PROVED`：在 `(a,b)=(5,3)` 中，`mathcal S=B(mathcal C)` 无 singleton，上述定理给出 `a>=12`，与 `a=5` 矛盾。

## 6. `(4,4)` 与四对四 transversal 计数

`PROVED`：private-witness 上界与 `|C|>=4` 强制每个 `C in B(mathcal S)` 恰有四点。因此 `mathcal S` 的任意 transversal 都至少有四点。

`PROVED`：四个 `S` 必须两两不交。若某点同时落在两个成员中，再从另外两个非空成员各取一点，即得至多三点的 transversal，矛盾。

`PROVED`：从四个两两不交的 `S` 各取一点，所得四点集合是 inclusion-minimal transversal；删除来自某个 `S_i` 的点后便漏掉 `S_i`。不同选择由与各个不交 `S_i` 的交恢复，故对应不同实际子集。因此

```text
|B(mathcal S)|
 >= product_(S in mathcal S)|S|
 >= 2^4
 = 16,
```

与 `|mathcal C|=4` 矛盾。

## 7. 小于八成员的完整性

`PROVED`：由 `a>=4,b>=2`：

- `b=2` 时，两集合论证给 `a>=16`；
- `b=3` 时，三集合定理给 `a>=12`；
- `b>=4` 且 `a+b<=8` 时，只能为 `(4,4)`。

所以不存在总数小于或等于八的 admissible pair，确实得到

```text
m(2,4) >= 9.
```

## 8. `A_2` mutual-blocker recognition

`PROVED`：冻结 oriented cover 对每个 `R subseteq U` 给出

```text
存在 small S subseteq R，
或存在 large trace K 满足 R subseteq K。
```

令 `C=U\K`。层反链的 cross 条件给出每个 `S` 都与每个 `C` 相交。

`PROVED`：若 `R` 是 `mathcal C` 的 transversal，则 `R` 不包含于任何 `K`；cover 强制某个 `S subseteq R`。结合 small 侧 antichain，得到

```text
mathcal S=B(mathcal C).
```

`PROVED`：若 `D` 是 `mathcal S` 的 transversal，对 `R=U\D` 应用 cover。没有 `S subseteq R`，故某个 `R subseteq K`，即 `C subseteq D`。补后的 large-trace 侧仍是 antichain，因此

```text
mathcal C=B(mathcal S).
```

两次 recognition 都证明了 blocker minimality，没有把一般 transversal 误认为 blocker 成员。

`PROVED`：complementing large traces 是双射，所以实际层大小为

```text
|A_2|=|mathcal S|+|mathcal C|>=9.
```

即使一个 core subset 同时作为两侧元素出现，也不会造成层计数合并：small 与 large 原成员由是否包含 `H` 区分。

## 9. `A_4` 补侧交换

`PROVED`：冻结 `A_4` 接口给出相互 blocker 的 `mathcal S_4,mathcal C_4`，其中成员大小下界分别为四和二。令

```text
mathcal S'=mathcal C_4,
mathcal C'=mathcal S_4.
```

则

```text
mathcal S'=B(mathcal C'),
mathcal C'=B(mathcal S'),
|S'|>=2,
|C'|>=4.
```

交换保持普通 set-family 性、antichain、任意有限 `U` 的量词及两侧总成员数。因此

```text
|A_4|>=9.
```

这只是已识别 mutual-blocker pair 的 side swap，不假设全局族具有补对称性。

## 10. Stable minimum 与全局求和

`PROVED`：冻结 G4/G4.2 框架选择稳定区间内、充分大有限底集上的 endpoint-normal minimum saturated 7-Sperner family，并由既有上界 55 强制 homogeneous block。该步骤不使用待证下界 41，依赖无环。

`PROVED`：七个 canonical layers 不交且耗尽该最小族。把 `A_2,A_4` 的新界代入冻结界，得到

```text
(|A_0|,...,|A_6|)
 >= (1,6,9,9,9,6,1),
```

故

```text
|F| >= 1+6+9+9+9+6+1 = 41.
```

所选底集位于 eventual stable range，且 `F` 为该底集上的最小族，所以

```text
sat(7)=sat(n,7)=|F|>=41.
```

该结论是 eventual stable 参数的全局下界，不是固定 core、固定 incidence pattern 或有限 solver 类结论。

## 11. 反例与第一失效步骤

`PROVED`：任何总数至多八的候选反例都必须进入上述三种分拆，而每种均产生严格 blocker-count 矛盾。因此没有剩余最小反例形态。

```text
FIRST_INVALID_STEP: NONE
FIRST_UNCERTAIN_MATHEMATICAL_STEP: NONE_WITHIN_FROZEN_DEPENDENCIES
COUNTEREXAMPLE: NONE
MINIMAL_COUNTEREXAMPLE: NONE
STATEMENT_MISMATCH: NO
UNRESOLVED_MATHEMATICAL_DEPENDENCIES: NONE
```

## 12. 操作声明

```text
ROLE: P0054_G4_3_REFEREE_B_COMPAT
VERDICT: ACCEPT

NETWORK_USED: NO
FILES_WRITTEN_BY_THIS_REFEREE: NONE
REPOSITORY_MUTATIONS_BY_THIS_REFEREE: NONE
G4_3_REFEREE_A_READ: NO
G4_3_PROVER_OUTPUT_READ: NO
G4_3_EXPERIMENTALIST_OUTPUT_READ: NO
ONLY_AUTHORIZED_FILES_SUBSTANTIVELY_READ: YES
FROZEN_G4_AND_G4_2_INPUTS_READ: YES
FINAL_HASH_RECHECK_MATCHED: YES

FINITE_SOLVER_RUN: NO
FINITE_UNSAT_USED_AS_PROOF: NO
FORMALIZER_USED: NO
FORMALIZATION_PERFORMED: NO
LEAN_RUN: NO
REPAIR_EDIT_PERFORMED: NO
CLAIMS_OR_STATUS_MODIFIED: NO
COMMIT_STAGE_PUSH_PUBLICATION_PERFORMED: NO
```

本 `ACCEPT` 仅确认候选证明在冻结依赖内数学闭合；不授权 exact-value、novelty、priority、`solved-status`、Formalizer、状态更新、提交、推送或公开发布。

最终 verdict：`ACCEPT`
