# P0054 G4 兼容替代 Referee A 审稿报告

最终 verdict：`ACCEPT`

## 一、审查范围与输入完整性

本审查独立重建证明，不采用三份 Prover 的结论，也未读取任何其他 Referee 报告。

起始 `HEAD`：

```text
d2c8e3eb81466a3743c736319ef1874920590abc
```

工作树起始即存在 P0053 修改及未跟踪的 P0054 文件；本轮未将其误报为干净基线，也未改变任何文件。

实质读取的规定输入及 SHA-256：

| 文件 | SHA-256 |
|---|---|
| `AGENTS.md` | `5ec4fe8a019a5c52efe2a382989d58782abfc6242240f77f9a0f5f8a7a39f4c1` |
| `Problems/P0054/statement.md` | `c09275667570ef827939625d7e82560ad8eeb5a448efca3ba251af3208d57990` |
| `Problems/P0054/status.md` | `e412554110cc58f9189237a261eb8699a6b88304a6088ac9e0f99f1c0e41d65f` |
| `Problems/P0054/claims.yaml` | `5ba25ce2d3cb36f5e13c3c2d4dd252d0d47ef3033408d131141e38abe5744564` |
| `Problems/P0054/literature/g4-global-lower/literature-pack.md` | `dc4a5258ce5fc4b4d2d2ffa5aeb6d96b51d467b2cf013c1655ca44486d22497c` |
| `Problems/P0054/literature/g4-global-lower/source-theorem-matrix.md` | `fee4fddb9bc0f25cc017e23b2bd7366db9687307c2686270ffa6ff408a20ede0` |
| `Problems/P0054/literature/g4-global-lower/freeze-manifest.json` | `62313da89a38e1a773954956c8252bf7afcd2e841842bc7686a8fd39cae4a62d` |
| `Problems/P0054/proof/g4-global-lower/candidate-proof.md` | `9e0821e821458ee390d809d03e5fd927ae661222b4712c2c679b02a26d6ed448` |

原始文献快照：

| 快照 | SHA-256 |
|---|---|
| `/private/tmp/p0054-scout-a.Lxqfjm/mv.pdf`，Martin–Veldt 2025 VOR，13 页 | `e5183031a356080e053ead0766373b4f62eed130e3020b72003617030d670cf2` |
| `/private/tmp/p0054-scout-a.Lxqfjm/gklppp.pdf`，Gerbner 等原始来源，用于复核端点正规化和稳定性 | `eaf3ce7f53045ff6fc8d810e7b1b469468e198510f6c4985e39c946c5790d89e` |

这里的 MV PDF 是工作树外、本轮 Scout 保存的临时快照，不是仓库内实体；其哈希与 `freeze-manifest.json` 完全一致。第二份独立 MV 快照也具有同一哈希。

清单附带项目也复核一致：

```text
search-log.md:
92eef5bf137c16ec5ce66d652ae421935afe0b3c9b380c4ab2aff4781bf0bc00

section0-baseline.json:
6985924a2f54cc845b7415e5023c6b84dc80747770ea5d8624beae6c780b57ae
```

## 二、从定义重建全局量词

目标不是某个固定 core/template 类，而是 eventual saturation number：

```text
sat(n,7)
  = n 元底集上饱和 7-Sperner 族的最小基数；

∃N_stab ∀n≥N_stab,
  sat(n,7)=sat(7).
```

证明选择

```text
n ≥ N_stab,
n ≥ 7,
n > 2^55.
```

然后由 Gerbner 等 Lemma 6 选择一个同时含 `∅` 与 `X` 的最小基数饱和族 `F`，满足

```text
|F| = sat(n,7) = sat(7).
```

已有全局上界 P0054-C7 给出 `|F|≤55`，所以

```text
|X| = n > 2^55 ≥ 2^|F|.
```

MV Lemma 6 因而给出 `F` 的 homogeneous atom `H`。后续对这个任意充分大稳定底集上的最小族证明 `|F|≥37`，故结论确实是

```text
sat(7)≥37,
```

而不是：

- 固定七核或八核模板类下界；
- common-block layered-template 类最优性；
- DRAT 搜索类的不可满足性；
- 对所有有限 `n` 的 `sat(n,7)≥37`。

因此 `CLASS_RESTRICTED: NO` 的表述正确。

## 三、逐依赖审计

### 1. 稳定性与充分大 `n`

Gerbner 等的稳定性结果确实提供 eventual constant。候选只需存在一个同时超过稳定阈值和 `2^55` 的整数 `n`，量词选择合法。

利用已经证明的上界 55 来取得 atom 阈值不循环：37 没有出现在 `n>2^55` 的选择中。

### 2. 端点正规化与最小性

Gerbner 等 Lemma 6 的原文是存在性正规化：

```text
若 2≤k≤n，则存在一个最小基数的饱和 k-Sperner 族，
同时含 ∅ 和 [n]。
```

候选正确地使用“可选择这样的最小族”，没有错误地声称每个最小族天然都含端点。

该正规化保持最小基数，所以 MV Lemma 15 所需的 minimum-cardinality 前提仍然成立。

### 3. homogeneous atom 阈值

MV VOR 的定义是

```text
homogeneous atom H 满足 |H|≥2，
```

不是旧本地材料中的 `|H|>2`。

候选严格使用 `|H|≥2`。当 `|H|=2` 时仍可选非空真子集 `∅≠Q⊊H`，因此覆盖论证的最小边界合法。

### 4. canonical decomposition 恰有七层

因为 `|F|≤55<2^n`，存在 `T∉F`。饱和性使 `F∪{T}` 含八元严格链；该链必须含 `T`，删除它后得到 `F` 中的七元严格链。

另一方面，7-Sperner 性排除八元严格链，所以 `F` 的高度恰为七。

按迭代删除极小元得到的 canonical level 等于“以该元素结尾的最长链的包含步数”。一条七元极大链在位置 `i` 的元素恰位于 `A_i`；若层号更大，与剩余链尾拼接会产生超过七元的链。

所以：

```text
F = A_0 ⊔ A_1 ⊔ ... ⊔ A_6
```

七层全部非空、互不相交且耗尽 `F`。候选没有暗中假设层非空。

### 5. 层饱和

MV Lemma 13 的前提是：

- `F` 是饱和 `k`-Sperner 族；
- `F` 有 homogeneous atom `H`；
- `A_i` 是 canonical decomposition。

三项均已满足，因此每个 `A_i` 是整个 `2^X` 中的 saturated antichain。后续测试集覆盖确实可以逐层应用饱和性。

### 6. 共享 block 与层内 atom 最大性的区别

`H` 是整个 `F` 的 homogeneous atom。因为 `A_i⊆F`，每层成员仍然对同一 `H` 全含或全不含。

但 `H` 不必继续是每个 `A_i` 的最大 atom。候选明确放弃了这一错误强化，只使用：

```text
∀B∈A_i,
H⊆B 或 B∩H=∅。
```

覆盖论证只需要这个 inherited all-or-none block 加上 `A_i` 的饱和性；没有偷偷恢复层内 atom 最大性。

### 7. 端点层与 MV Lemma 15

由端点正规化：

```text
A_0={∅}.
```

任意七元链必须以 `X` 结尾，否则可追加 `X` 得到八元链。因此 `X∈A_6`；再由 `A_6` 是 antichain 得

```text
A_6={X}.
```

MV Lemma 15 原始前提为：

- minimum-cardinality saturated `k`-Sperner family；
- canonical decomposition；
- homogeneous atom `H`。

候选的 `F` 完全满足这些前提。在 `k=7` 时，原文给出：

```text
A_1: 至少 5 个 small singleton，并有 1 个 large 成员；
A_5: 对偶地至少 5 个 large co-singleton，并有 1 个 small 成员。
```

故候选所取的较弱结论

```text
|A_1|≥6, |A_5|≥6
```

有效。

原文的 reduction argument 即使被保守解读为先取得同大小正规形，也足以支持这里的基数结论：若 reduction 真减少总大小，将直接违反 `F` 的全局最小性。

### 8. 前驱、后继和尺寸限制

canonical level 直接给每个 `A_i` 成员一个 `A_{i-1}` 中的严格前驱。

对后继，候选使用 `A_{i+1}` 的饱和性。若所得可比较成员 `C∈A_{i+1}` 满足 `C⊊B`，则 `C` 的 canonical 前驱 `D∈A_i` 会满足

```text
D⊊C⊊B,
```

与 `D,B∈A_i` 的 antichain 性矛盾。因此必有 `B⊊C`。

沿前驱链，小成员保持小；沿后继链，大成员保持大。故：

```text
S∈A_i small  => |S|≥i；
L∈A_i large  => |X\L|≥6-i。
```

没有遗漏空集、全集或方向问题。

### 9. 精确 oriented cover

固定 `i∈{2,3,4}`，取 `∅≠Q⊊H`，对每个 `R⊆U=X\H` 令

```text
T_R=R∪Q.
```

`T_R` 只含 `H` 的一部分，所以不可能属于 `F`，尤其不属于 `A_i`。

由 `A_i` 饱和，存在与 `T_R` 严格可比的层成员：

- small 成员不能包含 `T_R`，只能被 `T_R` 包含，投影后为 `S⊆R`；
- large 成员不能被 `T_R` 包含，只能包含 `T_R`，投影后为 `R⊆K=L\H`。

因此对所有 `R⊆U`：

```text
Z_i(R)
 = Σ_small 1[S⊆R] + Σ_large 1[R⊆K]
 ≥1.
```

方向、严格性以及投影后使用非严格包含均正确。

### 10. `A_2` 与 `A_4`

对 `A_2` 取 `p=2/5`：

```text
small 概率 ≤(2/5)^2=4/25；
large 概率 ≤(3/5)^4=81/625<4/25。
```

故

```text
1≤E[Z_2]≤(4/25)|A_2|,
```

推出 `|A_2|≥7`。

对 `A_4` 取 `p=3/5`，两侧上界交换，同样得到 `|A_4|≥7`。

这里没有使用未经证明的补集对偶，也允许 small 或 large 一侧为空。

### 11. 中间层及等号排除

`p=1/2` 给出

```text
1≤E[Z_3]≤|A_3|/8,
```

先得 `|A_3|≥8`。

若 `|A_3|=8`，所有事件概率都必须等于 `1/8`，所以：

- 每个 small 成员大小恰为 3；
- 每个 large 成员补集大小恰为 3；
- 因 `Z_3(R)≥1` 且均匀分布对每个 `R` 都赋正概率，`E[Z_3]=1` 强迫 `Z_3(R)=1` 对所有 `R` 成立。

取 `R=∅`，所有 large down-events 发生而 small event 均不发生，故 large 成员数 `b=1`。

取 `R=U`，所有 small up-events 发生而 large event 均不发生，故 small 成员数 `a=1`。

于是 `a+b=2`，与 `|A_3|=8` 矛盾。因此：

```text
|A_3|≥9.
```

这是完整、有限、逐点的等号排除。

### 12. 求和

七层不交且耗尽 `F`，故

```text
|F|
≥1+6+7+9+7+6+1
=37.
```

又因 `|F|=sat(n,7)=sat(7)`，得到全局 eventual 结论 `sat(7)≥37`。

## 四、边界情况

逐项检查结果：

- `n=N_stab`：允许，只需同时满足另外两个下界。
- `n=7`：实际选择的 `n>2^55`，所以 `k≤n` 自动满足。
- `F=2^X`：由 `|F|≤55<2^n` 排除。
- `|H|=2`：非空真子集 `Q` 仍存在。
- `R=∅` 与 `R=U`：均包含在覆盖中，并且是中间层等号排除的关键。
- small side 或 large side 为空：`A_2,A_4` 的期望估计仍成立；中间层假设等号时会自动排除。
- `U=∅`：形式上的覆盖仍有唯一 `R=∅`；内部层尺寸限制会立即排除内部成员，因而不会产生漏例。
- endpoint 成员混入 `A_2,A_3,A_4`：由 `|S|≥i` 和 `|X\L|≥6-i` 排除。
- 严格可比与投影后非严格包含：处理正确。
- 所有数值比较均为精确有理不等式；未依赖浮点舍入。
- `A_4`：有直接 `p=3/5` 证明，不依赖未陈述的对偶定理。

## 五、MV Lemma 17 的原文含义与第一处失效步骤

MV VOR Lemma 17 的打印结论是

```text
|A_i^small|+|A_i^large|
>
exp(2 ln(2) · i(k-i-1)/(k-1)).
```

在 `k=7`：

```text
i=2:
|A_2| > 2^(8/3) ≈ 6.3496，
故整数性给 |A_2|≥7。

i=3:
|A_3| > 2^3 = 8，
故打印结论本身给 |A_3|≥9。
```

再经对偶，`A_4≥7`。所以打印的 Lemma 17 与 Lemma 15、端点层相加，几乎直接给出 37。

但是原文证明在中央边界存在明确失效步骤。其参数为

```text
ε=(ln 2/2)(1-2i/(k-1)).
```

当 `k=7,i=3` 时 `ε=0`。原文期望估计中的严格比较

```text
(1/2±ε)^m < exp(-m ln2 ± 2mε)
```

此时退化为等号，不再严格。因此原文证明只能直接推出 `|A_3|≥8`，不能仅凭该严格号推出 9。

这是本次发现的第一处不成立步骤，但它位于 MV Lemma 17 的打印证明中，不位于候选证明中。候选第 8 节的逐点一重覆盖与 `R=∅,U` 论证独立排除了等号 8，完整修复了该中央缝隙。

候选证明中的第一处不成立步骤：`NONE`。

## 六、prior-art 结论

数学有效性与 prior-art 必须分开：

- MV Theorem 18 明文给出的粗化全局结果在 `k=7` 仅为 `sat(7)≥10`。
- 但 MV Lemma 17 的打印陈述专门化后已经明文包含 `A_2≥7`、`A_3≥9` 的数值内容；对偶给 `A_4≥7`。
- 中央层的打印证明存在严格性缺口，而候选提供了独立修复。
- 因而 37 不应被宣传为与 MV 文献毫无关联的新下界；更准确的描述是“MV 打印层界的 `k=7` 专门化，加上对中央等号缝隙的独立修复和完整全局量词重建”。

本 verdict 仅认可证明正确性，不认可 novelty、priority、`WORLD_FIRST`、最佳已知或全局文献缺失。负面搜索仍只能保留：

```text
NO_PUBLIC_EQUIVALENT_FOUND_IN_RECORDED_SCOPE
STATUS_UNVERIFIED
```

## 七、状态文件与证据标签

当前 `status.md` 仍停留在 G3，`claims.yaml` 仅到 P0054-C16，尚无 P0054-C17。这与候选文件的“pending two referees”状态一致，不构成数学 statement mismatch。

在主 Agent 完成另一份独立 Referee 审计前，仓库公开标签不应提前提升。本报告本身不修改 `status.md`、`claims.yaml` 或 candidate。

## 八、操作声明

```text
ROLE: REFEREE_A_COMPAT
NETWORK_USED: NO
FILES_WRITTEN: NONE
REPOSITORY_MODIFIED: NO
OTHER_REFEREE_REPORTS_READ: NO
PROVER_CONCLUSIONS_RELIED_ON: NO
FORMALIZATION_PERFORMED: NO
LEAN_RUN: NO
REPAIR_EDIT_PERFORMED: NO
SOURCE_PDF_ACCESS: LOCAL_OFFLINE_ONLY
```

最终 verdict：`ACCEPT`
