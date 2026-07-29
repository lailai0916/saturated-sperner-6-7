# P0054 G4 兼容替代 Referee B 审稿报告

## 审查范围与完整性

全程离线、只读；未写入仓库，未运行 Lean/形式化，未读取三份 Prover attempt、Referee A 或任何其他 Referee 报告，也未把有限 SMT 结果当作证明。

当前 `HEAD` 为 `d2c8e3eb81466a3743c736319ef1874920590abc`。工作区原有未提交内容；审查前后状态未因本代理改变。

实质读取及 SHA-256：

| 文件 | SHA-256 |
|---|---|
| `AGENTS.md` | `5ec4fe8a019a5c52efe2a382989d58782abfc6242240f77f9a0f5f8a7a39f4c1` |
| `Problems/P0054/statement.md` | `c09275667570ef827939625d7e82560ad8eeb5a448efca3ba251af3208d57990` |
| `Problems/P0054/status.md` | `e412554110cc58f9189237a261eb8699a6b88304a6088ac9e0f99f1c0e41d65f` |
| `Problems/P0054/claims.yaml` | `5ba25ce2d3cb36f5e13c3c2d4dd252d0d47ef3033408d131141e38abe5744564` |
| `literature/g4-global-lower/literature-pack.md` | `dc4a5258ce5fc4b4d2d2ffa5aeb6d96b51d467b2cf013c1655ca44486d22497c` |
| `literature/g4-global-lower/source-theorem-matrix.md` | `fee4fddb9bc0f25cc017e23b2bd7366db9687307c2686270ffa6ff408a20ede0` |
| `literature/g4-global-lower/freeze-manifest.json` | `62313da89a38e1a773954956c8252bf7afcd2e841842bc7686a8fd39cae4a62d` |
| `proof/g4-global-lower/candidate-proof.md` | `9e0821e821458ee390d809d03e5fd927ae661222b4712c2c679b02a26d6ed448` |
| `experiments/g4-global-lower/report.md` | `543561c2313001b82846a0a67e30dd711b57664d72a200271b18840eccb3a09d` |
| `experiments/g4-global-lower/exact_layer_search.py` | `589a90bd629a73daf3fa70d1edd87e08a0141dcf15c1f0b64015162c354901d0` |
| `experiments/g4-global-lower/results.json` | `62fd54f10dca28694b8d5c0d7e9e7fd6ede54636437fe301595be6d1bd247516` |
| `experiments/g4-global-lower/manifest.json` | `a64c6bc7017ba0eddad6709f36e19267194ba3d458c9c5defb92d22a5d562501` |
| `experiments/g4-global-lower/section0-baseline.json` | `6985924a2f54cc845b7415e5023c6b84dc80747770ea5d8624beae6c780b57ae` |
| Martin–Veldt 2025 VOR `/private/tmp/p0054-scout-a.Lxqfjm/mv.pdf` | `e5183031a356080e053ead0766373b4f62eed130e3020b72003617030d670cf2` |

另仅为验证 freeze manifest 闭包而核验了 `search-log.md`，其 SHA-256 为 `92eef5bf137c16ec5ce66d652ae421935afe0b3c9b380c4ab2aff4781bf0bc00`，未依赖其搜索结论。

冻结文献、实验 manifest 与实际文件的字节数及哈希全部相符；`statement.md`、`status.md`、`claims.yaml` 也与 Section 0 基线相符。

## 原始来源核查

直接阅读 13 页 Martin–Veldt VOR 后确认：

- homogeneous atom 的实际门槛是 `|H|≥2`，不是 `|H|>2`。
- Lemma 6 确实从 `|X|>2^{|F|}` 给出 homogeneous atom。
- Lemma 13 确实给出：有 homogeneous atom 的 saturated `k`-Sperner family 的各 canonical layer 均为 saturated antichain。
- Proposition 14 和 Lemma 15 的最小族、端点、内部大小及首尾内部层假设，与候选证明所需输入一致。
- Lemma 17 在 `k=7,i=3` 时，其证明中宣称的严格比较退化为等号；候选证明没有依赖该错误严格性，而是独立排除了八元等号情形。
- Theorem 18 及有限计算均未被候选证明用作 `37` 的证明。

因此来源中的中央严格性接缝不是候选证明的失效点。

## 独立证明重构

### 1. 全局最小族到共同 block 的归约

取稳定区间中满足 `n>2^55` 的基集 `X`，再取含 `∅,X` 的最小 saturated 7-Sperner family `F`。

已有上界仅用于得到

\[
|F|=\operatorname{sat}(7)\le 55,\qquad |X|>2^{55}\ge 2^{|F|}.
\]

因此 VOR Lemma 6 强制任意这个全局最优族拥有 homogeneous atom `H`，且每个成员对 `H` 全含或全不含。令 `U=X\setminus H`。

这一步从任意全局最优族出发，并未预设固定 core、固定层型或共同 block 模板类。

### 2. 七层及端点

饱和性加上 `F` 是 proper family，推出 `F` 中存在七成员严格链；7-Sperner 性又排除八成员链，故高度恰为七。Canonical decomposition 因而恰有七个非空层。

由 `∅,X∈F`：

\[
A_0=\{\varnothing\},\qquad A_6=\{X\}.
\]

每个非首层成员有上一 canonical level 的严格前驱。利用下一层为 saturated antichain，可反证得到每个非末层成员也有下一层的严格后继。

因此：

- small `S∈A_i` 沿前驱链给出 `|S|≥i`；
- large `L∈A_i` 沿后继链给出 `|X\setminus L|≥6-i`。

VOR Lemma 15 在 `k=7` 给出

\[
|A_1|\ge (7-2)+1=6,\qquad |A_5|\ge6.
\]

### 3. partial-`H` 有向覆盖

固定非空真子集 `Q⊊H`。对任意 `R⊆U`，令

\[
T_R=R\cup Q.
\]

由于 `T_R` 只含 `H` 的一部分，它不属于 `F`，故不属于任一 `A_i`。`A_i` 的饱和性给出与 `T_R` 严格可比的成员：

- 若为 small `S`，只能有 `S⊆R`；
- 若为 large `K∪H`，只能有 `R⊆K`。

所以对 `i=2,3,4`，

\[
Z_i(R)=\sum_{S\text{ small}}1_{S\subseteq R}
+\sum_{K\text{ large trace}}1_{R\subseteq K}\ge1
\]

对所有 `R⊆U` 成立，包括 `R=∅`、`R=U` 及成员自身 trace。该推导只需 `|H|≥2`，不要求 `H` 在各层仍为极大 atom。

令 `R` 按 Bernoulli(`p`) 生成，精确得到

\[
1\le E Z_i
=\sum_S p^{|S|}
+\sum_K(1-p)^{|U\setminus K|}.
\]

### 4. 各层有理界

- `i=2,p=2/5`：

\[
p^{|S|}\le\frac4{25},\qquad
(1-p)^{|U\setminus K|}\le\left(\frac35\right)^4
=\frac{81}{625}<\frac4{25}.
\]

六个事件最多贡献 `24/25<1`，故 `|A_2|≥7`。

- `i=4,p=3/5`：

\[
p^{|S|}\le\frac{81}{625}<\frac4{25},\qquad
(1-p)^{|U\setminus K|}\le\frac4{25}.
\]

同理 `|A_4|≥7`。

- `i=3,p=1/2`：

每个事件至多 `1/8`，先得 `|A_3|≥8`。

### 5. `|A_3|=8` 的全部等号蕴含

若恰有八个成员，则

\[
1\le E Z_3\le 8\cdot\frac18=1.
\]

所以：

1. 每个事件概率都必须恰为 `1/8`；
2. 每个 small 成员恰有大小 3；
3. 每个 large 成员的补集恰有大小 3；
4. `p=1/2` 对每个 `R⊆U` 都赋正概率；
5. `Z_3(R)≥1` 且均值为 1，因此逐点 `Z_3(R)=1`。

令 small、large 数量分别为 `a,b`：

- `R=∅` 时无 small 事件、所有 large 事件发生，故 `b=1`；
- `R=U` 时所有 small 事件发生、无 large 事件发生，故 `a=1`。

这与 `a+b=8` 矛盾，故

\[
|A_3|\ge9.
\]

独立的同侧闭包核查也成立：两个 small 上闭包在生成元之并处相交；两个 large 下闭包在 trace 之交处相交。因此一重覆盖至多各取一个。

### 6. 总和

\[
|F|\ge1+6+7+9+7+6+1=37.
\]

由于所选 `n` 已在稳定区间，

\[
\operatorname{sat}(7)=\operatorname{sat}(n,7)=|F|\ge37.
\]

## 边界与反例审计

- `|H|=2`：存在非空真子集 `Q`，证明仍完整。
- `R=∅`、`R=U`：均被覆盖，且正是中层等号排除的关键点。
- 成员自身：small trace `S=R` 与 large trace `K=R` 都由非严格投影事件正确计数；原基集中的可比仍因 `Q` 而严格。
- small/large 某侧为空：覆盖分别在 `R=U` 或 `R=∅` 立即失败。
- 空集/全集：内部层的大小限制排除了 small 空集和 large 全集。
- full support：有限 `U` 上的均匀分布对所有子集赋概率 `2^{-|U|}>0`。
- 最小反例攻击：任何覆盖反例都给出某个 `R`，使 `T_R` 与整层无可比成员，直接违反该层的饱和性；不存在最小反例。
- 对 `|A_3|=8`，任意最小反例都会被 `R=∅,U` 强制为 `a=b=1`，故同样不可能。
- 独立穷举 `|U|=0,...,4` 的所有 eligible 事件子族，没有找到满足秩限制、反链和覆盖的候选；这只记为 `COMPUTED` 辅助证据。
- `|U|≤4` 也可直接排除：七成员链有六次严格增长，而 `H` 至多整体进入一次，至少五次增长必须来自 `U`。

实验报告中的有限 Z3 `UNSAT/UNKNOWN` 未进入上述证明。

## 全局性判断

该证明不是把 G0–G3 的固定共同 block 类结论冒充全局下界。共同 block 是从任意足够大稳定基集上的全局最小族，通过 homogeneous-atom 定理强制得到的；`U` 的大小始终任意，覆盖不等式量化所有 `R⊆U`。证明未使用 core `7/8` 的 CNF、DRAT 或有限 SMT 不可满足性。

因此它证明的是 eventual stable 参数的全局结论 `sat(7)≥37`，不是仅有的固定模板类下界。它不证明 `sat(7)=37`、`sat(7)=55`、新颖性或优先权。

`status.md` 仍停留在 G3，`claims.yaml` 尚无 G4 新 claim；候选文件明确规定两份审稿均通过前不得更新，因此这是门控中的预期元数据状态，不是数学陈述错配。

```text
FIRST_INVALID_STEP: NONE
NETWORK_USED: NO
WRITES_PERFORMED: NO
FORMALIZATION_USED: NO
OTHER_REFEREE_REPORTS_READ: NO
PROVER_ATTEMPTS_READ_OR_RELIED_ON: NO
FINITE_SMT_USED_AS_PROOF: NO
```

最终 verdict：`ACCEPT`
