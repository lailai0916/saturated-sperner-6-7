# P0054 G4.4 — 隔离 Prover A 报告

```text
ROLE: COMPATIBILITY_PROVER_A
MODEL_PATH: dedicated prover role failed before material access; isolated compatible replacement
NETWORK: OFFLINE
REPOSITORY_WRITES_BY_ROLE: NONE
OTHER_G4_4_ROLE_OUTPUTS_READ_OR_CONTACTED: NONE
FORMALIZER: NOT_USED
RESULT: PARTIAL_PROOF; PRODUCT_INEQUALITY_UNKNOWN_IN_THIS_ROUTE
```

## 1. 冻结核验

`COMPUTED`：literature freeze manifest 的 SHA-256 为

```text
765b79a3832c03e03903045286be1fa8f05f714dee1381e6a5d34a2b067954e5
```

与冻结值一致。角色全程离线、只读；未读取其他 G4.4 角色输出，未修改仓库，
结束时 `git diff --check` 通过。

## 2. 任意有限底集的 incidence support

`DEFINITION`：令

\[
a=|\mathcal S|,\qquad b=|\mathcal C|,
\]

其中

\[
\mathcal S=B(\mathcal C),\quad
\mathcal C=B(\mathcal S),\quad
\min|S|\ge2,\quad \min|C|\ge4.
\]

编号 \(\mathcal C=\{C_1,\ldots,C_b\}\)。对实际点
\(x\in\bigcup_iC_i\) 定义

\[
I(x)=\{i\in[b]:x\in C_i\}.
\]

`PROVED`：因为 \(\mathcal S\) 无 singleton，所有实际 supports 都是
\([b]\) 的非空真子集。令 \(m_I\) 为 support \(I\) 的实际点数。

`PROVED`：minimal transversals 与 \([b]\) 的 inclusion-minimal support
covers 精确对应。若 \(\mathcal M_b\) 是所有由不同非空真 supports 组成的
minimal covers，则

\[
a=Q_b(m)
=\sum_{\mathcal P\in\mathcal M_b}\prod_{I\in\mathcal P}m_I.    \tag{1}
\]

乘积逐一选择不同实际点，所以 (1) 计数普通 blocker subsets，而不是把一个
pattern 当成一个点。

`PROVED`：每个实际点都出现在某个 minimal transversal 中。给定
\(x\in C_i\)，对每个不含 \(x\) 的 \(C_j\)，clutter 性给
\(y_j\in C_j\setminus C_i\)。集合 \(\{x\}\cup\{y_j\}\) 是 transversal，
且除 \(x\) 外的点都在 \(C_i\) 外；从中取 inclusion-minimal transversal
时必须保留 \(x\)。

`PROVED`：因此每个 \(m_I>0\) 的 support 都出现在至少一个
\(\mathcal M_b\) 成员中。此外

\[
|C_i|=\sum_{I\ni i}m_I,
\]

而 clutter 性等价于每个有序对 \(i\ne j\) 都有正 multiplicity support
\(I\) 满足 \(i\in I,j\notin I\)。

`PROVED`：在搜索 \(a\le A\) 的反例时，private-witness 注入给

\[
4\le|C_i|\le a\le A.
\]

所以 repeated patterns、非均匀成员大小及任意有限 \(U\) 被一个有限
multiplicity 问题完整覆盖；没有预设底集大小。

`COMPUTED`：minimal support-cover patterns 的数目为：

| \(b\) | 按 cover 大小分布 | 合计 |
|---:|---|---:|
| 4 | \(25,22,1\) | 48 |
| 5 | \(90,305,65,1\) | 461 |
| 6 | \(301,3410,2540,171,1\) | 6423 |

`COMPUTED`：本角色用一个 Z3/support-polynomial 实现，对 active support
family 按全部 \(b!\) 个 row permutations 取 lexicographic canonical
representative，再枚举 multiplicities：

| 搜索 | canonical support families | 结果 |
|---|---:|---|
| \(b=4,\ Q_4\le7\) | 123 | 无所有 row degrees 至少四的实例 |
| \(b=5,\ Q_5\le6\) | 677 | 无所有 row degrees 至少四的实例 |
| \(b=6,\ Q_6\le5\) | 1028 | 无所有 row degrees 至少四的实例 |

`UNKNOWN`：这些结果没有反例，但不能提升为证明。它们没有归档独立可检查
certificate，也没有完整第二实现。

## 3. 五成员解析定理

`PROVED`（本角色候选）：若 \(H\) 是恰有五个成员的 clutter，满足

\[
\min_{E\in H}|E|\ge2,\qquad \tau(H)\ge4,
\]

则

\[
|B(H)|\ge12.                                                   \tag{2}
\]

### 3.1 交叠图

构造交叠图 \(G\)，其五个 vertices 对应 \(H\) 的五个成员，两 vertices
相邻当且仅当对应集合相交。

`PROVED`：若 \(G\) 有两条 vertex-disjoint edges，各取一个交点，再从第五
成员取一点，就得到至多三点 transversal，违背 \(\tau(H)\ge4\)。故

\[
\nu(G)\le1.                                                    \tag{3}
\]

`PROVED`：matching number 至多一的 simple graph，其所有 edges 要么有
一个公共端点，要么恰位于一个 triangle 中。取两条相交 edges
\(uv,uw\)；任何不含 \(u\) 的 edge 只能是 \(vw\)，否则会与其中一条形成
two-edge matching。

### 3.2 星形情形

存在中心成员 \(E_0\)，其余四个成员 \(L_1,\ldots,L_4\) 两两不交。定义

\[
p_i=|L_i\setminus E_0|,\qquad
q_i=|L_i\cap E_0|,\qquad
c=\left|E_0\setminus\bigcup_iL_i\right|.
\]

于是

\[
p_i+q_i\ge2,\qquad c+\sum_iq_i=|E_0|\ge2.
\]

`PROVED`：minimal transversals 恰分成：

1. 每个 \(L_i\) 选一点，且至少一个所选点属于 \(E_0\)；
2. 从每个 \(L_i\setminus E_0\) 选一点，再选一个中心专属点。

所以

\[
|B(H)|
=\prod_i(p_i+q_i)-\prod_ip_i+c\prod_ip_i.                     \tag{4}
\]

`PROVED`：若 \(c\ge1\)，(4) 至少为
\(\prod_i(p_i+q_i)\ge16\)。

`PROVED`：若 \(c=0\) 且某个 \(q_i\ge2\)，则

\[
\prod_j(p_j+q_j)-\prod_jp_j
\ge q_i\prod_{j\ne i}(p_j+q_j)
\ge2\cdot2^3=16.
\]

`PROVED`：最后设所有 \(q_i\in\{0,1\}\)。令
\(h=\sum_iq_i\ge2\)。上述差关于各 \(p_i\) 单调不减，故最小值在
\(q_i=1\) 时 \(p_i=1\)、\(q_i=0\) 时 \(p_i=2\) 取得。对
\(h=2,3,4\)，下界依次为

\[
16-4=12,\qquad16-2=14,\qquad16-1=15.
\]

所以星形情形至少有十二个 blockers。

### 3.3 三角形情形

`PROVED`：此时 \(H\) 是三成员分量 \(K\) 与两个孤立成员
\(L_4,L_5\) 的不交并。因为

\[
\tau(H)=\tau(K)+2\ge4,
\]

有 \(\tau(K)\ge2\)。

`PROVED`：\(|B(K)|\ge3\)。private-witness bound 先给
\(|B(K)|\ge2\)。若恰为二，写 \(B(K)=\{A,B\}\)。由
\(\tau(K)\ge2\)，有 \(|A|,|B|\ge2\)。若 \(A\cap B\ne\varnothing\)，则
\(K=B(\{A,B\})\) 含 singleton member，矛盾；故 \(A,B\) 不交，于是
\(K\) 有 \(|A||B|\ge4\) 个 members，又与 \(|K|=3\) 矛盾。

`PROVED`：不交并的 blocker 是各 components blockers 的笛卡尔积，所以

\[
|B(H)|=|B(K)|\,|L_4|\,|L_5|\ge3\cdot2\cdot2=12.
\]

这证明 (2)。

## 4. admissible pair 的部分后果

`PROVED`（本角色候选）：若 \(a=5\)，对 \(H=\mathcal S\) 应用 (2)：

\[
|H|=5,\quad \min|H|\ge2,\quad
\tau(H)=\min_{C\in\mathcal C}|C|\ge4.
\]

所以

\[
b=|B(\mathcal S)|\ge12.                                       \tag{5}
\]

`PROVED`（本角色候选）：(5) 排除

\[
(5,4),\qquad(5,5),\qquad(5,6).
\]

结合冻结的 \(m(2,4)\ge9\)，总数九的唯一未决 split \((5,4)\) 被排除，
故本路线单独给出候选下界

\[
m(2,4)\ge10.
\]

`UNKNOWN`：本角色结果未经本 gate 两个 Referees 独立审查，不能单独更新
claims/status。

## 5. 乘积不等式的实际状态

`PROVED`：结合冻结结论

\[
b=2\Rightarrow a\ge16,\qquad
b=3\Rightarrow a\ge12,\qquad
a=4\Rightarrow b\ge16
\]

以及 (5)，产品不等式可能失败的情形只剩

\[
(a,b)=(6,4),(7,4),(6,5).                                     \tag{6}
\]

其余情形中：\(a\ge6,b\ge6\) 给 \(ab\ge36\)；
\(b=5,a\ge7\) 给 \(ab\ge35\)；\(b=4,a\ge8\) 给 \(ab\ge32\)。

`UNKNOWN`：本路线没有证明或反驳

\[
|\mathcal S||\mathcal C|\ge32.
\]

`UNKNOWN`：第一处缺失的解析步骤是把 incidence polynomial 约束提升为

\[
\begin{aligned}
b=4:\ &d_i\ge4\text{ 且 row separation}\Rightarrow Q_4(m)\ge8,\\
b=5:\ &d_i\ge4\text{ 且 row separation}\Rightarrow Q_5(m)\ge7.
\end{aligned}
\]

`COMPUTED`：本角色的单实现枚举支持这些不等式。

`REFUTED`：把该单实现枚举直接称为证明是不合法的；缺少独立可检查 certificate
和完整第二实现，而不是缺少任意 \(U\)、重复 pattern 或 multiplicity 的归约。

## 6. 六个 split 在本路线中的状态

| total | split | 本路线数学状态 | 本路线有限证据 |
|---:|---:|---|---|
| 9 | \((5,4)\) | `PROVED` 不存在 | `COMPUTED` 无命中 |
| 10 | \((6,4)\) | `UNKNOWN` | `COMPUTED` 无命中 |
| 10 | \((5,5)\) | `PROVED` 不存在 | `COMPUTED` 无命中 |
| 11 | \((7,4)\) | `UNKNOWN` | `COMPUTED` 无命中 |
| 11 | \((6,5)\) | `UNKNOWN` | `COMPUTED` 无命中 |
| 11 | \((5,6)\) | `PROVED` 不存在 | `COMPUTED` 无命中 |

```text
COUNTEREXAMPLE_TO_PRODUCT: NONE_FOUND
PRODUCT_INEQUALITY_STATUS_IN_THIS_ROUTE: UNKNOWN
NEW_PARTIAL_BOUND_IN_THIS_ROUTE: PROVED_CANDIDATE_m(2,4)>=10
FIRST_OPEN_SPLIT_IN_THIS_ROUTE: (6,4)
EXACT_m(2,4)_IN_THIS_ROUTE: UNKNOWN
GLOBAL_sat(7)>=47_IN_THIS_ROUTE: NOT_ESTABLISHED
```
