# P0054 G4.4 — Prover C：任意有限底集的精确 incidence-pattern 归约

```text
ROLE: COMPATIBILITY_PROVER_C
MODEL_PATH: dedicated prover role unavailable before material access; isolated compatible replacement
NETWORK: OFFLINE
REPOSITORY_WRITES_BY_ROLE: NONE
OTHER_G4_4_ROLE_OUTPUTS_READ: NONE
FORMALIZER: NOT_USED
```

## 1. 冻结输入

`COMPUTED`：本角色开始工作时独立复核了
`HEAD=d2c8e3eb81466a3743c736319ef1874920590abc`、Section 0、冻结文献包、
G4.3 候选证明、G4.3 stronger-local-parameter 说明以及 G4.3 实验三件套；
所见 SHA-256 与 Section 0 和 literature freeze manifest 一致。

`COMPUTED`：本角色用冻结的 G4.3 源码离线重放 totals 8、9、10，结构投影一致。
这只是同一实现重放，不是独立穷举证明。

## 2. 有限向量模型

`DEFINITION`：固定正整数 \(r,k,\ell,q\)。令
\([r]=\{1,\ldots,r\}\)。对每个非空 pattern
\(P\subseteq[r]\) 设置非负整数 multiplicity \(m_P\)，并定义

\[
D(m)=\{P:m_P>0\},\qquad
d_i(m)=\sum_{P\ni i}m_P.
\]

`DEFINITION`：令 \(\mathcal M(m)\) 为 supported patterns 的所有
inclusion-minimal covers：

\[
\mathcal M(m)=
\left\{
Q\subseteq D(m):
\bigcup_{P\in Q}P=[r],\
\forall P\in Q,\
\bigcup_{R\in Q\setminus\{P\}}R\ne[r]
\right\}.
\]

`DEFINITION`：定义

\[
W(m)=\sum_{Q\in\mathcal M(m)}\prod_{P\in Q}m_P.
\]

## 3. 精确归约定理

`PROVED`：以下两件事等价。

1. 存在有限普通 clutter \(H=\{H_1,\ldots,H_r\}\) 和
   \(K=B(H)\)，满足

   \[
   H=B(K),\qquad |K|=k,\qquad
   |H_i|\ge\ell,\qquad
   \min_{T\in K}|T|\ge q.
   \]

2. 存在整数向量 \(m\) 满足：

   - 对每个非空 \(P\subseteq[r]\)，\(0\le m_P\le k\)；
   - \(m_{[r]}=0\)；
   - 对每个 \(i\)，\(\ell\le d_i(m)\le k\)；
   - 对每个有序对 \(i\ne j\)，存在 \(P\in D(m)\) 使
     \(i\in P\) 且 \(j\notin P\)；
   - \(\min_{Q\in\mathcal M(m)}|Q|\ge q\)；
   - \(W(m)=k\)。

### 3.1 空侧与 inactive points

`PROVED`：可容许 pair 的两侧都非空。若一侧为空，则其 blocker 为
\(\{\varnothing\}\)，与相应的成员大小下界冲突；空底集也不能产生可容许
pair。

`PROVED`：令 \(A=\bigcup H\)。若 \(x\notin A\) 出现在 transversal
\(T\) 中，删除 \(x\) 不改变命中关系，所以 minimal transversal 不含
\(x\)。因此

\[
B_U(H)=B_A(H).
\]

由 \(K=B(H)\) 得 \(K\subseteq A\)。删除 \(U\setminus A\) 同时保持
两条 blocker 等式、成员大小和实际集合数。

### 3.2 private-witness 上界

`PROVED`：若 \(T\in B(H)\) 且 \(x\in T\)，minimality 给出某个
\(E_x\in H\)，使

\[
T\cap E_x=\{x\}.
\]

不同 \(x\) 对应不同 \(E_x\)，所以 \(|T|\le |H|\)。将它用于
\(H_i\in B(K)\)，得到

\[
|H_i|\le |K|=k.
\]

于是总 incidence 数

\[
\sum_i|H_i|\le rk,
\]

活跃点数不超过 \(rk\)，且每个非空 pattern 的 multiplicity 不超过
\(k\)。

### 3.3 incidence quotient 不丢失 multiplicity

`PROVED`：每个活跃点 \(x\) 由

\[
P(x)=\{i:x\in H_i\}\ne\varnothing
\]

刻画。同 pattern 的不同点通过真实整数 \(m_P\) 保留，没有合并成一个
点。反过来，由任意 \(m\) 构造

\[
U_m=\{(P,t):1\le t\le m_P\},\qquad
H_i=\{(P,t):i\in P\}.
\]

因此，在固定带标号 rows 后，multiplicity 向量恰好消去 column
permutation，同时保留重复 incidence pattern。

`PROVED`：条件

\[
\forall i\ne j\ \exists P\in D(m):
i\in P,\ j\notin P
\]

等价于 \(H_i\nsubseteq H_j\) 对所有有序对成立，因而恰好保证 rows
两两不同且不可比。空 incidence classes 被允许，row 大小也不要求均匀。

### 3.4 minimal transversals 的精确计数

`PROVED`：minimal transversal 不能包含两个同 pattern 点；否则删除其中
一个不改变任何命中关系。它的 pattern 集因此覆盖 \([r]\)，而每个所选点
的 private row 恰好说明该 cover inclusion-minimal。

`PROVED`：反过来，给定 \(Q\in\mathcal M(m)\)，从每个 \(P\in Q\)
选择一个真实点。每个 pattern 都有不被其余 patterns 覆盖的 private
row，所以所得点集是 minimal transversal。

`PROVED`：固定 \(Q\) 恰有

\[
\prod_{P\in Q}m_P
\]

个不同真实 minimal transversals。不同 \(Q\) 或不同真实点选择不会生成
同一集合。因此 \(W(m)=|B(H)|\) 是实际集合数，不是带重 tuple 数。

`PROVED`：每个 irredundant cover 至多含 \(r\) 个 patterns。给每个
pattern 选择一个 private row；同一 row 不可能同时是两个 patterns 的
private row。

### 3.5 blocker involution

`PROVED`：对有限非空 clutter \(H\)，有 \(B(B(H))=H\)。

每个 \(E\in H\) 命中所有 \(B(H)\)。若 \(A\subsetneq E\)，clutter 性保证
不存在 \(F\in H\) 满足 \(F\subseteq A\)，故 \(U\setminus A\) 命中
\(H\)，并包含一个与 \(A\) 不交的 minimal transversal；所以 \(A\)
不命中 \(B(H)\)。这证明每个 \(E\) 都是 \(B(H)\) 的 minimal
transversal。

反之，若 \(Z\in B(B(H))\) 不包含任何 \(E\in H\)，则
\(U\setminus Z\) 命中 \(H\)，其中含有一个与 \(Z\) 不交的
\(B(H)\) 成员，矛盾。因此 \(Z\) 包含某个 \(E\in H\)，再由
minimality 得 \(Z=E\)。

`PROVED`：3.1–3.5 同时给出必要性与充分性，所以本节归约是 iff，而不是
只保留必要条件的松弛。

## 4. 六个 split 的有限空间

`DEFINITION`：若取 \(H=S\)，则

\[
(r,k,\ell,q)=(a,b,2,4).
\]

若取 \(H=C\)，则

\[
(r,k,\ell,q)=(b,a,4,2).
\]

选择 rows 较少的一侧仅减少搜索维数；它不是 incidence matrix transpose，
也没有重复计算对偶。

| split \((a,b)\) | primary \(H\) | \((r,k,\ell,q)\) | 可变 proper nonempty patterns | incidence 范围 |
|---|---|---:|---:|---:|
| \((5,4)\) | \(C\) | \((4,5,4,2)\) | 14 | \(16\le I\le20\) |
| \((6,4)\) | \(C\) | \((4,6,4,2)\) | 14 | \(16\le I\le24\) |
| \((7,4)\) | \(C\) | \((4,7,4,2)\) | 14 | \(16\le I\le28\) |
| \((5,5)\) | \(S\) | \((5,5,2,4)\) | 30 | \(10\le I\le25\) |
| \((6,5)\) | \(C\) | \((5,6,4,2)\) | 30 | \(20\le I\le30\) |
| \((5,6)\) | \(S\) | \((5,6,2,4)\) | 30 | \(10\le I\le30\) |

`PROVED`：形式上有 \(2^r-1\) 个非空 patterns。因 \(q\ge2\)，full
pattern multiplicity 必须为零，否则其中任一点构成 singleton minimal
transversal。因此实际自由 patterns 为 14 或 30。

`PROVED`：row permutations 可用于取 \(S_r\)-orbit canonical
representative，但 symmetry pruning 不是归约正确性的依赖。不使用 symmetry
的 checker 仍可直接核验完整空间。

## 5. four-set lemma 的有限化

`PROVED`：候选四-set命题

\[
|H|=4,\quad \min_i|H_i|\ge4,\quad
\min_{T\in B(H)}|T|\ge2
\Longrightarrow |B(H)|\ge8
\]

已严格归约为有限命题。若它失败，令 \(k=|B(H)|\le7\)。
private-witness 上界给出

\[
4\le |H_i|\le k,
\]

故 \(k\in\{4,5,6,7\}\)。逐一检查
\((r,k,\ell,q)=(4,k,4,2)\) 的 14-variable boxes 即充分。

`UNKNOWN`：本角色没有给出不依赖穷举证书的 four-set 组合证明，也没有证明
\(|S||C|\ge32\)。

## 6. 计算边界与第一缺口

`COMPUTED`：冻结 G4.3 搜索与本角色同源重放只支持 totals 8、9、10。
因此它们不能证明任何 total-11 split。

`COMPUTED`：G4.3 中的两个 blocker validators 独立检查 blocker 语义和
潜在 SAT witness，但没有独立遍历完整 multiplicity 空间；它们不构成第二个
完整穷举实现。

`UNKNOWN`：现有 coverage counters 不是 proof certificate，因为它们没有
记录一棵可由独立 checker 重建且完整覆盖所有 multiplicity assignments 的
排除树。

```text
FIRST_MISSING_STEP_OF_A_COMPUTATION_BASED_EXACT_12_ARGUMENT:
  prove or independently certify that all six finite vector spaces are empty

FINITE_REDUCTION: PROVED
ALL_SIX_SPLITS_CERTIFIED_UNSAT: NO
EXACT_m(2,4): UNKNOWN_IN_THIS_REPORT
```

`PROVED`（条件结论）：若六个 finite spaces 都有独立可检查的完整
exhaustion/UNSAT 证书，并由完整第二实现复验，则本报告的 iff 归约足以把
六个 split 的排除升级为 `PROVED`。当前本报告不满足该条件。

## 7. 可接受证书的最低接口

`DEFINITION`：可独立检查的 UNSAT 证书至少需要：

- 固定 \((r,k,\ell,q)\) 与 pattern ordering；
- branch 子域严格、无重叠地覆盖父域；
- 每个 leaf 给出 checker 可重算的失败谓词；
- 对 partial \(W>k\) 与 small-cover prune，由 checker 自行重算精确整数值；
- symmetry prune 附实际 row permutation，或由 checker 独立重算 canonical
  representative；
- 固定 root hash、leaf count、源码、命令、运行时与输出哈希；
- 或由确定性 encoder 生成 CNF，再由独立 LRAT/DRAT checker 核验。

`DEFINITION`：完整第二实现必须独立遍历全部有限空间，例如：

- 不依赖 symmetry 的 multiplicity DFS，加可检查排除树；以及
- 独立 CNF/ILP 编码与证书，或不同语言的完整枚举器。

同一程序重跑、同一 pruning 代码的包装、或只验证小底集 blocker 语义，都不
满足这一要求。
