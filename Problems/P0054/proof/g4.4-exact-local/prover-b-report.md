# P0054 G4.4 — 隔离 Prover B 报告

```text
ROLE: COMPATIBILITY_PROVER_B
MODEL_PATH: dedicated prover role failed before material access; isolated compatible replacement
NETWORK: OFFLINE
REPOSITORY_WRITES_BY_ROLE: NONE
OTHER_G4_4_ROLE_OUTPUTS_READ_OR_CONTACTED: NONE
FORMALIZER: NOT_USED
RESULT: PROVED_CANDIDATE_PENDING_MAIN_RECONSTRUCTION_AND_REFEREES
```

## 1. 冻结输入与结论

`COMPUTED`：研究前后
`HEAD=d2c8e3eb81466a3743c736319ef1874920590abc`。AGENTS、Section 0、
frozen subproblem、四份 literature 输入、G4.3 candidate proof 与
stronger-local-parameter 的 SHA-256 均保持冻结值。角色未联网、未写文件，
结束时 `git diff --check` 通过。

`PROVED`（本角色候选）：对任意有限 \(U\)，每个 admissible
\((2,4)\) mutual-blocker pair \((\mathcal S,\mathcal C)\) 都满足

\[
|\mathcal S||\mathcal C|\ge32.
\]

`PROVED`（本角色候选）：

\[
m(2,4)=12.
\]

`PROVED`（相对于冻结 G4.3 canonical-layer 接口的本角色候选）：

\[
(|A_0|,\ldots,|A_6|)
\ge(1,6,12,9,12,6,1),\qquad sat(7)\ge47.
\]

`UNKNOWN`：\(sat(7)\) 的精确值、外部新颖性和优先权。

## 2. 基础引理

`DEFINITION`：\(B(\mathcal H)\) 是有限 family \(\mathcal H\) 的
inclusion-minimal transversals。

`LITERATURE`：有限 clutter 满足 blocker involution：

\[
B(B(\mathcal H))=\mathcal H.
\]

`PROVED`（private-witness lemma）：若 \(T\in B(\mathcal H)\)，则对每个
\(x\in T\)，存在 \(E_x\in\mathcal H\) 使

\[
T\cap E_x=\{x\}.
\]

不同 \(x\) 的 witnesses 不同，故

\[
|T|\le|\mathcal H|.
\]

`PROVED`（三-blocker 辅助引理）：若 clutter \(\mathcal K\) 至多有五个
成员、每个成员大小至少三，且 \(B(\mathcal K)\) 无 singleton，则

\[
|B(\mathcal K)|\ge4.
\]

private-witness lemma 先给 \(|B(\mathcal K)|\ge3\)。若恰为三，记
\(B(\mathcal K)=\{D_1,D_2,D_3\}\)。每个 \(D_i\) 大小至少二；又因为
\(B(B(\mathcal K))=\mathcal K\) 的成员均至少三，这三个 \(D_i\) 不存在
二点 transversal。若两个 \(D_i\) 相交，交点加第三个集合任一点就是至多
二点 transversal，矛盾。因此三个 \(D_i\) 两两不交，任选
\(d_i\in D_i\) 产生至少 \(2^3=8\) 个不同 minimal transversals，即
\(|\mathcal K|\ge8\)，与 \(|\mathcal K|\le5\) 矛盾。

## 3. Prover B 的四集合证明

设

\[
\mathcal C=\{C_1,C_2,C_3,C_4\},\qquad |C_i|\ge4,
\]

且 \(B(\mathcal C)\) 无 singleton。对点 \(x\) 令 \(d(x)\) 为包含
\(x\) 的 \(C_i\) 数目。

`PROVED`：不存在 \(d(x)=4\)，否则 \(\{x\}\in B(\mathcal C)\)。

### 3.1 存在三重 incidence

不妨 \(x\in C_1,C_2,C_3\) 且 \(x\notin C_4\)。

`PROVED`：对每个 \(y\in C_4\)，\(\{x,y\}\) 是 minimal transversal。
删除 \(y\) 后漏掉 \(C_4\)；删除 \(x\) 后，由无 singleton 假设，\(y\)
至少漏掉前三个集合之一。因此得到至少四个含 \(x\) 的 blocker。

令

\[
\mathcal C^{-x}=\{C_i\setminus\{x\}:1\le i\le4\},
\]

并取 inclusion-minimal clutter reduction \(\mathcal K\)。

`PROVED`：\(\mathcal K\) 至多四个成员、每个大小至少三，且
\(B(\mathcal K)\) 无 singleton。三-blocker 辅助引理给出至少四个避开
\(x\) 的 blocker；它们也正是原 family 中避开 \(x\) 的 minimal
transversals。总数至少八。

### 3.2 无三重 incidence，但存在一次 incidence

不妨 \(x\) 只属于 \(C_1\)。

`PROVED`：\(C_2,C_3,C_4\) 没有公共点，否则出现三重 incidence。冻结
G4.3 三集合定理给

\[
|B(\{C_2,C_3,C_4\})|\ge12.
\]

若其中 \(T\) 命中 \(C_1\)，保留 \(T\)；否则映为 \(T\cup\{x\}\)。
因为 \(x\) 不属于后三个集合，该映射保持所有原 private witnesses；
新增 \(x\) 以 \(C_1\) 为 private witness，且映射单射。因此原四集合
family 至少有十二个 blocker。

### 3.3 所有相关点恰有二重 incidence

`PROVED`：实际点构成四个 labels 上的 loopless multigraph；
\(x_{ij}\) 是 pattern \(\{i,j\}\) 的实际点数。每个 label 的 weighted
degree 至少四。

`PROVED`：minimal transversals 正是 minimal edge covers。它们或者是
两条边组成的 perfect matching，或者是三条边组成的 \(K_{1,3}\)。故实际
blocker 数为

\[
\begin{aligned}
F={}&x_{12}x_{34}+x_{13}x_{24}+x_{14}x_{23}\\
 &+x_{12}x_{13}x_{14}
  +x_{12}x_{23}x_{24}
  +x_{13}x_{23}x_{34}
  +x_{14}x_{24}x_{34}.
\end{aligned}
\]

每个乘积逐一选择不同实际点，所以这里计数的是实际 subsets。

`PROVED`：正 support graph 无孤立点；按同构分成以下七类。

| support | 整数下界 |
|---|---:|
| \(2K_2\) | 两条权重均至少四，\(F\ge16\) |
| \(P_4\) | 两条 endpoint edges 均至少四，\(F\ge16\) |
| \(K_{1,3}\) | 三条 leaf edges 均至少四，\(F\ge64\) |
| \(C_4\) | 全权重至少二时两 perfect-match products 之和至少八；若某权重为一，其两邻边均至少三，仍至少八 |
| paw | pendant 权重 \(t\ge4\)，且 \(F=t(c+ab)\ge8\) |
| \(K_4-e\) | \(F\ge(b+d)(c+e)\ge16\) |
| \(K_4\) | 全一时 \(F=7\)；weighted degree 至少四迫使某权重增加，最小增量至少三 |

三种 incidence 情形穷尽任意有限 \(U\)，故

\[
|B(\mathcal C)|\ge8.
\]

`REFUTED`（本路线的首个失败尝试）：删去三重 incidence 点 \(x\) 后，不能
直接把未改变的 \(C_4\) 当成 reduced clutter 的成员并对它使用
private-witness lemma；\(C_4\) 可能变为 redundant。

`PROVED`：正确修复是先取 \(\mathcal K\)，再只使用“至多四个成员、每个
大小至少三、blocker 无 singleton”的三-blocker 辅助引理。

## 4. 五生成集定理

`PROVED`：若

\[
\mathcal S=\{S_1,\ldots,S_5\},\qquad |S_i|\ge2,
\]

且每个 transversal 大小至少四，则

\[
|B(\mathcal S)|\ge8.
\]

若一点属于三个 \(S_i\)，再从剩余至多两个集合各取一点，会产生至多三点
transversal。因此每点最多属于两个 \(S_i\)。

令交图 \(G\) 的 vertices 为五个 \(S_i\)。若 \(G\) 有两条
vertex-disjoint edges，取两交点，再从第五个集合取一点，同样产生至多三点
transversal。因此 \(G\) 的 matching number 至多一；它只能是空图、星或
三角形，加任意孤立 vertices。

- `PROVED`：空图时五集合两两不交，逐集合选一点给至少
  \(2^5=32\) 个 minimal transversals。
- `PROVED`：星中固定一个 center–leaf 交点，再从另外三个 pairwise
  disjoint leaves 各选一点，给至少 \(2^3=8\) 个不同 minimal
  transversals。
- `PROVED`：三角形中固定一个 \(S_1\cap S_2\) 点，再分别从
  \(S_3,S_4,S_5\) 取一点，给至少 \(2^3=8\) 个不同 minimal
  transversals。incidence degree 至多二保证固定点仍有 private witness。

## 5. 六生成集定理

`PROVED`：若

\[
\mathcal S=\{S_1,\ldots,S_6\},\qquad |S_i|\ge2,
\]

且每个 transversal 大小至少四，则

\[
|B(\mathcal S)|\ge6.
\]

一点最多属于三个 \(S_i\)。若 \(x\) 恰属于三个，不妨为前三个，则后三个
必须两两不交；否则 \(x\)、一个交点及第三集合一点给出至多三点
transversal。每个

\[
\{x,y_4,y_5,y_6\},\qquad y_i\in S_i,
\]

都是四点 transversal，且因不存在三点 transversal 而自动 minimal。后三个
集合两两不交，所以得到至少 \(2^3=8\) 个不同 blockers。

以下设每点属于一个或两个 \(S_i\)，并把实际点表示为六 vertices 上的带环
多重图。loops 覆盖一个 vertex，nonloop edges 覆盖两个；每个 vertex 的
实际 incidence degree 至少二。三个点能覆盖六 vertices 当且仅当它们是三个
两两不交的 nonloop edges。因此 nonloop support graph 的 matching number
\(\nu\le2\)。

### 5.1 \(\nu=0,1\)

- `PROVED`：\(\nu=0\) 时只有 loops。每 vertex 至少两个 loop choices，
  所以至少 \(2^6=64\) 个 minimal covers。
- `PROVED`：\(\nu=1\) 时 nonloop support 是星或三角形。星中固定一个
  center–leaf actual edge，再从其余四 vertices 各取一个 incident point；
  这些选择互不重合并给至少 \(2^4=16\) 个 minimal covers。三角形中固定
  两条相邻 actual edges；其余三个孤立 vertices 各有至少两个 loops，
  给至少 \(2^3=8\) 个 minimal covers。

### 5.2 \(\nu=2\) 的完整量化

`DEFINITION`：取两个 support-disjoint 的 nonloop supports \(E_1,E_2\)。
令 \(P_i\) 是具有 support \(E_i\) 的所有实际点，\(m_i=|P_i|\ge1\)；
令 \(u,v\) 为其余两个 vertices。

`PROVED`：不存在 support \(\{u,v\}\)，否则与 \(E_1,E_2\) 组成
three-edge matching。

对

\[
e_i\in P_i,\qquad p\ni u,\qquad q\ni v
\]

定义

\[
F(e_1,e_2,p,q)=\{e_1,e_2,p,q\}.
\]

`PROVED`：四个实际点两两不同，并组成四点 edge cover。它必定
inclusion-minimal；否则删除一点得到 three-point cover，而这只能是
three-edge matching。

`PROVED`：固定 \(E_1,E_2\) 后，四元组可由所得 subset 唯一恢复，所以生成

\[
m_1m_2d(u)d(v)
\]

个不同 minimal covers。若该数至少六即完成。若小于六，整数条件
\(m_i\ge1,d(u),d(v)\ge2\) 迫使

\[
m_1=m_2=1,\qquad d(u)=d(v)=2. \tag{1}
\]

固定唯一实际点 \(e_i\in P_i\)，记 \(M=\{e_1,e_2\}\)。上述
\(\mathcal F_M\) 恰有四个成员。

#### 第二个 actual matching 存在

令 \(N=\{f_1,f_2\}\ne M\) 为第二个 actual two-edge matching。用其两个
unmatched vertices 的 incident points 同样构造 \(\mathcal F_N\)，故
\(|\mathcal F_N|\ge4\)。

`PROVED`：

\[
|\mathcal F_M\cap\mathcal F_N|\le2.
\]

若 \(M,N\) 不共享 actual point，共同成员必须等于四点集 \(M\cup N\)，所以
至多一个。若恰共享一个，写

\[
M=\{e,f\},\qquad N=\{e,g\}.
\]

若 \(f,g\) support-disjoint，则 \(e,f,g\) 是 three-edge matching，矛盾。
若它们相交一个 vertex，三点 \(e,f,g\) 覆盖五个 vertices；共同生成成员
的第四点必须 incident with 唯一遗漏 vertex，而该 vertex 是 \(M\) 的
unmatched vertex，由 (1) 至多有两个选择。若 \(f,g\) 是不同 parallel
actual points，则一个额外 support 若覆盖余下两个 vertices，立即产生
three-edge matching，所以交为空。

因此

\[
|\mathcal F_M\cup\mathcal F_N|\ge4+4-2=6.
\]

#### \(M\) 是唯一 actual matching

`PROVED`：所有 incident with \(u\) 或 \(v\) 的实际点都是 loops。若
nonloop \(p\) 从 \(u\) 连到 \(E_1\) 的 vertex，则 \(\{p,e_2\}\) 是第二
matching；连到 \(E_2\) 时与 \(e_1\) 构成第二 matching；连到 \(v\) 时
产生 perfect matching。结合 (1)，\(u,v\) 各恰有两个不同 loops。

写

\[
E_1=\{a,b\},\qquad E_2=\{c,d\}.
\]

由 \(d(a),d(b)\ge2\)，分别选

\[
r_a\ne e_1,\ a\in\sigma(r_a),\qquad
r_b\ne e_1,\ b\in\sigma(r_b).
\]

它们的 supports 位于 core \(\{a,b,c,d\}\)。并且 \(r_a\ne r_b\)；
否则其 support 是 \(\{a,b\}\)，与 \(e_2\) 构成第二 actual matching。
所以

\[
\{r_a,r_b,e_2\}
\]

覆盖 core。取其中一个 inclusion-minimal core cover \(K\)。
它避开 \(e_1\)。

对 \(u,v\) 的两个 loop choices \(\ell_u^i,\ell_v^j\)，四个集合

\[
K\cup\{\ell_u^i,\ell_v^j\},\qquad i,j\in\{1,2\},
\]

都是 minimal edge covers：\(K\) 的每点在 core 中保留 private vertex，
两个 loops 分别以 \(u,v\) 为 private vertices。它们两两不同且都避开
\(e_1\)，而 \(\mathcal F_M\) 的四个成员全含 \(e_1\)。因此共有至少八个。

`REFUTED`（局部补强前的第一失效步骤）：从 \(e_1=\{a,b\}\) 的一个端点
任选额外 incident point 并直接替换 \(e_1\)，未必覆盖另一个端点，不能直接
断言得到 edge cover。

`PROVED`：修复是分别选择 \(r_a,r_b\)，先覆盖完整 core，再在有限集合中取
inclusion-minimal core cover \(K\)。

这闭合 \(\nu=2\)，也闭合六生成集定理。

## 6. 乘积不等式与六个 split

令

\[
a=|\mathcal S|,\qquad b=|\mathcal C|.
\]

`PROVED`：private-witness lemma 给 \(a\ge4,b\ge2\)。以下情形穷尽：

| 情形 | 下界 | 乘积 |
|---|---:|---:|
| \(b=2\) | 冻结 G4.3 两集合论证给 \(a\ge16\) | \(ab\ge32\) |
| \(b=3\) | 冻结 G4.3 三集合定理给 \(a\ge12\) | \(ab\ge36\) |
| \(b=4\) | 本报告四集合定理给 \(a\ge8\) | \(ab\ge32\) |
| \(b\ge5,a=4\) | 冻结 G4.3 四生成集论证给 \(b\ge16\) | \(ab\ge64\) |
| \(b\ge5,a=5\) | 五生成集定理给 \(b\ge8\) | \(ab\ge40\) |
| \(b\ge5,a=6\) | 六生成集定理给 \(b\ge6\) | \(ab\ge36\) |
| \(b\ge5,a\ge7\) | 整数算术 | \(ab\ge35\) |

所以

\[
|\mathcal S||\mathcal C|\ge32.
\]

`PROVED`：完全用整数算术，

\[
(a+b)^2=(a-b)^2+4ab\ge128.
\]

若 \(a+b\le11\)，则左侧不超过 \(121<128\)，矛盾。因此

\[
a+b\ge12.
\]

六个 frozen split 均被排除：

| split | 状态 | 纯组合理由 |
|---|---|---|
| \((5,4)\) | `REFUTED` | \(b=4\Rightarrow a\ge8\) |
| \((6,4)\) | `REFUTED` | 同上 |
| \((5,5)\) | `REFUTED` | \(a=5\Rightarrow b\ge8\) |
| \((7,4)\) | `REFUTED` | \(b=4\Rightarrow a\ge8\) |
| \((6,5)\) | `REFUTED` | \(a=6\Rightarrow b\ge6\) |
| \((5,6)\) | `REFUTED` | \(a=5\Rightarrow b\ge8\) |

## 7. 十二成员 witness 与全局推论

`DEFINITION`：

\[
U=\{a_0,a_1,a_2,a_3,b_0,b_1,b_2,b_3\}.
\]

\(\mathcal S\) 是两个不交四环的八条边。令

\[
A_0=\{a_0,a_2\},\quad A_1=\{a_1,a_3\},\quad
D_0=\{b_0,b_2\},\quad D_1=\{b_1,b_3\},
\]

并令

\[
\mathcal C=\{A_i\cup D_j:i,j\in\{0,1\}\}.
\]

`PROVED`：四环的 inclusion-minimal vertex covers 恰为两个
bipartition classes；不交 components 的 minimal transversals 是各
component minimal transversal 的并。因此

\[
B(\mathcal S)=\mathcal C.
\]

`PROVED`：任一 \(\mathcal C\)-transversal 若同时遇到 \(A_0,A_1\)，就
包含第一四环的一条边；否则被迫同时遇到 \(D_0,D_1\)，就包含第二四环的
一条边。八条边本身均为 minimal transversals，所以

\[
B(\mathcal C)=\mathcal S.
\]

成员大小分别至少二和四，总数 \(8+4=12\)。与下界结合，

\[
m(2,4)=12.
\]

`COMPUTED`：按 bits \(0,\ldots,7\) 编码：

```text
S = 03 06 09 0c 30 60 90 c0
C = 55 5a a5 aa
```

独立 powerset blocker engine 与 edge-choice/minimization engine 均返回
\(B(S)=C\)、\(B(C)=S\)、\(B(B(S))=S\)。

`PROVED`（相对于冻结 G4.3 layer recognition）：局部定理同时给

\[
|A_2|,|A_4|\ge12.
\]

与其余五层的冻结下界相加：

\[
1+6+12+9+12+6+1=47.
\]

所以候选全局下界是

\[
sat(7)\ge47.
\]

本角色没有更新 `status.md` 或 `claims.yaml`；仍须主 Agent 重建和两份
隔离 Referee `ACCEPT`。
