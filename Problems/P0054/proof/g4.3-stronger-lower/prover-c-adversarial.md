# P0054 G4.3 Prover C 兼容隔离反向攻击报告

```text
RUN_MODE: STRONGER_GLOBAL_LOWER_BOUND_DISCOVERY
CURRENT_GATE: P0054_G4_3_EIGHT_MEMBER_LAYER_EXCLUSION
ROLE: OFFLINE_COMPATIBILITY_PROVER_C
STANCE: ASSUME_THE_CANDIDATE_FALSE_AND_FIND_THE_FIRST_FAILURE
NETWORK: OFFLINE; NOT_USED
FORMALIZER: FORBIDDEN; NOT_USED
REPOSITORY_WRITES: NONE
ATTACK_VERDICT: PROVED
FIRST_INVALID_STEP: NONE
```

## 1. 冻结边界

`COMPUTED`：只读校验得到以下 SHA-256，全部与任务冻结值逐字节相符。

| 文件 | SHA-256 |
|---|---|
| `AGENTS.md` | `5ec4fe8a019a5c52efe2a382989d58782abfc6242240f77f9a0f5f8a7a39f4c1` |
| `section0-freeze.md` | `759e7b6a2bbad8853f2baa7424c8b19ac06e6ecaf07b3c3758a30d57a9a99aaf` |
| `frozen-subproblem.md` | `cc64e1e376196355b68266abcfdf228d38836b6fc05c170204397efc67a8ddaa` |
| G4.2 `candidate-proof.md` | `ef87bce75e3db5a8a46d99318c6b4c5e8bc769f33ef61be4e6adee55372c5a1e` |
| G4 `candidate-proof.md` | `9e0821e821458ee390d809d03e5fd927ae661222b4712c2c679b02a26d6ed448` |

`DEFINITION`：没有读取其他 G4.3 Agent 输出，没有联网，没有调用 Formalizer，没有写入仓库。

## 2. 结论

`PROVED`：对任意有限集合 \(U\)，每个 admissible \((2,4)\) blocker pair
\((\mathcal S,\mathcal C)\) 都满足

\[
|\mathcal S|+|\mathcal C|\ge 9.
\]

因此

\[
m(2,4)\ge 9.
\]

`PROVED`（相对于冻结 G4/G4.2 全局依赖）：第二层和第四层分别满足

\[
|A_2|\ge 9,\qquad |A_4|\ge 9,
\]

从而

\[
\operatorname{sat}(7)\ge 41.
\]

没有发现反例或无效推理步骤。

## 3. Blocker 基础引理

### 3.1 空侧排除

`PROVED`：admissible pair 的两侧都非空。

若 \(\mathcal C=\varnothing\)，则按冻结约定

\[
\mathcal S=B(\varnothing)=\{\varnothing\},
\]

但其唯一成员大小为零，违反 \(|S|\ge2\)。交换两侧同理：若
\(\mathcal S=\varnothing\)，则
\(\mathcal C=\{\varnothing\}\)，违反 \(|C|\ge4\)。

### 3.2 Private-witness 引理

`PROVED`：若有限族 \(\mathcal H\) 的 blocker 中含有
\(T\in B(\mathcal H)\)，则对每个 \(x\in T\)，存在
\(E_x\in\mathcal H\) 满足

\[
T\cap E_x=\{x\}.
\]

证明：\(T\setminus\{x\}\) 不是 transversal，否则 \(T\) 不具 inclusion-minimality。因此存在 \(E_x\in\mathcal H\) 与
\(T\setminus\{x\}\) 不交。另一方面 \(T\) 是 transversal，故
\(T\cap E_x\ne\varnothing\)，于是交集只能是 \(\{x\}\)。

`PROVED`：不同的 \(x,y\in T\) 必有 \(E_x\ne E_y\)，否则同一交集同时等于
\(\{x\}\) 和 \(\{y\}\)。所以

\[
|T|\le|\mathcal H|.
\]

### 3.3 Blocker recognition

`PROVED`：设 \(\mathcal G\) 是 clutter。若

1. 每个 \(G\in\mathcal G\) 都是 \(\mathcal H\) 的 transversal；
2. 每个 \(\mathcal H\) 的 transversal 都包含某个 \(G\in\mathcal G\)；

则

\[
\mathcal G=B(\mathcal H).
\]

证明：若 \(G_0\in\mathcal G\) 有真子集仍是 transversal，该真子集按条件 2 包含某个 \(G_1\in\mathcal G\)，于是
\(G_1\subsetneq G_0\)，与 clutter 性矛盾。故每个 \(G_0\) 都是 minimal transversal。反过来，每个 minimal transversal 包含某个 \(G_0\)，其 minimality 迫使两者相等。

## 4. Split 的初步压缩

记

\[
a=|\mathcal S|,\qquad b=|\mathcal C|.
\]

`PROVED`：由两侧非空，可任选 \(C\in\mathcal C\)。Private-witness 引理给出

\[
4\le |C|\le a,
\]

所以 \(a\ge4\)。同理任选 \(S\in\mathcal S\)，得到

\[
2\le |S|\le b,
\]

所以 \(b\ge2\)。

`PROVED`：若 \(a+b=8\)，只剩

\[
(a,b)=(6,2),(5,3),(4,4).
\]

下面的证明同时排除所有 \(a+b\le8\)，不需要导入先前的
\(m(2,4)\ge8\)。

## 5. 两集合 blocker：排除 \(b=2\)

设

\[
\mathcal C=\{C_1,C_2\}.
\]

`PROVED`：\(C_1\cap C_2=\varnothing\)。否则任取
\(x\in C_1\cap C_2\)，单点集 \(\{x\}\) 是 minimal transversal，因而属于
\(\mathcal S=B(\mathcal C)\)，违反所有 \(S\) 的大小至少为二。

`PROVED`：对任意 \(x\in C_1\)、\(y\in C_2\)，集合
\(\{x,y\}\) 是 minimal transversal。两集合不交保证删除 \(x\) 后漏掉
\(C_1\)，删除 \(y\) 后漏掉 \(C_2\)。不同的有序选择给出不同的二元集合。因此

\[
a=|B(\mathcal C)|
 \ge |C_1||C_2|
 \ge4\cdot4
 =16.
\]

所以 \(b=2\) 时不可能有 \(a+b\le8\)，特别排除了 \((6,2)\)。

## 6. 三集合 blocker 的精确 incidence-pattern 计数

设

\[
\mathcal C=\{C_1,C_2,C_3\}.
\]

### 6.1 Incidence classes

`PROVED`：三重交为空。否则三重交中的点形成 singleton minimal transversal，违反 \(|S|\ge2\)。

去掉不属于任何 \(C_i\) 的点；这种点不可能属于 minimal transversal。把
\(C_1\cup C_2\cup C_3\) 分成六个 incidence classes：

\[
X_1,X_2,X_3,X_{12},X_{13},X_{23},
\]

并记其大小为

\[
x,y,z,p,q,r.
\]

这里例如 \(X_{12}\) 表示恰好属于 \(C_1,C_2\) 而不属于 \(C_3\) 的点。非均匀大小和重复 incidence pattern 均由这些任意非负整数保留。

成员大小条件等价于

\[
x+p+q\ge4,\qquad
y+p+r\ge4,\qquad
z+q+r\ge4. \tag{1}
\]

### 6.2 所有 minimal transversals

`PROVED`：private-witness 引理给出每个
\(T\in B(\mathcal C)\) 满足 \(|T|\le3\)，而 admissibility 给出
\(|T|\ge2\)。

`PROVED`：二元 minimal transversals 恰来自以下六类配对：

\[
(X_1,X_{23}),\ (X_2,X_{13}),\ (X_3,X_{12}),
\]
\[
(X_{12},X_{13}),\ (X_{12},X_{23}),\ (X_{13},X_{23}).
\]

`PROVED`：三元 minimal transversals 恰好由
\(X_1,X_2,X_3\) 各取一点组成。若三元 minimal transversal 中某点同时属于两个 \(C_i\)，private witnesses 的三个不同 witness 边便不能分别只与三个点相交；等价地，其中至少一个点可删除。反向则每个纯类点都有自己的唯一被击中集合，所以三元组确为 minimal。

因此得到精确计数

\[
|B(\mathcal C)|
=xr+yq+zp+pq+pr+qr+xyz. \tag{2}
\]

### 6.3 下界十二

`PROVED`：若 \(p\ge3\)，则每个 \(X_{12}\) 中的点和每个
\(C_3\) 中的点组成一个不同的 minimal transversal，故已有

\[
p|C_3|\ge3\cdot4=12
\]

个。对 \(q\ge3\) 或 \(r\ge3\) 完全同理。

剩下只需考虑

\[
0\le p,q,r\le2.
\]

由 (1)，

\[
x\ge4-p-q,\quad
y\ge4-p-r,\quad
z\ge4-q-r. \tag{3}
\]

`PROVED`：式 (2) 对 \(x,y,z\) 分别单调不减，因此可把它们替换为
(3) 的下界。令替换后的值为 \(F(p,q,r)\)。以下三个矩阵的行依次是
\(q=0,1,2\)，列依次是 \(r=0,1,2\)：

\[
p=0:\quad
\begin{pmatrix}
64&40&24\\
40&25&16\\
24&16&12
\end{pmatrix},
\]

\[
p=1:\quad
\begin{pmatrix}
40&25&16\\
25&17&13\\
16&13&12
\end{pmatrix},
\]

\[
p=2:\quad
\begin{pmatrix}
24&16&12\\
16&13&12\\
12&12&12
\end{pmatrix}.
\]

每项均由 (2) 的整数代入直接得到，且每项至少为十二。因此

\[
|B(\mathcal C)|\ge12.
\]

故 \(b=3\) 时 \(a\ge12\)，排除了所有 \(a+b\le8\)，特别排除了
\((5,3)\)。

## 7. 四对四 split

现在设

\[
a=b=4,\qquad
\mathcal S=\{S_1,S_2,S_3,S_4\},\quad
\mathcal C=\{C_1,C_2,C_3,C_4\}.
\]

`PROVED`：每个 \(C_j\) 恰有四个点。其大小下界为四，而
\(C_j\in B(\mathcal S)\) 和 private-witness 引理给出
\(|C_j|\le|\mathcal S|=4\)。

固定 \(j\)。对每个 \(x\in C_j\)，选择满足
\(C_j\cap S_i=\{x\}\) 的 private witness。四个不同的 \(x\) 使用四个不同的 \(S_i\)，因此这是两个四元集合间的双射。

`PROVED`：于是对每个 \(i\)，

\[
C_j\cap S_i
\]

都是 singleton，且固定 \(j\) 时这四个 singleton 两两不同。特别地，
\(C_j\) 中没有点同时属于两个不同的 \(S_i\)。

`PROVED`：四个 \(S_i\) 两两不交。若
\(y\in S_i\cap S_k\) 且 \(i\ne k\)，由
\(S_i\in B(\mathcal C)\) 的 minimality，\(y\) 有某个 private witness
\(C_j\)，所以 \(y\in C_j\)。这与固定 \(C_j\) 内
\(S_i,S_k\) 的交点必须是不同 singleton 矛盾。

`PROVED`：从每个 \(S_i\) 中任选一点 \(x_i\)。由于四个 \(S_i\) 两两不交，

\[
\{x_1,x_2,x_3,x_4\}
\]

是 minimal transversal：删除 \(x_i\) 后 \(S_i\) 未被击中。不同选择产生不同集合。因此

\[
|B(\mathcal S)|
\ge\prod_{i=1}^{4}|S_i|
\ge2^4
=16.
\]

但 \(B(\mathcal S)=\mathcal C\) 只有四个成员，矛盾。故 \((4,4)\) 不存在。

## 8. 局部定理闭合

`PROVED`：若 \(a+b\le8\)，由 \(a\ge4,b\ge2\)：

- \(b=2\) 时 \(a\ge16\)；
- \(b=3\) 时 \(a\ge12\)；
- \(b=4\) 时只能 \(a=4\)，而四对四 split 已被排除；
- \(b\ge5\) 时自动有 \(a+b\ge9\)。

因此不存在总成员数至多八的 admissible pair，即

\[
m(2,4)\ge9.
\]

| \(a+b=8\) split | 结论 | 原因 |
|---|---|---|
| \((6,2)\) | `REFUTED` | 两集合 blocker 至少有 \(16\) 个成员 |
| \((5,3)\) | `REFUTED` | 三集合精确 incidence 计数至少为 \(12\) |
| \((4,4)\) | `REFUTED` | private witnesses 迫使四个 \(S_i\) 两两不交，继而产生至少 \(16\) 个 blocker |

## 9. \(A_2\) mutual-blocker 接口

设 \(\mathcal S\) 为 \(A_2\) 的 small members。对每个 large member
\(K\cup H\)，令

\[
C=U\setminus K,
\]

并由这些 \(C\) 组成 \(\mathcal C\)。

`PROVED`（冻结 G4 大小接口）：

\[
|S|\ge2,\qquad |C|\ge4.
\]

`PROVED`：\(\mathcal S,\mathcal C\) 都是 clutters。small members 的 clutter 性来自层 antichain；large traces 的 antichain 性在取补后仍保留。

`PROVED`：每个 \(S\) 与每个 \(C\) 相交。若
\(S\cap C=\varnothing\)，则 \(S\subseteq K\)，于是

\[
S\subsetneq K\cup H,
\]

与同一 canonical layer 的 antichain 性矛盾。

冻结 oriented cover 对每个 \(R\subseteq U\) 给出

\[
(\exists S\in\mathcal S,\ S\subseteq R)
\quad\text{或}\quad
(\exists C\in\mathcal C,\ R\subseteq U\setminus C). \tag{4}
\]

`PROVED`：\(\mathcal S=B(\mathcal C)\)。每个 \(S\) 是
\(\mathcal C\) 的 transversal。若 \(R\) 是任意
\(\mathcal C\)-transversal，则它不可能包含于任何 \(U\setminus C\)。
由 (4)，它必包含某个 \(S\)。应用 recognition 引理。

`PROVED`：\(\mathcal C=B(\mathcal S)\)。每个 \(C\) 都击中所有
\(S\)。若 \(D\) 是任意 \(\mathcal S\)-transversal，令
\(R=U\setminus D\)。此时没有 \(S\subseteq R\)，故 (4) 给出某个

\[
R\subseteq U\setminus C,
\]

等价于 \(C\subseteq D\)。再次应用 recognition 引理。

所以 \((\mathcal S,\mathcal C)\) 是 admissible \((2,4)\) blocker pair，且 complement 与 large member 一一对应。因此

\[
|A_2|=|\mathcal S|+|\mathcal C|\ge9.
\]

## 10. \(A_4\) 补对偶与 side-swap

对 \(A_4\)，原 small members 满足 \(|S|\ge4\)，large-trace complements
\(C=U\setminus K\) 满足 \(|C|\ge2\)。相同 recognition 证明给出

\[
\mathcal S=B(\mathcal C),\qquad
\mathcal C=B(\mathcal S).
\]

`PROVED`：交换两侧后
\((\mathcal C,\mathcal S)\) 正是 admissible \((2,4)\) pair，所以

\[
|A_4|=|\mathcal C|+|\mathcal S|\ge9.
\]

`PROVED`：这也可直接从 oriented cover 的补变换验证。令
\(R'=U\setminus R\)，则

\[
S\subseteq R
\iff
R'\subseteq U\setminus S,
\]

而

\[
R\subseteq K
\iff
U\setminus K=C\subseteq R'.
\]

因此原 small 事件变为新 large-trace 事件，原 large 事件变为新 small 事件；所有量词、clutter 性和成员大小下界均被保留。该步骤不假设某个具体 family 具有自补对称性。

## 11. 全局求和与 eventual 量词

`PROVED`（相对于冻结依赖）：冻结 canonical-layer 框架给出七个互不相交且穷尽 \(F\) 的层，并已有

\[
|A_0|=1,\quad |A_1|\ge6,\quad |A_3|\ge9,\quad
|A_5|\ge6,\quad |A_6|=1.
\]

插入新证明的 \(A_2,A_4\) 下界：

\[
\begin{aligned}
|F|
 &=\sum_{i=0}^{6}|A_i|\\
 &\ge1+6+9+9+9+6+1\\
 &=41.
\end{aligned}
\]

`PROVED`（相对于冻结稳定性与 homogeneous-atom 依赖）：先取稳定阈值
\(N_{\mathrm{stab}}\)，再选择

\[
n\ge N_{\mathrm{stab}},\qquad n\ge7,\qquad n>2^{55}.
\]

选择 endpoint-normal 的 minimum saturated family \(F\)。冻结上界
\(|F|\le55\) 给出

\[
n>2^{55}\ge2^{|F|},
\]

从而产生所需 homogeneous block。这里使用的是既有上界 55，不是待证的 41，所以没有循环。

由于 \(F\) 是该 \(n\) 上的 minimum family，且 \(n\) 已在稳定区间，

\[
\operatorname{sat}(7)
=\operatorname{sat}(n,7)
=|F|
\ge41.
\]

局部 blocker 证明适用于任意有限 \(U=X\setminus H\)，没有对
\(|U|\) 设置上界，故不存在从小规模 \(U\) 外推到 eventual 范围的量词缺口。

## 12. 边界审计

- `PROVED`：空侧已由 blocker 空族约定显式排除。
- `PROVED`：private witnesses 的存在、不同性及其对 blocker minimality 的依赖均已显式证明。
- `PROVED`：三个 \(a+b=8\) split 分别独立排除，没有假设目标结论。
- `PROVED`：三集合计数保留每个 incidence class 的实际基数；多个点具有相同 incidence pattern 不会被合并。
- `PROVED`：所有成员只要求各自满足下界，证明没有假设同一侧成员等大。
- `PROVED`：\(U\) 只要求有限，可以任意大；未使用 bounded-\(U\) enumeration。
- `PROVED`：不属于任何 blocker edge 的 ground points 自动不能出现在 minimal transversal 中，故任意 unused points 不影响证明。
- `PROVED`：四对四证明使用的是实际元素和实际成员，不依赖 incidence-pattern quotient。
- `PROVED`：\(A_2\) 和 \(A_4\) 的 mutual-blocker recognition 分别检查了 transversal、containment 和 clutter minimality。
- `PROVED`：补对偶逐式保留全称量词，不依赖固定 core 大小。
- `PROVED`：全局 minimum-family 身份在最终等式
  \(\operatorname{sat}(n,7)=|F|\) 处显式使用。
- `PROVED`：没有把有限搜索或数值试验作为证明依赖。
- `UNKNOWN`：本报告不构成隔离 Referee 的 `ACCEPT`，也不主张 novelty、priority、publication readiness 或更强下界。

## 13. 最终控制面板

```text
LOCAL_THEOREM_m(2,4)>=9: PROVED
A2>=9: PROVED
A4>=9: PROVED
GLOBAL_sat(7)>=41_RELATIVE_TO_FROZEN_DEPENDENCIES: PROVED
ATTACK_VERDICT: PROVED
FIRST_INVALID_STEP: NONE
COUNTEREXAMPLE: NONE
UNRESOLVED_MATHEMATICAL_DEPENDENCIES_INSIDE_ALLOWED_SCOPE: NONE
FINITE_SEARCH_USED_AS_PROOF: NO
NETWORK_USED: NO
FORMALIZER_USED: NO
OTHER_G4_3_AGENT_OUTPUTS_READ: NO
REPOSITORY_WRITES: NONE
CLAIMS_OR_STATUS_MODIFIED: NO
```
