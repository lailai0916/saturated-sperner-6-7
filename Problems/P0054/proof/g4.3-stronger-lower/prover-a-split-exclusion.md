# P0054 G4.3 — Prover A 兼容隔离证明报告

```text
ROLE: COMPATIBLE_ISOLATED_OFFLINE_PROVER_A
CURRENT_GATE: P0054_G4_3_EIGHT_MEMBER_LAYER_EXCLUSION
NETWORK: OFFLINE; NOT_USED
FORMALIZER: FORBIDDEN; NOT_USED
REPOSITORY_WRITES: NONE
OTHER_G4_3_AGENT_OUTPUTS_READ: NONE
CLAIMS_OR_STATUS_MODIFIED: NO
```

## 1. 冻结输入核验

`COMPUTED`：本次只实质读取了允许的四个文件；SHA-256 为：

| 文件 | 实测 SHA-256 | 结果 |
|---|---|---|
| `AGENTS.md` | `5ec4fe8a019a5c52efe2a382989d58782abfc6242240f77f9a0f5f8a7a39f4c1` | 匹配 |
| `Problems/P0054/experiments/g4.3-stronger-lower/section0-freeze.md` | `759e7b6a2bbad8853f2baa7424c8b19ac06e6ecaf07b3c3758a30d57a9a99aaf` | 匹配 |
| `Problems/P0054/proof/g4.3-stronger-lower/frozen-subproblem.md` | `cc64e1e376196355b68266abcfdf228d38836b6fc05c170204397efc67a8ddaa` | 匹配 |
| `Problems/P0054/proof/g4.2-stronger-lower/candidate-proof.md` | `ef87bce75e3db5a8a46d99318c6b4c5e8bc769f33ef61be4e6adee55372c5a1e` | 匹配 |

`DEFINITION`：以下所有集合族均为普通有限 set family，不是 multiset。底集 \(U\) 是任意有限集。若 \(\mathcal H=\varnothing\)，采用
\[
B(\mathcal H)=\{\varnothing\}.
\]

`DEFINITION`：令 \((\mathcal S,\mathcal C)\) 为 admissible \((2,4)\) blocker pair，即
\[
\mathcal S=B(\mathcal C),\qquad
\mathcal C=B(\mathcal S),
\]
且
\[
|S|\ge2\quad(S\in\mathcal S),\qquad
|C|\ge4\quad(C\in\mathcal C).
\]
记
\[
a=|\mathcal S|,\qquad b=|\mathcal C|.
\]

## 2. Private-witness lemma

### 引理 2.1

`PROVED`：设 \(\mathcal H\) 是有限普通集合族，且 \(T\in B(\mathcal H)\)。对每个 \(x\in T\)，存在 \(E_x\in\mathcal H\) 满足
\[
T\cap E_x=\{x\}.
\]
不同的 \(x\) 必有不同的 witness；因此
\[
|T|\le|\mathcal H|.
\]

证明。若 \(T=\varnothing\)，witness 断言为空断言，且
\[
0=|T|\le|\mathcal H|.
\]

以下设 \(x\in T\)。因为 \(T\) 是 inclusion-minimal transversal，\(T\setminus\{x\}\) 不是 transversal。因此存在 \(E_x\in\mathcal H\) 使
\[
(T\setminus\{x\})\cap E_x=\varnothing.
\]
另一方面，\(T\) 是 transversal，所以 \(T\cap E_x\ne\varnothing\)。两式合并得到
\[
T\cap E_x=\{x\}.
\]

若 \(x\ne y\) 却有 \(E_x=E_y\)，则同一个集合与 \(T\) 的交集同时等于 \(\{x\}\) 和 \(\{y\}\)，矛盾。因此映射 \(x\mapsto E_x\) 是从 \(T\) 到普通集合族 \(\mathcal H\) 的单射，故 \(|T|\le|\mathcal H|\)。证毕。

### 推论 2.2

`PROVED`：admissible pair 的两侧都非空，并且
\[
a\ge4,\qquad b\ge2.
\]

证明。若 \(\mathcal C=\varnothing\)，则
\[
\mathcal S=B(\varnothing)=\{\varnothing\},
\]
违反 \(|S|\ge2\)。若 \(\mathcal S=\varnothing\)，则
\[
\mathcal C=B(\varnothing)=\{\varnothing\},
\]
违反 \(|C|\ge4\)。故两侧均非空。

任取 \(C\in\mathcal C=B(\mathcal S)\)。引理 2.1 给出
\[
4\le|C|\le|\mathcal S|=a.
\]
任取 \(S\in\mathcal S=B(\mathcal C)\)，同理
\[
2\le|S|\le|\mathcal C|=b.
\]
证毕。

## 3. 三个结构引理

### 引理 3.1：四个 small sets

`PROVED`：若
\[
\mathcal S=\{S_1,S_2,S_3,S_4\},\qquad
\mathcal C=B(\mathcal S),
\]
每个 \(S_i\) 非空，且每个 \(C\in\mathcal C\) 满足 \(|C|\ge4\)，则 \(S_1,\ldots,S_4\) 两两不交，并且
\[
|\mathcal C|=\prod_{i=1}^{4}|S_i|.
\]
特别地，若每个 \(|S_i|\ge2\)，则
\[
|\mathcal C|\ge16.
\]

证明。任意 transversal \(T\) 都包含一个 inclusion-minimal transversal：由于 \(U\) 有限，可以不断删除不必要的点直至不能再删。所得集合属于 \(B(\mathcal S)=\mathcal C\)，故每个 transversal 都至少有四个点。

若 \(S_i\cap S_j\ne\varnothing\)，取 \(x\in S_i\cap S_j\)，并从另外两个非空集合各取一点。所得至多三点的集合击中全部四个 \(S_k\)，与上一段矛盾。因此四个集合两两不交。

对两两不交的 \(S_i\)，inclusion-minimal transversal 必须且只能从每个 \(S_i\) 中恰取一点：漏取某个 \(S_i\) 就不是 transversal；从同一个 \(S_i\) 取两个点或取并集外的点就不是 minimal。反过来，每个这样的四点选择都是 minimal transversal。由于四个 \(S_i\) 两两不交，不同选择向量产生不同的实际子集。因此
\[
|B(\mathcal S)|=\prod_{i=1}^{4}|S_i|.
\]
证毕。

### 引理 3.2：两个 large sets

`PROVED`：若
\[
\mathcal C=\{C_1,C_2\},\qquad
\mathcal S=B(\mathcal C),
\]
每个 \(S\in\mathcal S\) 满足 \(|S|\ge2\)，则 \(C_1\cap C_2=\varnothing\)，并且
\[
|\mathcal S|=|C_1||C_2|.
\]
若另有 \(|C_1|,|C_2|\ge4\)，则
\[
|\mathcal S|\ge16.
\]

证明。若 \(x\in C_1\cap C_2\)，则 \(\{x\}\) 是 transversal。因 \(C_1,C_2\) 非空，空集不是 transversal，所以 \(\{x\}\in B(\mathcal C)=\mathcal S\)，违反 \(|S|\ge2\)。故 \(C_1,C_2\) 不交。

两个集合不交时，minimal transversal 必须且只能从 \(C_1,C_2\) 各取一点。因此
\[
|B(\mathcal C)|=|C_1||C_2|\ge4\cdot4=16.
\]
不同点对产生不同的实际二元子集，不使用 multiset 计数。证毕。

### 引理 3.3：三个 large sets 的 blocker 下界

`PROVED`：设
\[
\mathcal C=\{C_1,C_2,C_3\}
\]
是有限普通集合族，满足
\[
|C_i|\ge4\quad(i=1,2,3),\qquad
C_1\cap C_2\cap C_3=\varnothing.
\]
则
\[
|B(\mathcal C)|\ge6.
\]

证明。把 \(C_1\cup C_2\cup C_3\) 中的点按六种非空 incidence pattern 分组：

\[
\begin{array}{lll}
P_{12}=(C_1\cap C_2)\setminus C_3,&
P_{13}=(C_1\cap C_3)\setminus C_2,&
P_{23}=(C_2\cap C_3)\setminus C_1,\\[2mm]
P_1=C_1\setminus(C_2\cup C_3),&
P_2=C_2\setminus(C_1\cup C_3),&
P_3=C_3\setminus(C_1\cup C_2).
\end{array}
\]

令
\[
a=|P_{12}|,\quad b=|P_{13}|,\quad c=|P_{23}|,\quad
d=|P_1|,\quad e=|P_2|,\quad f=|P_3|.
\]
于是
\[
a+b+d\ge4,\qquad a+c+e\ge4,\qquad b+c+f\ge4. \tag{1}
\]

由引理 2.1，每个 minimal transversal 至多有三个点。三重交为空，所以不存在一元 transversal；每个 \(C_i\) 非空，所以空集也不是 transversal。

二元 minimal transversals 的 incidence-pattern 对恰为
\[
(12,13),(12,23),(12,3),(13,23),(13,2),(23,1).
\]
这些分别贡献
\[
ab,\ ac,\ af,\ bc,\ be,\ cd.
\]

若 \(T\) 是三元 minimal transversal，引理 2.1 给三个点提供三个不同的 private witnesses，故三个 witness 恰为 \(C_1,C_2,C_3\)。若分配给 \(C_i\) 的点还属于 \(C_j\)，那么分配给 \(C_j\) 的点也属于 \(C_j\)，从而 \(T\cap C_j\) 至少含两点，违反后者对 \(C_j\) 的 private-witness 等式。因此三个点必须分别来自 \(P_1,P_2,P_3\)。反过来，从这三个类各取一点确实给出三元 minimal transversal，贡献 \(def\)。

因此得到完整且无重复的 blocker 计数式
\[
N:=|B(\mathcal C)|
 =ab+ac+af+bc+be+cd+def. \tag{2}
\]

以下从 (1)–(2) 证明 \(N\ge6\)。

#### 情形一：\(d=e=f=0\)

此时
\[
a+b\ge4,\qquad a+c\ge4,\qquad b+c\ge4,
\]
且
\[
N=ab+ac+bc.
\]
在 \(a,b,c\) 中取最小者并通过重标 \(C_1,C_2,C_3\) 记为 \(a\)。

- 若 \(a=0\)，则 \(b,c\ge4\)，所以 \(N\ge bc\ge16\)；
- 若 \(a=1\)，则 \(b,c\ge3\)，所以 \(N\ge3+3+9=15\)；
- 若 \(a\ge2\)，则 \(a,b,c\ge2\)，所以 \(N\ge4+4+4=12\)。

#### 情形二：\(d,e,f\) 中恰有一个为正

重标后三者可写为
\[
d>0,\qquad e=f=0.
\]
此时
\[
N=ab+c(a+b+d).
\]

- 若 \(c=0\)，由 (1) 得 \(a,b\ge4\)，故 \(N\ge16\)；
- 若 \(c=1\)，由 (1) 得 \(a,b\ge3\)，故 \(N\ge ab\ge9\)；
- 若 \(c\ge2\)，由 \(a+b+d\ge4\) 得 \(N\ge4c\ge8\)。

#### 情形三：\(d,e,f\) 中恰有两个为正

重标后可写为
\[
d,e>0,\qquad f=0.
\]
由 (2)，
\[
N=b(a+c+e)+c(a+d).
\]

- 若 \(b=0\)，则 (1) 给出 \(c\ge4\) 及 \(a+d\ge4\)，故 \(N\ge16\)；
- 若 \(b=1\)，则 \(c\ge3\)、\(a+d\ge3\)、\(a+c+e\ge4\)，故
  \[
  N\ge4+3\cdot3=13;
  \]
- 若 \(b\ge2\)，则
  \[
  N\ge b(a+c+e)\ge2\cdot4=8.
  \]

#### 情形四：\(d,e,f\) 全为正

令
\[
s=a+b+c,\qquad p=def,\qquad t=d+e+f.
\]
由 (2) 及 \(d,e,f\ge1\)，
\[
N\ge af+be+cd+def\ge s+p. \tag{3}
\]
若反设 \(N\le5\)，则 \(p\le5\) 且 \(s\le5-p\)。正整数三元组在 \(p=1,\ldots,5\) 时的因子分解给出：

| \(p\) | \((d,e,f)\) 的无序可能 | \(t\) 的最大值 | \(2s+t\) 的上界 |
|---:|---|---:|---:|
| 1 | \((1,1,1)\) | 3 | \(2(4)+3=11\) |
| 2 | \((1,1,2)\) | 4 | \(2(3)+4=10\) |
| 3 | \((1,1,3)\) | 5 | \(2(2)+5=9\) |
| 4 | \((1,1,4),(1,2,2)\) | 6 | \(2(1)+6=8\) |
| 5 | \((1,1,5)\) | 7 | \(2(0)+7=7\) |

但把 (1) 三式相加得到
\[
2s+t\ge12,
\]
与表中每一行矛盾。故 \(N\ge6\)。

四种情形穷尽所有非负整数 \(d,e,f\)，所以
\[
|B(\mathcal C)|=N\ge6.
\]
证毕。

`PROVED`：引理 3.3 完全允许同一 incidence pattern 中出现任意多个不同点；变量 \(a,\ldots,f\) 正是这些重复 pattern 的实际 multiplicity。式 (2) 计数的是不同实际子集，不把普通集合族当作 multiset。

## 4. 排除总数小于八

`PROVED`：不存在 admissible pair 满足 \(a+b<8\)。

证明。由推论 2.2，
\[
a\ge4,\qquad b\ge2.
\]
因此 \(a+b<8\) 时只可能有
\[
(a,b)=(4,2),(4,3),(5,2).
\]

- 当 \(b=2\) 时，引理 3.2 给出 \(a\ge16\)，排除 \((4,2)\) 与 \((5,2)\)；
- 当 \((a,b)=(4,3)\) 时，引理 3.1 给出 \(b\ge16\)，矛盾。

因此较小总数已在本报告内独立排除；冻结 G4.2 的 \(m(2,4)\ge8\) 上游结论不是本步骤的证明依赖。

## 5. 从 \(a+b=8\) 得到仅三个 split

`PROVED`：若 \(a+b=8\)，由 \(a\ge4,b\ge2\) 得
\[
2\le b\le4,\qquad a=8-b.
\]
所以且仅所以
\[
(a,b)=(4,4),(5,3),(6,2).
\]

### 5.1 排除 \((4,4)\)

`REFUTED`：不存在 admissible pair 满足 \((a,b)=(4,4)\)。

由引理 3.1，
\[
b=|B(\mathcal S)|
 =\prod_{S\in\mathcal S}|S|
 \ge2^4=16,
\]
与 \(b=4\) 矛盾。

### 5.2 排除 \((5,3)\)

`REFUTED`：不存在 admissible pair 满足 \((a,b)=(5,3)\)。

写
\[
\mathcal C=\{C_1,C_2,C_3\}.
\]
若 \(x\in C_1\cap C_2\cap C_3\)，则 \(\{x\}\in B(\mathcal C)=\mathcal S\)，违反每个 \(S\) 至少有两个点。因此
\[
C_1\cap C_2\cap C_3=\varnothing.
\]
又有 \(|C_i|\ge4\)。引理 3.3 因而给出
\[
a=|\mathcal S|=|B(\mathcal C)|\ge6,
\]
与 \(a=5\) 矛盾。

### 5.3 排除 \((6,2)\)

`REFUTED`：不存在 admissible pair 满足 \((a,b)=(6,2)\)。

引理 3.2 给出
\[
a=|B(\mathcal C)|\ge16,
\]
与 \(a=6\) 矛盾。

## 6. 主定理

`PROVED`：对任意有限底集 \(U\)，每个 admissible \((2,4)\) blocker pair 都满足
\[
|\mathcal S|+|\mathcal C|\ge9.
\]
因此
\[
\boxed{m(2,4)\ge9}.
\]

证明。第 4 节排除了总数小于八；第 5 节穷尽并排除了总数等于八的全部三个整数 split。故不存在总数至多八的 admissible pair。证毕。

## 7. 边界与量词审计

- `PROVED`：\(U\) 仅被假设为任意有限集；证明中没有 \(|U|\) 上界、稳定范围假设或 incidence-pattern 数量界。
- `PROVED`：空侧已显式排除。若某侧为空，另一侧按冻结约定等于 \(\{\varnothing\}\)，立即违反成员大小下界。
- `PROVED`：所有成员大小均可非均匀。证明只使用 \(|S|\ge2\) 与 \(|C|\ge4\)。在三个 equality split 中，private-witness lemma 还分别允许：
  \[
  \begin{array}{c|c|c}
  (a,b)&|S|\text{ 的允许范围}&|C|\text{ 的允许范围}\\ \hline
  (4,4)&2\le|S|\le4&|C|=4\\
  (5,3)&2\le|S|\le3&4\le|C|\le5\\
  (6,2)&|S|=2&4\le|C|\le6
  \end{array}
  \]
  排除证明没有把未被强制的范围收缩为 uniform size。
- `PROVED`：三集合引理显式容许任意重复 incidence pattern；相同 pattern 中的不同点仍按不同实际元素计数。
- `PROVED`：private-witness lemma、三集合 blocker 分类以及两两不交时的乘积公式均显式检查 inclusion-minimality。
- `PROVED`：普通 set family 中不存在重复成员副本；\(a,b\) 计数不同集合。所有乘积计数均通过实际子集的一一对应完成，不使用 multiset multiplicity。
- `PROVED`：不属于相关集合并集的点不会出现在 minimal transversal 中，因为删除该点不改变 transversal 性质。
- `PROVED`：未使用有限搜索、概率估计、浮点运算、SAT/SMT、Lean、Formalizer、网络、极限、紧性或对有限 \(|U|\) 的外推。

## 8. 对 \(A_2\)、\(A_4\) 与 \(41\) 的条件性依赖闭包

`PROVED`（条件蕴含，不创建 claim）：冻结 G4.2 接口已经把 \(A_2\) 的 small generators 与 large-trace complements 识别为 mutual blockers，并给出成员大小下界 \(2\) 与 \(4\)。在该冻结接口下，本报告的局部定理直接给出
\[
|A_2|\ge9.
\]

`PROVED`（条件蕴含，不创建 claim）：冻结 complemented side-swap 把 \(A_4\) 的接口交换为同一个 admissible \((2,4)\) blocker pair，保持成员总数不变。因此
\[
|A_4|\ge9.
\]

`PROVED`（条件蕴含，不创建 claim）：若同时采用冻结 canonical-layer 分解及其余层界，则
\[
(1,6,8,9,8,6,1)
\]
中的第二、第四内部层可分别提升为 \(9\)，得到
\[
(1,6,9,9,9,6,1),
\qquad
1+6+9+9+9+6+1=41.
\]
因此冻结全局接口与本局部定理形成通向
\[
\operatorname{sat}(7)\ge41
\]
的 dependency-closed 数学蕴含链。

`UNKNOWN`：该全局候选的独立 Referee 结果、控制面板晋级及 claim 创建授权不属于本 Prover 报告。本报告未创建或修改任何 claim、status 或仓库文件。

```text
PRIMARY_LOCAL_RESULT: PROVED
M(2,4)>=9: PROVED
FIRST_INVALID_STEP: NONE
COUNTEREXAMPLE_STATUS: NO_ADMISSIBLE_PAIR_WITH_TOTAL_AT_MOST_8
UNRESOLVED_LOCAL_MATHEMATICAL_DEPENDENCIES: NONE
FINITE_COMPUTATION_USED_AS_PROOF: NO
FORMALIZER_USED: NO
OTHER_G4_3_AGENT_OUTPUT_READ: NO
CLAIM_CREATED: NO
REPOSITORY_WRITE: NO
```
