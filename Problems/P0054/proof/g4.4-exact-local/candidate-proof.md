# P0054 G4.4 dependency-resolved candidate proof

```text
RUN_MODE: EXACT_LOCAL_PARAMETER_DISCOVERY
CURRENT_GATE: P0054_G4_4_EXACT_m_2_4
CANDIDATE_LOCAL_THEOREM: m(2,4)=12
CANDIDATE_PRODUCT_THEOREM: |S||C|>=32
CANDIDATE_GLOBAL_THEOREM: sat(7)>=47
CANDIDATE_STATUS: DEPENDENCY_RESOLVED_PENDING_TWO_REFEREES
NETWORK: OFFLINE_AFTER_LITERATURE_FREEZE
FORMALIZER: FORBIDDEN; NOT_USED
COMMIT_PUSH_PUBLICATION: FORBIDDEN; NOT_USED
```

## 1. 精确命题与证据边界

`PROVED`（本候选的结论）：对任意有限集 \(U\)，若两个 clutters
\(\mathcal S,\mathcal C\) 满足

\[
\mathcal S=B(\mathcal C),\qquad
\mathcal C=B(\mathcal S),
\]

以及

\[
\min_{S\in\mathcal S}|S|\ge2,\qquad
\min_{C\in\mathcal C}|C|\ge4,
\]

则

\[
|\mathcal S||\mathcal C|\ge32                                      \tag{1}
\]

和

\[
|\mathcal S|+|\mathcal C|\ge12.                                   \tag{2}
\]

`PROVED`（本候选的结论）：冻结的十二成员 mutual-blocker witness 达到
(2)，所以

\[
m(2,4)=12.                                                        \tag{3}
\]

`PROVED`（相对于冻结 G4.2/G4.3 global-layer 接口）：(3) 同时给出

\[
|A_2|,|A_4|\ge12
\]

以及

\[
sat(7)\ge47.                                                       \tag{4}
\]

`DEFINITION`：本文件中的 `PROVED` 表示 dependency-resolved 候选证明；
只有两份隔离 Referee 都给出 `ACCEPT` 后，才可新增 P0054-C20。

`COMPUTED`：G4.4 incidence-pattern 枚举及其两个 blocker validators 不是
本证明的依赖。

`UNKNOWN`：\(sat(7)\) 的精确值、(1)–(4) 的外部新颖性和优先权。

## 2. 冻结依赖

`PROVED`（冻结 G4.2/G4.3 接口）：canonical layers \(A_2,A_4\) 都可识别
为上述形状的 mutual-blocker pair，且对应 layer 的成员数就是两侧 cardinality
之和。\(A_4\) 只交换已识别 blocker pair 的两侧，不使用全局补对称。

`PROVED`（冻结 G4.3 接口）：其余五层满足

\[
(|A_0|,|A_1|,|A_3|,|A_5|,|A_6|)\ge(1,6,9,6,1).             \tag{5}
\]

`PROVED`（冻结 G4.3 结果）：以下三个局部下界已由纯组合证明和两份
`ACCEPT` 固定：

\[
\begin{array}{rcl}
|\mathcal C|=2&\Longrightarrow&|\mathcal S|\ge16,\\
|\mathcal C|=3&\Longrightarrow&|\mathcal S|\ge12,\\
|\mathcal S|=4&\Longrightarrow&|\mathcal C|\ge16.
\end{array}                                                       \tag{6}
\]

对应冻结文件为
[`candidate-proof.md`](../g4.3-stronger-lower/candidate-proof.md) 和
[`stronger-local-parameter.md`](../g4.3-stronger-lower/stronger-local-parameter.md)。

`PROVED`（(6) 的内容摘要）：两集合情形中，无 singleton blocker 强迫两集合
不交，逐边选择产生至少 \(4^2=16\) 个 blockers。三集合情形中，把实际点按
六个非空 incidence classes 分成 singleton classes \(A_i\) 和 doubleton
classes \(P_i\)，令其 cardinalities 为 \(\alpha_i,\pi_i\)，则

\[
|B(\mathcal C)|
=\alpha_1\alpha_2\alpha_3+\sum_i\alpha_i\pi_i
 +\pi_1\pi_2+\pi_1\pi_3+\pi_2\pi_3\ge12.                  \tag{7}
\]

四生成集情形中，transversal number 至少四强迫四个生成集两两不交，逐集合
选择产生至少 \(2^4=16\) 个 blockers。这些都是实际点计数，允许重复
incidence patterns。

## 3. blocker 基础

`DEFINITION`：\(B(\mathcal H)\) 是有限 family \(\mathcal H\) 的全部
inclusion-minimal transversals。family 是普通 set family，不是 multiset。

`PROVED`：admissible pair 两侧都非空。若一侧为空，其 blocker 为
\(\{\varnothing\}\)，与相应成员大小下界冲突。

`LITERATURE`：有限 clutter 的 blocker involution

\[
B(B(\mathcal H))=\mathcal H                                      \tag{8}
\]

由冻结文献包记录的 Edmonds–Fulkerson blocker theorem 支持；见
[`literature-pack.md`](../../literature/g4.4-exact-local/literature-pack.md)。
本轮也在 Prover C 的有限归约中给出了自包含证明。

`PROVED`（private-witness lemma）：若 \(T\in B(\mathcal H)\)，则对每个
\(x\in T\)，存在 \(E_x\in\mathcal H\) 使

\[
T\cap E_x=\{x\}.                                                 \tag{9}
\]

否则删除 \(x\) 后仍命中所有成员，与 \(T\) inclusion-minimal 矛盾。
不同 \(x\) 的 private witnesses 不同，所以

\[
|T|\le|\mathcal H|.                                              \tag{10}
\]

`PROVED`：取任意 \(C\in\mathcal C=B(\mathcal S)\)，由
\(|C|\ge4\) 和 (10) 得

\[
a:=|\mathcal S|\ge4.
\]

同理

\[
b:=|\mathcal C|\ge2.                                             \tag{11}
\]

## 4. 四集合 blocker 定理

`PROVED`（four-set theorem）：若

\[
\mathcal C=\{C_1,C_2,C_3,C_4\}
\]

是有限 clutter，每个成员大小至少四，且 \(B(\mathcal C)\) 无 singleton，
则

\[
|B(\mathcal C)|\ge8.                                             \tag{12}
\]

### 4.1 按最小成员分解 blocker

取 cardinality 最小的成员 \(E=C_1\)，写

\[
n=|E|\ge4.
\]

对 \(j=2,3,4\) 定义

\[
O_j=E\setminus C_j,\qquad R_j=C_j\setminus E,\qquad
o_j=|O_j|,\quad q_j=|R_j|.                                      \tag{13}
\]

`PROVED`：每个 \(O_j,R_j\) 都非空。否则两个不同 clutter 成员发生包含。

`PROVED`：由于 \(E\) 的 cardinality 最小，

\[
q_j-o_j=|C_j|-|E|\ge0,
\]

所以

\[
q_j\ge o_j.                                                      \tag{14}
\]

`PROVED`：\(B(\mathcal C)\) 无 singleton 等价于
\(\bigcap_i C_i=\varnothing\)。因此

\[
O_2\cup O_3\cup O_4=E.                                          \tag{15}
\]

对每个 \(x\in E\)，定义非空 residual family

\[
\mathcal J_x=\{R_j:x\in O_j,\ j\in\{2,3,4\}\}.                  \tag{16}
\]

`PROVED`：映射

\[
R\longmapsto \{x\}\cup R                                       \tag{17}
\]

给出以下两类集合的双射：

- \(B(\mathcal J_x)\)；
- 满足 \(T\cap E=\{x\}\) 的 \(T\in B(\mathcal C)\)。

若 \(R\in B(\mathcal J_x)\)，则 \(\{x\}\cup R\) 由 \(x\) 命中 \(E\)
以及所有包含 \(x\) 的 \(C_j\)，并由 \(R\) 命中其余 \(C_j\)。\(E\) 是
\(x\) 的 private witness；\(R\) 中每点在某个 residual \(R_j\) 中的
private witness 同时也是原 \(C_j\) 中的 private witness。

反过来，若 \(T\cap E=\{x\}\)，则 \(R=T\setminus\{x\}\) 命中所有
\(\mathcal J_x\) 成员；\(T\) 中每个 \(R\)-点的原 private witness 必须是
一个不含 \(x\) 的 \(C_j\)，所以它在 \(R_j\) 中仍是 private witness。
这证明双向 minimality 和 (17)。

令

\[
d_x=\min_{j:x\in O_j}q_j,\qquad
w_x=\min_{j:x\in O_j}o_j.                                      \tag{18}
\]

`PROVED`：取 \(\mathcal J_x\) 的 inclusion-minimal clutter reduction。
cardinality 等于 \(d_x\) 的 residual 成员仍是其成员：若它包含一个严格更小
residual，则违背 \(d_x\) 的最小性。由 (8)–(10)，该成员的每个点向
\(B(\mathcal J_x)\) 注入不同 private witness，故

\[
|B(\mathcal J_x)|\ge d_x\ge w_x.                               \tag{19}
\]

不同 \(x\) 的 (17) images 由与 \(E\) 的唯一交点区分。因此

\[
|B(\mathcal C)|\ge\sum_{x\in E}w_x.                            \tag{20}
\]

### 4.2 omission-size 的整数下界

对每个 \(x\in E\)，选一个达到 \(w_x\) 的 index \(f(x)\in\{2,3,4\}\)，
并令

\[
t_j=|\{x:f(x)=j\}|.
\]

`PROVED`：被赋给 \(j\) 的点都在 \(O_j\)，所以

\[
0\le t_j\le o_j,\qquad t_2+t_3+t_4=n.
\]

于是

\[
\sum_{x\in E}w_x
=\sum_{j=2}^4t_jo_j
\ge\sum_{j=2}^4t_j^2
\ge\left\lceil\frac{n^2}{3}\right\rceil.                       \tag{21}
\]

最后一步也可完全整数化为

\[
3\sum_jt_j^2-\left(\sum_jt_j\right)^2
=\frac12\sum_{i,j}(t_i-t_j)^2\ge0.
\]

`PROVED`：若 \(n\ge5\)，则 (20)–(21) 给

\[
|B(\mathcal C)|\ge\left\lceil\frac{25}{3}\right\rceil=9,
\]

从而得到 (12)。

### 4.3 \(n=4\) 的两个低和值

以下设 \(n=4\)。由 (21)，\(\sum_xw_x\ge6\)。

`PROVED`：若某个 \(O_j=E\)，则 \(\sum_xw_x\ge8\)。确实，对上述
assignment，不妨 \(o_4=4\)；于是

\[
\sum_xw_x\ge t_2^2+t_3^2+4t_4,\qquad t_2+t_3+t_4=4.
\]

对 \(t_4=0,1,2,3,4\) 分别取 \(t_2,t_3\) 最平衡的整数值，右侧下界依次为
\(8,9,10,13,16\)。

`PROVED`：若 \(\sum_xw_x=7\)，则所有 \(O_j\) 都是 \(E\) 的 proper
nonempty subsets。trace family

\[
\mathcal T=\{E,E\setminus O_2,E\setminus O_3,E\setminus O_4\}   \tag{22}
\]

没有空成员，并由 (15) 没有 singleton transversal。有限性保证 (22) 有一个
inclusion-minimal transversal \(T\subseteq E\)，且 \(|T|\ge2\)。
它也是 \(\mathcal C\) 的 minimal transversal：每个 trace 与对应原成员在
\(E\) 上相同；并且 \(E\) 本身不可能是 \(T\) 中某个点的 private witness，
因为 \(E\cap T=T\) 至少有两个点，所以每个 private witness 必来自某个
\(E\setminus O_j=C_j\cap E\)，从而也是原 \(C_j\) 的 private witness。
该 \(T\) 不属于 (17) 的任何 singleton-intersection class。
因此 (20) 外再有一个 blocker，总数至少八。

`PROVED`：若 \(\sum_xw_x=6\)，则 (21) 的两步不等式都取等。
三个正整数 \(t_j\) 在和为四时必须是 \(2,1,1\)，且 \(o_j=t_j\)。
每个 \(O_j\) 恰等于分配给它的点集，所以三个 \(O_j\) 是 \(E\) 的一个
\(2+1+1\) partition。

写 size-two block 为 \(\{r,s\}\)，两个 singleton blocks 为
\(\{p\},\{q\}\)。则下列五个 pairs 都命中 (22)：

\[
\{r,p\},\ \{s,p\},\ \{r,q\},\ \{s,q\},\ \{p,q\}.             \tag{23}
\]

由 (15)，没有 singleton 命中 (22)，所以 (23) 都 inclusion-minimal，
也都是原 \(\mathcal C\) 的 blockers。它们与 (17) 的 classes 不交。
此时 blocker 数甚至至少 \(6+5=11\)。

`PROVED`：若 \(\sum_xw_x\ge8\)，(20) 已完成。结合上述所有情形，(12)
对任意有限 \(U\)、任意重复 incidence patterns 和非均匀成员大小成立。

## 5. 五生成集定理

`PROVED`：若

\[
\mathcal S=\{S_1,\ldots,S_5\},\qquad |S_i|\ge2,
\]

且每个 transversal 大小至少四，则

\[
|B(\mathcal S)|\ge8.                                           \tag{24}
\]

`PROVED`：一个点最多属于两个 \(S_i\)。若属于至少三个，再从剩余至多两个
集合中各取一点，会产生至多三点 transversal。

令交图 \(G\) 的 vertices 为 \(S_i\)，两 vertices 相邻当且仅当对应集合
相交。

`PROVED`：\(G\) 的 matching number 至多一。若有两条 vertex-disjoint
edges，取两个交点，再从第五个集合取一点，便产生至多三点 transversal。

`PROVED`：matching number 至多一的有限 simple graph 是空图、星或三角形，
再加任意 isolated vertices。若有两条不相交的 graph edges 即违背定义；
若至少两条 edges 共享中心，而另有一条不含中心，它与其中一条不相交，除非
三条 edges 恰组成 triangle。

- `PROVED`：空图时五集合两两不交。逐集合选一点给至少
  \(2^5=32\) 个不同 minimal transversals。
- `PROVED`：星中固定一个 center–leaf 交点，再从其余三个 vertices 对应的
  pairwise disjoint 集合各选一点，给至少 \(2^3=8\) 个不同 minimal
  transversals。每个所选点以自己的 leaf 为 private witness。
- `PROVED`：三角形中固定 \(S_1\cap S_2\) 的一点，再从
  \(S_3,S_4,S_5\) 各选一点。后三集合 pairwise disjoint。固定点的 incidence
  degree 至多二，所以 \(S_1,S_2\) 中至少一个仍是它的 private witness。
  因此得到至少 \(2^3=8\) 个不同 minimal transversals。

这证明 (24)。

## 6. 六生成集定理

`PROVED`：若

\[
\mathcal S=\{S_1,\ldots,S_6\},\qquad |S_i|\ge2,
\]

且每个 transversal 大小至少四，则

\[
|B(\mathcal S)|\ge6.                                           \tag{25}
\]

### 6.1 三重 incidence

`PROVED`：一个点最多属于三个 \(S_i\)。若属于至少四个，再从剩余至多两个
集合中各取一点，产生至多三点 transversal。

`PROVED`：若某个 \(x\) 恰属于前三个集合，则 \(S_4,S_5,S_6\) 两两不交；
否则 \(x\)、一个交点及第三集合一点构成至多三点 transversal。

每个

\[
\{x,y_4,y_5,y_6\},\qquad y_i\in S_i,
\]

是四点 transversal。不存在三点 transversal，所以它自动
inclusion-minimal；后三集合两两不交保证不同 choices 给不同 subsets。
因此此情形有至少 \(2^3=8\) 个 blockers。

### 6.2 degree 至多二的带环多重图

以下设每个实际点属于一个或两个 \(S_i\)。把六个 \(S_i\) 当作 vertices：
一次 incidence 点是 loop，二次 incidence 点是 nonloop edge；相同 support
的不同实际点保留为 parallel actual points。每 vertex 的实际 incidence
degree 至少二。

`PROVED`：三个实际点能覆盖六 vertices，当且仅当它们是三个
support-disjoint nonloop edges。因此 transversal number 至少四等价于
nonloop support graph 没有 perfect matching，其 matching number
\(\nu\le2\)。

`PROVED`：若 \(\nu=0\)，只有 loops；逐 vertex 选择一个 loop 得至少
\(2^6=64\) 个 minimal covers。

`PROVED`：若 \(\nu=1\)，nonloop support 是星或三角形。在星中固定一个
center–leaf actual edge，再从其余四 vertices 各取一个 incident point。
其余 vertices 之间没有 nonloop edge，所以四个 choices 相互不同，各有
private vertex，得到至少 \(2^4=16\) 个 minimal covers。三角形中固定两条
相邻 actual edges；其余三个 isolated vertices 各有至少两个 loop choices，
得到至少 \(2^3=8\) 个 minimal covers。

### 6.3 \(\nu=2\) 的完整计数

取两个 support-disjoint nonloop supports \(E_1,E_2\)。令 \(P_i\) 是
support 等于 \(E_i\) 的实际点集，\(m_i=|P_i|\ge1\)；令 \(u,v\) 为余下
两个 vertices。

`PROVED`：不存在 nonloop support \(\{u,v\}\)，否则它与 \(E_1,E_2\)
构成 perfect matching。

`PROVED`：对任意

\[
e_i\in P_i,\qquad p\ni u,\qquad q\ni v,
\]

四个实际点

\[
F(e_1,e_2,p,q)=\{e_1,e_2,p,q\}                               \tag{26}
\]

两两不同并覆盖六 vertices。若 (26) 可删点，便有 three-point cover，
与 \(\nu=2\) 矛盾，所以它 minimal。

`PROVED`：固定 \(E_1,E_2\) 后，可从 (26) 唯一恢复 \(e_1,e_2,p,q\)：
\(p,q\) 分别是唯一 incident with \(u,v\) 的所选实际点；余下两点由其
supports 区分。因此 (26) 给出

\[
m_1m_2d(u)d(v)                                                \tag{27}
\]

个不同 minimal covers。

若 (27) 至少六即完成。否则，由
\(m_i\ge1,d(u),d(v)\ge2\) 的整数条件，只可能

\[
m_1=m_2=1,\qquad d(u)=d(v)=2.                                \tag{28}
\]

固定唯一 \(e_i\in P_i\)，记 \(M=\{e_1,e_2\}\)。其生成族
\(\mathcal F_M\) 恰有四个成员。

`PROVED`：若存在另一个 actual two-edge matching
\(N=\{f_1,f_2\}\ne M\)，其同类生成族 \(\mathcal F_N\) 至少有四个成员，
并且

\[
|\mathcal F_M\cap\mathcal F_N|\le2.                            \tag{29}
\]

若 \(M,N\) 不共享 actual point，共同成员必须等于四点集 \(M\cup N\)，所以
至多一个。若恰共享一个，写

\[
M=\{e,f\},\qquad N=\{e,g\}.
\]

若 \(f,g\) support-disjoint，则 \(e,f,g\) 是 perfect matching，矛盾。
若它们相交一个 vertex，\(e,f,g\) 共覆盖五个 vertices；共同生成成员的
第四点必须 incident with 唯一遗漏 vertex。该 vertex 是 \(M\) 的 unmatched
vertex，由 (28) 至多有两个 choices。若 \(f,g\) 是不同 parallel actual
points，一个额外 support 若覆盖余下两个 vertices，就与 \(M\) 组成 perfect
matching，所以共同成员不存在。这证明 (29)，从而

\[
|\mathcal F_M\cup\mathcal F_N|\ge4+4-2=6.                     \tag{30}
\]

`PROVED`：若 \(M\) 是唯一 actual two-edge matching，则所有 incident with
\(u\) 或 \(v\) 的实际点都是 loops。若 nonloop \(p\) 从 \(u\) 连到
\(E_1\) 的 vertex，则 \(\{p,e_2\}\) 是第二 matching；连到 \(E_2\)
时同理；连到 \(v\) 时产生 perfect matching。由 (28)，\(u,v\) 各恰有两个
不同 loops。

写

\[
E_1=\{a,b\},\qquad E_2=\{c,d\}.
\]

由 core vertices 的实际 incidence degree 至少二，分别选

\[
r_a\ne e_1,\ a\in\sigma(r_a),\qquad
r_b\ne e_1,\ b\in\sigma(r_b).
\]

`PROVED`：\(r_a,r_b\) 的 supports 都在 core \(\{a,b,c,d\}\) 中，并且
\(r_a\ne r_b\)。否则共同点的 support 是 \(\{a,b\}\)，与 \(e_2\)
形成第二 actual matching。

所以 \(\{r_a,r_b,e_2\}\) 覆盖 core。取其中一个 inclusion-minimal core
cover \(K\)。它避开 \(e_1\)。将 \(K\) 分别与 \(u,v\) 的两个 loop
choices 组合，得到四个不同 minimal covers；core private vertices 以及
\(u,v\) 保证 minimality。它们全都避开 \(e_1\)，而 \(\mathcal F_M\) 的
四个成员全含 \(e_1\)，故总数至少八。

`PROVED`：\(\nu=0,1,2\) 穷尽，(25) 成立。

## 7. 乘积不等式

`PROVED`：由 (6)、(12)、(24)、(25) 和 (11)，以下分类穷尽所有
admissible pairs：

| 情形 | cardinality 下界 | 乘积下界 |
|---|---:|---:|
| \(b=2\) | \(a\ge16\) | \(ab\ge32\) |
| \(b=3\) | \(a\ge12\) | \(ab\ge36\) |
| \(b=4\) | \(a\ge8\) | \(ab\ge32\) |
| \(b\ge5,\ a=4\) | \(b\ge16\) | \(ab\ge64\) |
| \(b\ge5,\ a=5\) | \(b\ge8\) | \(ab\ge40\) |
| \(b\ge5,\ a=6\) | \(b\ge6\) | \(ab\ge36\) |
| \(b\ge5,\ a\ge7\) | 整数乘法 | \(ab\ge35\) |

因此 (1) 成立。

## 8. 整数取整与 equality audit

`PROVED`：不使用浮点近似，

\[
(a+b)^2=(a-b)^2+4ab\ge128.                                   \tag{31}
\]

若整数 \(a+b\le11\)，则

\[
(a+b)^2\le11^2=121<128,
\]

矛盾。因此 \(a+b\ge12\)，证明 (2)。

`PROVED`：算术上 \(a+b=12\) 且 \(ab\ge32\) 的正整数 pairs 恰为

\[
(a,b)\in\{(4,8),(5,7),(6,6),(7,5),(8,4)\}.                  \tag{32}
\]

下界取等不要求乘积 (1) 也取等；例如 \((6,6)\) 的乘积是 36。本候选只需
一个实现 (32) 的 mutual-blocker witness，下一节给出 \((8,4)\)。

`PROVED`：若专门要求 \(ab=32\)，结合 \(a\ge4,b\ge2\)，整数 factor pairs
只可能

\[
(a,b)=(4,8),(8,4),(16,2).
\]

这项 product-equality 审计不声称三种结构都唯一或都由本轮分类。

## 9. 十二成员 upper witness

`DEFINITION`：

\[
U=\{a_0,a_1,a_2,a_3,b_0,b_1,b_2,b_3\}.
\]

令 \(\mathcal S\) 为两个不交四环的八条边：

\[
\begin{aligned}
\mathcal S=\{&
\{a_0,a_1\},\{a_1,a_2\},\{a_2,a_3\},\{a_3,a_0\},\\
&\{b_0,b_1\},\{b_1,b_2\},\{b_2,b_3\},\{b_3,b_0\}\}.
\end{aligned}
\]

令

\[
A_0=\{a_0,a_2\},\quad A_1=\{a_1,a_3\},\quad
D_0=\{b_0,b_2\},\quad D_1=\{b_1,b_3\},
\]

以及

\[
\mathcal C=\{A_i\cup D_j:i,j\in\{0,1\}\}.
\]

`PROVED`：四环的 inclusion-minimal vertex covers 恰为两个 bipartition
classes；不交 components 的 minimal transversals 是各 component minimal
transversal 的并。因此

\[
B(\mathcal S)=\mathcal C.
\]

`PROVED`：任一 \(\mathcal C\)-transversal 若同时遇到 \(A_0,A_1\)，便
包含第一四环的一条边；否则它必须同时遇到 \(D_0,D_1\)，便包含第二四环的
一条边。八条边本身均为 minimal transversals。因此

\[
B(\mathcal C)=\mathcal S.
\]

两侧最小成员大小分别为二和四，总 cardinality 为 \(8+4=12\)。这证明
\(m(2,4)\le12\)；与 (2) 结合得到 (3)。

`COMPUTED`：按 bits \(0,\ldots,7\) 编码：

```text
S = 03 06 09 0c 30 60 90 c0
C = 55 5a a5 aa
```

冻结 G4.3 的 powerset blocker engine 与 edge-choice/minimization engine
独立返回 \(B(S)=C\)、\(B(C)=S\)、\(B(B(S))=S\)。

## 10. 六个 split 与全局求和

`PROVED`：六个 frozen split 被逐项排除，且对偶只用于避免重复计算，不遗漏
ordered split：

| split \((a,b)\) | 状态 | 纯组合理由 |
|---|---|---|
| \((5,4)\) | `REFUTED` | (12) 给 \(b=4\Rightarrow a\ge8\) |
| \((6,4)\) | `REFUTED` | 同上 |
| \((5,5)\) | `REFUTED` | (24) 给 \(a=5\Rightarrow b\ge8\) |
| \((7,4)\) | `REFUTED` | (12) 给 \(b=4\Rightarrow a\ge8\) |
| \((6,5)\) | `REFUTED` | (25) 给 \(a=6\Rightarrow b\ge6\) |
| \((5,6)\) | `REFUTED` | (24) 给 \(a=5\Rightarrow b\ge8\) |

`PROVED`：把 (3) 分别用于冻结的 \(A_2,A_4\) blocker interfaces，并与
(5) 相加：

\[
1+6+12+9+12+6+1=47.
\]

所以 (4) 成立。这里没有从局部 witness 推断 \(sat(7)\) 的精确值。

## 11. 量词、multiplicity 与计算边界

`PROVED`：证明从未限制 \(|U|\)。inactive points 不进入任何 minimal
transversal；任意大的有限 \(U\) 均被覆盖。

`PROVED`：重复 incidence patterns 是不同实际点。所有 \(2^k\)、乘积和
weighted incidence degrees 都逐实际点计数；没有把 pattern tuple 当成一个
集合。

`PROVED`：证明允许空 incidence classes、非均匀成员大小和任意正
multiplicities；只使用给定的成员大小下界。

`PROVED`：删去或取 trace 后，只在明确取 inclusion-minimal clutter
reduction 时使用 blocker involution；普通 family 中的 redundant 成员没有
被误当作 \(B(B(\mathcal H))\) 的成员。

`PROVED`：五、六生成集的 graph 表示把 incidence degree 一的实际点保留为
loops，把 degree 二的点保留为 parallel nonloop actual points。每个生成的
cover 都以实际点 subset 计数。

`PROVED`：Prover C 已给出 arbitrary finite \(U\) 到有限
incidence-pattern multiplicity boxes 的 iff 归约，见
[`prover-c-finite-reduction.md`](./prover-c-finite-reduction.md)。
它独立支持搜索空间的语义完整性，但不是本候选纯组合证明的依赖。

`COMPUTED`：即使 G4.4 枚举把六个 split 全部报告为
`UNSAT_COMPUTED`，没有独立可检查的完整 UNSAT certificate 和第二个完整
enumerator 时，也不把该输出升级为 `PROVED`。

## 12. 已发现并修复的第一失效步骤

`REFUTED`：六生成集 \(\nu=2\) 情形中，“任选 \(e_1\) 一个端点的额外
incident point并替换 \(e_1\)”不保证覆盖 \(e_1\) 的另一个端点。

`PROVED`：6.3 的修复分别选择 \(r_a,r_b\)，先证明
\(\{r_a,r_b,e_2\}\) 覆盖完整 core，再从中取 inclusion-minimal core
cover \(K\)。

`REFUTED`：有限 incidence-pattern 搜索的 coverage counters 不是 proof
certificate；它们不记录可由独立 checker 重建的完整排除树。

`PROVED`：本候选不依赖任何该类 counter、timeout 或 solver 结论。

## 13. dependency table

| 依赖 | 标签 | 依据 |
|---|---|---|
| mutual-blocker layer recognition | `PROVED` | 冻结 G4.2/G4.3 interface |
| blocker involution | `LITERATURE` | Edmonds–Fulkerson；冻结 literature pack |
| private-witness lemma | `PROVED` | inclusion-minimality |
| \(b=2,b=3,a=4\) bounds | `PROVED` | 冻结 G4.3 纯组合证明 |
| four-set theorem | `PROVED` | residual blocker 双射与整数 omission bound |
| five-generator theorem | `PROVED` | intersection graph matching number \(\le1\) |
| six-generator theorem | `PROVED` | 三重 incidence 或带环多重图 \(\nu\le2\) |
| product inequality | `PROVED` | 七种整数 cardinality cases |
| sum lower bound 12 | `PROVED` | \(11^2<128\) |
| size-12 witness | `PROVED` | 两个不交四环 |
| \(m(2,4)=12\) | `PROVED` | lower bound + witness |
| \(sat(7)\ge47\) | `PROVED` | 冻结 layer interface + exact integer sum |
| exact \(sat(7)\) | `UNKNOWN` | 不在本 gate 内 |
| novelty / priority | `UNKNOWN` | bounded literature freeze 不能证明 absence |
