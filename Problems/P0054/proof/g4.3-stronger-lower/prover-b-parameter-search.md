# P0054 G4.3 兼容隔离离线 Prover B 报告

## 0. Verdict

```text
ROLE: COMPAT_ISOLATED_OFFLINE_PROVER_B
PRIMARY_TARGET: m(2,4) >= 9
PRIMARY_VERDICT: PROVED
PROOF_DEPENDS_ON_COMPUTATION: NO
TOTAL_AT_MOST_8_WITNESS: PROVED_NOT_TO_EXIST
TOTAL_9_WITNESS: NOT_FOUND_COMPUTED_ONLY
FIRST_UNCERTAIN_STEP: hand-proof or proof-certificate exclusion of the
                      exact-nine splits (a,b)=(6,3),(5,4)
NETWORK: OFFLINE
FORMALIZER: NOT_USED
REPOSITORY_WRITES: NONE
```

`PROVED`: 对任意有限底集 \(U\)，每个 admissible \((2,4)\) blocker pair
\((\mathcal S,\mathcal C)\) 都满足
\[
|\mathcal S|+|\mathcal C|\ge 9.
\]
因此
\[
m(2,4)\ge 9.
\]

`PROVED`: 不存在总成员数不超过 \(8\) 的 admissible pair；该结论没有导入
G4.2 的 \(m(2,4)\ge8\)，也不依赖有限搜索。

`COMPUTED`: 对总数恰为 \(9\) 时尚未被纸笔论证直接排除的
\((a,b)=(6,3),(5,4)\) 做了完整 incidence-type 零命中枚举；没有找到九成员
witness。按本 gate 的证据边界，这个有限负结果不升级为 `PROVED`，也不据此
声称 \(m(2,4)\ge10\)。

## 1. 隔离与输入核验

`COMPUTED`: 只实质读取了以下三个获准文件：

| 文件 | 实测 SHA-256 |
|---|---|
| `AGENTS.md` | `5ec4fe8a019a5c52efe2a382989d58782abfc6242240f77f9a0f5f8a7a39f4c1` |
| `Problems/P0054/experiments/g4.3-stronger-lower/section0-freeze.md` | `759e7b6a2bbad8853f2baa7424c8b19ac06e6ecaf07b3c3758a30d57a9a99aaf` |
| `Problems/P0054/proof/g4.3-stronger-lower/frozen-subproblem.md` | `cc64e1e376196355b68266abcfdf228d38836b6fc05c170204397efc67a8ddaa` |

三项哈希均与冻结值一致。没有读取 Prover A、Prover C、Experimentalist、
Formalizer 或其他 G4.3 输出；没有网络访问或仓库写入。

## 2. 记号

`DEFINITION`: 令
\[
a=|\mathcal S|,\qquad b=|\mathcal C|.
\]

`DEFINITION`: blocker 使用冻结陈述中的定义；特别地
\(B(\varnothing)=\{\varnothing\}\)，且 admissible pair 满足
\[
\mathcal S=B(\mathcal C),\qquad
\mathcal C=B(\mathcal S),
\]
每个 \(S\in\mathcal S\) 有 \(|S|\ge2\)，每个 \(C\in\mathcal C\) 有
\(|C|\ge4\)。

## 3. Private-witness lemma

`PROVED`:

> 若 \(T\in B(\mathcal H)\)，则对每个 \(x\in T\)，存在
> \(E_x\in\mathcal H\) 满足
> \[
> T\cap E_x=\{x\}.
> \]
> 不同的 \(x\) 可取到不同的 \(E_x\)，因而
> \[
> |T|\le|\mathcal H|.
> \]

证明：固定 \(x\in T\)。由于 \(T\) 是 inclusion-minimal transversal，
\(T\setminus\{x\}\) 不是 transversal。因此存在 \(E_x\in\mathcal H\) 与
\(T\setminus\{x\}\) 不交。另一方面 \(T\) 命中 \(E_x\)，所以
\(T\cap E_x=\{x\}\)。

若 \(x\ne y\) 而 \(E_x=E_y\)，则同一个交集既等于 \(\{x\}\) 又等于
\(\{y\}\)，矛盾。因此 \(x\mapsto E_x\) 为单射。空族情形只有
\(T=\varnothing\)，结论也成立。

## 4. 初始边界和空侧审计

`PROVED`: \(\mathcal S,\mathcal C\) 均非空。若
\(\mathcal C=\varnothing\)，则
\(\mathcal S=B(\varnothing)=\{\varnothing\}\)，违反 \(|S|\ge2\)；交换两侧
同理。

`PROVED`: 对任意 \(C\in\mathcal C=B(\mathcal S)\)，private-witness lemma
给出
\[
4\le |C|\le a,
\]
故 \(a\ge4\)。同理，对任意 \(S\in\mathcal S=B(\mathcal C)\)，
\[
2\le |S|\le b,
\]
故 \(b\ge2\)。

因此若反设 \(a+b\le8\)，只需处理
\[
b=2,\quad b=3,\quad b=4.
\]

## 5. \(b=2\)

`PROVED`: 设
\(\mathcal C=\{C_1,C_2\}\)。

若 \(C_1\cap C_2\ne\varnothing\)，则每个
\(z\in C_1\cap C_2\) 给出 singleton minimal transversal \(\{z\}\)，与
\(\mathcal S\) 每个成员至少有两个点矛盾。因此
\[
C_1\cap C_2=\varnothing.
\]

对两个不交的非空集合，minimal transversal 恰为
\[
\{x,y\},\qquad x\in C_1,\ y\in C_2.
\]
所以
\[
a=|C_1||C_2|\ge4\cdot4=16,
\]
与 \(a+b\le8\) 矛盾。

该论证同时处理了 \((a,b)=(4,2),(5,2),(6,2)\) 等所有更小边界。

## 6. \(b=3\)

`PROVED`: 写
\(\mathcal C=\{C_1,C_2,C_3\}\)。三重交为空，否则其中任一点产生
singleton blocker。

删除 \(C_1\cup C_2\cup C_3\) 外的点不会改变 blocker：这种点若出现在
transversal 中，删除它仍是 transversal，故不可能出现在 minimal
transversal 中。

将剩余点按其精确 incidence type 分为六类。记

\[
\begin{aligned}
x_i&=\#\{\text{只属于 }C_i\text{ 的点}\},\\
p&=|C_1\cap C_2|,\qquad
q=|C_1\cap C_3|,\qquad
r=|C_2\cap C_3|.
\end{aligned}
\]

由于三重交为空，上述两两交已经是精确 incidence classes。允许任意重数，
因此重复 incidence pattern 已包含在 \(x_i,p,q,r\) 中。边大小条件为

\[
x_1+p+q\ge4,\qquad
x_2+p+r\ge4,\qquad
x_3+q+r\ge4.
\]

`PROVED`: minimal transversal 的完整列表为：

- 两点型：
  \[
  (12,13),(12,23),(13,23),(12,3),(13,2),(23,1);
  \]
- 三点型：恰为 \((1,2,3)\)。

任何 minimal transversal 至多含三个点，可由 private-witness lemma 得到。
同一 incidence type 的两个点不可能同时出现在 minimal transversal 中，
因为删除其中一个不改变被命中的 \(C_i\)。

因此 blocker 数恰为

\[
N=pq+pr+qr+px_3+qx_2+rx_1+x_1x_2x_3. \tag{1}
\]

重新标号 \(C_1,C_2,C_3\) 后可设 \(p\le q\le r\)。以下穷尽所有整数边界；
每行只丢弃了非负项：

| 条件 | 从 (1) 得到的下界 |
|---|---:|
| \(p\ge2\) | \(pq+pr+qr\ge12\) |
| \(p=1,\ q\ge2\) | \(q+r+qr\ge8\) |
| \(p=q=1,\ r\ge3\) | \(1+2r\ge7\) |
| \(p=q=1,\ r=2\) | 前三项为 \(5\)，且 \(x_3\ge1\)，故 \(px_3\ge1\) |
| \(p=q=r=1\) | 各 \(x_i\ge2\)，三个线性项之和至少 \(6\) |
| \(p=0,\ q\ge3\) | \(qr\ge9\) |
| \(p=0,\ q=2,\ r\ge3\) | \(qr\ge6\) |
| \(p=0,\ q=r=2\) | \(x_1,x_2\ge2\)，故 \(qx_2+rx_1\ge8\) |
| \(p=0,\ q=1,\ r\ge2\) | \(x_1\ge3\)，故 \(qr+rx_1\ge4r\ge8\) |
| \(p=0,\ q=r=1\) | \(x_1,x_2\ge3\)，故 \(qr+rx_1+qx_2\ge7\) |
| \(p=q=0,\ r\ge2\) | \(x_1\ge4\)，故 \(rx_1\ge8\) |
| \(p=q=0,\ r=1\) | \(x_1\ge4,\ x_2,x_3\ge3\)，乘积项至少 \(36\) |
| \(p=q=r=0\) | 各 \(x_i\ge4\)，乘积项至少 \(64\) |

故始终
\[
a=N\ge6.
\]
但在 \(b=3,\ a+b\le8\) 下必须有 \(a\le5\)，矛盾。

## 7. \(b=4\)

`PROVED`: 由 \(a+b\le8\) 和 \(a\ge4\) 得 \(a=4\)。写
\[
\mathcal S=\{S_1,S_2,S_3,S_4\}.
\]

因为 \(\mathcal C=B(\mathcal S)\) 的每个成员至少含四点，任何 transversal
都不可能有至多三个点；否则在有限集合中将其逐点缩小会得到大小至多三的
minimal transversal。因此
\[
\tau(\mathcal S)\ge4.
\]

每个 \(S_i\) 非空。任取 \(s_i\in S_i\)，集合
\(\{s_1,s_2,s_3,s_4\}\) 是大小至多四的 transversal，故
\[
\tau(\mathcal S)=4.
\]

若某两个 \(S_i,S_j\) 相交，取一个公共点，再从另外两个 \(S\)-成员各取
一点，就得到大小至多三的 transversal，矛盾。因此四个 \(S_i\) 两两不交。

对两两不交的 \(S_1,\ldots,S_4\)，每种选择
\[
\{s_1,s_2,s_3,s_4\},\qquad s_i\in S_i,
\]
都是 minimal transversal；删除 \(s_i\) 后会漏掉 \(S_i\)。不同选择给出
不同集合。因此

\[
b=|B(\mathcal S)|
 \ge\prod_{i=1}^4|S_i|
 \ge2^4=16,
\]
与 \(b=4\) 矛盾。

## 8. 主定理结论

`PROVED`: \(b=2,3,4\) 均不可能与 \(a+b\le8\) 同时发生，而
private-witness lemma 已排除其他 \(b\)。所以不存在总成员数不超过八的
admissible pair，即

\[
\boxed{m(2,4)\ge9}.
\]

此结论覆盖所有小于八及等于八的总数，没有把“已接受的 \(m(2,4)\ge8\)”
作为依赖。

## 9. 九成员 sharpness 检查

`PROVED`: 总数恰为九时，由 \(a\ge4,b\ge2\) 只有

\[
(a,b)=(7,2),(6,3),(5,4),(4,5).
\]

`PROVED`: \((7,2)\) 被第 5 节的 \(a\ge16\) 排除。

`PROVED`: \((4,5)\) 也被第 7 节的论证排除；该论证在 \(a=4\) 时实际上给出
\(b\ge16\)，不要求预先有 \(b=4\)。

剩余 \((6,3),(5,4)\) 只作 `COMPUTED` 检查：

- 对 \(b=3\)，private-witness lemma 给出每个 \(C_i\) 的大小在
  \(4,\ldots,6\)；枚举六个 incidence multiplicity，并用公式 (1) 精确
  计算 blocker 数。
- 对 \(b=4\)，每个 \(C_i\) 的大小在 \(4,\ldots,5\)。公共四重 incidence
  会产生 singleton blocker，故只需非空 proper 4-bit types
  \(1,\ldots,14\)。minimal transversal 对应这些 types 的 irredundant
  cover；它不会重复使用同一 type，且至多使用四种 type。重数通过各 cover
  上重数乘积精确计数。
- 四个 \(C_i\) 是 clutter 的条件被编码为：对每个有序对 \(i\ne j\)，存在
  incidence type 含 \(i\) 而不含 \(j\)。
- 底集外点已由 minimality 排除，因此 incidence 压缩没有给 \(|U|\) 加
  先验上界。

使用 Python 3.9.6，完整复现代码如下：

```python
from functools import reduce
from itertools import combinations, product
from math import prod

# Exact-total-9 candidates (a,b)=(6,3).
hit3 = 0
for u1,u2,u3,p,q,r in product(range(7), repeat=6):
    d = (u1+p+q, u2+p+r, u3+q+r)
    if not all(4 <= z <= 6 for z in d): continue
    if not (u1+q and u2+r and u1+p and u3+r and u2+p and u3+q): continue
    n = p*q+p*r+q*r+p*u3+q*u2+r*u1+u1*u2*u3
    hit3 += (n == 6)

# Exact-total-9 candidates (a,b)=(5,4).
F=15; types=range(1,F); covers=[]
for k in range(2,5):
    for c in combinations(types,k):
        if reduce(int.__or__,c,0)==F and all(
            reduce(int.__or__,c[:i]+c[i+1:],0)!=F for i in range(k)
        ): covers.append(c)
hit4=supports=terminal_assignments=0
for bits in range(1<<14):
    supp={m for m in types if bits>>(m-1)&1}
    cs=[c for c in covers if set(c)<=supp]
    if len(cs)>5: continue
    if not all(any(m>>i&1 and not(m>>j&1) for m in supp)
               for i in range(4) for j in range(4) if i!=j): continue
    supports += 1; masks=sorted(supp); vals=[0]*len(masks)
    def dfs(k,d):
        global hit4,terminal_assignments
        if k==len(masks):
            terminal_assignments += 1
            if all(4<=z<=5 for z in d):
                mult=dict(zip(masks,vals))
                hit4 += (sum(prod(mult[t] for t in c) for c in cs)==5)
            return
        m=masks[k]
        for n in range(1,6):
            nd=[d[i]+(n if m>>i&1 else 0) for i in range(4)]
            if max(nd)>5: break
            vals[k]=n; assigned=dict(zip(masks[:k+1],vals[:k+1]))
            lower=sum(prod(assigned[t] for t in c) for c in cs
                      if set(c)<=assigned.keys())
            if lower<=5: dfs(k+1,nd)
    dfs(0,[0]*4)
print('b3_hits',hit3)
print('type_covers',len(covers))
print('supports',supports)
print('terminal_assignments',terminal_assignments)
print('b4_hits',hit4)
```

输出：

```text
b3_hits 0
type_covers 48
supports 621
terminal_assignments 1785
b4_hits 0
```

`COMPUTED`: 第二个独立实现直接枚举允许零重数的十四维 count vector，并在
blocker count 超过五时剪枝；其输出为：

```text
degree-feasible leaves with blocker count <=5: 0
blocker count 5 clutter hits: 0
```

`COMPUTED`: 没有 SAT witness，因此没有可列出的九成员 blocker pair；报告
没有虚构 witness 或 blocker 列表。

`UNKNOWN`: 依照“有限 UNSAT 不得外推”的 gate 边界，上述零命中结果不作为
\(m(2,4)\ge9\) 的证明依赖，也不升级成排除所有 exact-nine pair 的
`PROVED` 声明。

## 10. 审计清单

- `PROVED`: 空侧已按 \(B(\varnothing)=\{\varnothing\}\) 单独排除。
- `PROVED`: 所有 family 均按普通集合族处理，没有把重复成员当作不同成员。
- `PROVED`: 重复 incidence pattern 通过整数重数和乘积计数保留。
- `PROVED`: 没有假设 \(S\)-成员或 \(C\)-成员等大；只使用冻结的下界。
- `PROVED`: blocker minimality 在 private-witness lemma、三边完整分类及
  四边 transversal argument 中均被显式使用。
- `PROVED`: 任意大有限 \(U\) 已处理；family 并集外点不可能属于 minimal
  transversal。
- `PROVED`: 主证明排除了所有 \(a+b\le8\)，而不只三个总数等于八的 split。
- `COMPUTED`: 所有计算只用于 exact-nine sharpness 探索。
- `UNKNOWN`: 没有作全局 \(sat(7)\ge41\)、新颖性、发布或相邻 gate 声明。

## 11. 失败尝试与停止点

`COMPUTED`: 第二枚举器最初在 type 排序阶段调用
`int.bit_count()`，本地解释器报 `AttributeError`；错误发生在任何搜索开始
之前。将其替换为 `bin(m).count("1")` 后才运行复核，因此该兼容性失败没有
产生或改变数学输出。

```text
FIRST_UNCERTAIN_STEP:
将 exact-nine 的 (6,3) 与 (5,4) 零命中计算升级为纸笔 PROVED 排除，
或提供独立可机械核验的 proof certificate。
```

按任务边界在此停止；没有探索总数 \(10,11,12\)。
