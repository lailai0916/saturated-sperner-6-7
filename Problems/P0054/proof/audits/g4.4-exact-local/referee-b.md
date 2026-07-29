# P0054 G4.4 兼容替代 Referee B 报告

角色边界：专用 Referee runtime 在材料访问前失败；本审查为隔离、只读、离线兼容替代。未使用网络、Formalizer，未读取另一位 G4.4 Referee 的报告内容，未修改仓库。

## 冻结与完整性

`COMPUTED`：

- `HEAD=d2c8e3eb81466a3743c736319ef1874920590abc`，与冻结值一致。
- `review-freeze.json` SHA-256 为 `25a89f...3149`，命中指定值。
- 清单内 18 个对象的字节数和 SHA-256 全部逐项匹配，包括候选证明 `5bacfe...9832`、Prover C、实验四件套、G4.3 冻结依赖以及条件可写文件。
- 文献 freeze manifest 的五个对象、实验记录引用的 G4.3 三件套也全部匹配。
- 实验三件套 SHA-256 行聚合为 `9e12a317...8601`，与 manifest 一致。
- 结束时上述关键哈希及 `HEAD` 未改变；工作树仍为 Section 0 记录的原有 dirty baseline。

## 命题匹配

`PROVED`：候选证明审查的命题与 frozen subproblem 完全一致：任意有限 \(U\)、普通 set-family clutters、两条 mutual-blocker 等式、成员大小下界 \(2,4\)，目标为
\[
|\mathcal S||\mathcal C|\ge32,\qquad
|\mathcal S|+|\mathcal C|\ge12,\qquad
m(2,4)=12.
\]
没有固定底集、均匀边、单一 incidence-pattern 或 complement-symmetry 的额外假设。

## 组合证明审查

`PROVED`：

- 空侧、inactive points、重复 incidence patterns、空 incidence classes、非均匀成员大小及任意大的有限 \(U\) 均被正确处理。
- private-witness injection 正确给出 \(a\ge4,b\ge2\)。

四集合定理审查通过：

- 选最小边 \(E\)，有 \(q_j\ge o_j\)，且无 singleton blocker 等价于 \(O_2\cup O_3\cup O_4=E\)。
- 对每个 \(x\in E\)，\(B(\mathcal J_x)\leftrightarrow\{T\in B(\mathcal C):T\cap E=\{x\}\}\) 的双射在 residual 重复或冗余时仍成立；取 inclusion-minimal clutter reduction 不改变 blocker，最小 residual 仍保留。
- \(\sum_xw_x\ge\lceil n^2/3\rceil\) 的整数推导正确。
- \(n=4\) 的两个危险边界均闭合：
  - 和为 7 时，trace family 的额外 minimal transversal 大小至少 2；其 private witness 不可能是 \(E\)，故确为原 family 的新 blocker。
  - 和为 6 时三个 omission sets 必为 \(2+1+1\) partition，列出的五个 pairs 均为额外 minimal blockers。
- `COMPUTED` 辅助反例搜索：独立 powerset 枚举了底集大小至 7 的 92,815 个有效四集合 clutters；未发现少于 8 个 blockers 的反例。该检查不作为证明依赖。

五生成集定理审查通过：

- incidence degree 至多 2、交图 matching number 至多 1，以及“空图／星／三角形加孤立点”分类完备。
- 星和三角形计数均按实际点 subsets 计数；固定交点及其余选择各有 private witness，不会因重复 incidence pattern 合并。

六生成集定理审查通过：

- degree 3 情形的后三集合两两不交，产生至少 \(2^3\) 个 blockers。
- degree 至多 2 时，loops 表示 singleton incidences，parallel points 保留为不同实际点；三点 cover 等价于三个 support-disjoint nonloop edges，故 \(\tau\ge4\iff\nu\le2\)。
- \(\nu=2\) 的核心计数正确：
  - 基本生成族大小为 \(m_1m_2d(u)d(v)\)。
  - 小于 6 只可能 \(m_1=m_2=1,d(u)=d(v)=2\)。
  - 第二 actual matching 与第一生成族的交集：不共享点时至多 1；共享一点且非平行时至多 2；平行时为 0，因此并集至少 6。
  - 若 matching core 唯一，则 \(u,v\) 只能有各两个 loops；分别为 core 两端选择额外 incident points 后，\(\{r_a,r_b,e_2\}\) 确实覆盖整个 core。从中取 minimal core cover \(K\)，与四种 loop choices 组合得到四个避开 \(e_1\) 的新 blockers，与原四个生成成员不重合。
- 候选第 12 节记录的旧错误替换步骤已被上述 core-cover 构造真正修复，不是当前证明中的缺口。

乘积分类的七种情形穷尽 \(b=2,3,4\) 及 \(b\ge5\) 下的 \(a=4,5,6,\ge7\)，每行下界均正确，故 \(ab\ge32\)。随后
\[
(a+b)^2=(a-b)^2+4ab\ge128>11^2
\]
正确给出 \(a+b\ge12\)。

## Witness、split 与全局接口

`PROVED`：

- 两个不交四环的八条边与四个 bipartition-union blockers 满足两条 blocker 等式及大小下界。
- `COMPUTED`：我另用独立 powerset 枚举确认 \(B(\mathcal S)=\mathcal C\) 与 \(B(\mathcal C)=\mathcal S\)。
- 六个冻结未决 split 均由纯组合定理排除；15 个实验 split 与六个数学 split 的区分准确。
- 冻结 G4.3 接口将同一个 \(m(2,4)\) 分别用于 \(A_2,A_4\)，不是假设全局补对称。
- 全局求和
  \[
  1+6+12+9+12+6+1=47
  \]
  正确。因此相对于冻结 canonical-layer 依赖，候选推出 \(sat(7)\ge47\)。

## Prover C 与实验边界

`PROVED`：Prover C 的 incidence quotient 是 iff 归约。multiplicity 保存相同 pattern 的不同实际点；row incomparability 条件恰对应 clutter；\(W(m)\) 计数实际 blocker subsets；inactive points、空 classes、非均匀 row sizes 均未遗漏。

`COMPUTED`：实验的 15 行均记录 `complete_exhaustion=true`、`UNSAT_COMPUTED`，总计 147,340,811 个 DFS nodes；源代码中的小-cover、结构数量和 weighted-count pruning 均具有所述单调性。

`UNKNOWN`：实验没有独立可检查的完整 UNSAT certificate，也没有第二个完整 enumerator。两个 blocker validators 只验证语义与小规模公式。因此实验不能升级为 `PROVED`。候选证明明确不依赖实验，证据标签正确。

```text
FIRST_INVALID_STEP: NONE
VERDICT: ACCEPT
```

此 `ACCEPT` 仅确认冻结候选在本兼容替代 Referee B 审查下 dependency-closed；是否已满足“两份隔离 ACCEPT”及后续状态更新条件，由主 gate 独立核定。
