# P0054 G4.4 兼容替代 Referee A 独立报告

## 隔离与冻结复核

- 全程离线、只读；未调用 Formalizer，未读取当前另一位 Referee 的输出。
- `HEAD` 为 `d2c8e3eb81466a3743c736319ef1874920590abc`，与冻结记录一致。
- `review-freeze.json` SHA-256 为 `25a89f111a4a5b1487bbea0a40ca0f738cfacd8dd3b2f55f107f178ab9153149`。
- 清单内全部 18 个文件逐一核对字节数和 SHA-256，均一致；旧 G4.3 referee 文件仅做哈希校验，未读取正文。
- `candidate-proof.md` 最终复核仍为 `5bacfe8e319ce76ac1c8e8e9efa35fe1454cf896ace8c6ee5c10d8f04b2d9832`。
- 本审查未修改仓库。

## 独立数学重建

1. **任意有限 \(U\) 与 blocker 基础**

   两侧空族均被成员大小条件排除。private-witness lemma 直接来自 inclusion-minimality；不同点的 private witnesses 必然不同，因此 \(|T|\le|\mathcal H|\)。这合法推出 \(a\ge4,b\ge2\)，且未限制 \(|U|\)、incidence multiplicity 或成员等势性。

2. **four-set theorem**

   对最小成员 \(E\)，候选的 residual 映射
   \[
   R\mapsto\{x\}\cup R
   \]
   确实在 \(B(\mathcal J_x)\) 与满足 \(T\cap E=\{x\}\) 的原 blockers 之间形成双射。正反方向的命中性和 minimality 都可由 \(E\) 及 residual private witnesses 恢复。

   最小 residual 在 inclusion-minimal reduction 中保留；blocker involution 与 private-witness bound 给出
   \[
   |B(\mathcal J_x)|\ge d_x\ge w_x.
   \]
   assignment 计数满足
   \[
   \sum_xw_x=\sum_jt_jo_j\ge\sum_jt_j^2
   \ge\left\lceil n^2/3\right\rceil.
   \]

   \(n\ge5\) 时下界至少九。\(n=4\) 时：

   - 和值七分支中，trace family 产生一个与 singleton-intersection classes 不交的新 blocker；
   - 和值六强迫 \(t\)-向量为 \(2,1,1\)，三个 omission sets 构成 \(2+1+1\) partition，列出的五个二元 trace blockers 均真实命中、均 minimal，且与 residual classes 不交；
   - 某个 omission set 等于 \(E\) 时的整数最小值表也正确。

   因而四生成集至少有八个 blockers。

3. **五、六生成集定理**

   五生成集情形中，三点 transversal 的禁止条件使点 incidence degree 至多二、交图 matching number 至多一。有限两两相交边族确实只能落在星或三角形结构中；空图、星、三角形三类构造分别给出至少 \(32,8,8\) 个不同 minimal transversals。

   六生成集情形中：

   - 存在 degree-three 点时，余下三个生成集两两不交，直接得到至少八个四点 blockers。
   - degree 至多二时，带环多重图模型保留所有平行实际点；三点 cover 等价于三个 support-disjoint nonloop edges，因此 \(\tau\ge4\) 等价于 \(\nu\le2\)。
   - \(\nu=2\) 时，固定 two-edge matching 得到
     \[
     m_1m_2d(u)d(v)
     \]
     个不同 minimal covers。若少于六，整数条件唯一强迫
     \(m_1=m_2=1,d(u)=d(v)=2\)。
   - 存在第二个 actual matching 时，两生成族交集至多二，故并集至少六。
   - matching 唯一时，未匹配顶点只能带 loops；core 上选择 \(r_a,r_b,e_2\) 后取得避开 \(e_1\) 的 inclusion-minimal core cover，再与 \(u,v\) 的两种 loop choices 组合，给出四个避开 \(e_1\) 的 blockers。它们与原四个全含 \(e_1\) 的 blockers 不交。

   因而六生成集至少有六个 blockers；修复后的 \(\nu=2\) 论证没有遗留缺口。

4. **cardinality 分类与整数取整**

   以下七类穷尽 \(a\ge4,b\ge2\)：

   \[
   b=2,\ b=3,\ b=4,\quad
   b\ge5\text{ 且 }a=4,5,6,\ge7.
   \]

   对应下界分别给出 \(ab\ge32,36,32,64,40,36,35\)，所以
   \[
   ab\ge32.
   \]
   随后
   \[
   (a+b)^2\ge4ab\ge128>121
   \]
   严格推出整数 \(a+b\ge12\)。候选对总和等号与乘积等号的区分正确。

5. **上界 witness**

   两个不交四环的八条边，其 blocker 恰为两个四环各选一个二分部所得的四个四元集合；反向 blocker 也恰为原八条边。因此这是合法的 \((8,4)\) mutual-blocker pair，总数十二。该部分有完整组合证明，不依赖计算 replay。

6. **六个 split 与全局接口**

   \((5,4),(6,4),(7,4)\) 由 four-set theorem 排除；\((5,5),(5,6)\) 由 five-generator theorem 排除；\((6,5)\) 由 six-generator theorem 排除。没有遗漏 ordered split。

   冻结 G4.3 的 \(A_2/A_4\) 接口保留任意有限 \(U\)、mutual-blocker 双等式和实际层 cardinality；\(A_4\) 只是交换接口两侧，不假设全局补对称。故
   \[
   |A_2|,|A_4|\ge12.
   \]
   与其余冻结层界相加：
   \[
   1+6+12+9+12+6+1=47.
   \]
   稳定区间内选择充分大的有限底集和 minimum family 后，
   \(|F|=sat(n,7)=sat(7)\)；新下界没有被反向用于 homogeneous-block 前提，因此量词稳定且无循环。

7. **证据边界**

   有限 incidence-pattern 搜索、15 个 UNSAT rows、blocker engines 和 coverage counters 均未进入上述证明链；它们保持 `COMPUTED`。结论是相对于冻结上游接口的组合证明，不声称 exact \(sat(7)\)、新颖性、优先权或 `FORMALIZED` 状态。

```text
FIRST_INVALID_STEP: NONE
VERDICT: ACCEPT
```
