<div align="center">
  <h1>饱和 6-与 7-Sperner 数的精确值</h1>
  <p><a href="README.md">English</a> · <strong>简体中文</strong></p>
  <p>
    <img src="https://img.shields.io/github/last-commit/lailai0916/saturated-sperner-6-7?style=flat-square" alt="最后提交" />
    <img src="https://img.shields.io/github/languages/top/lailai0916/saturated-sperner-6-7?style=flat-square" alt="主要语言" />
    <img src="https://img.shields.io/github/repo-size/lailai0916/saturated-sperner-6-7?style=flat-square" alt="仓库大小" />
    <img src="https://img.shields.io/github/license/lailai0916/saturated-sperner-6-7?style=flat-square" alt="许可证" />
  </p>
</div>

## 项目简介

本仓库收录 Jiazhi Chen 论文《The exact saturated 6- and 7-Sperner numbers》
的数学证明、Lean 4 形式化和可复现工件。

对固定正整数 `k`，令 `sat(k)` 表示充分大布尔格中饱和 `k`-Sperner 族的
最终稳定最小大小。本文证明

\[
\operatorname{sat}(6)=30,
\qquad
\operatorname{sat}(7)=55.
\]

Lean 中对应的最终定理为：

```lean
AiMathLab.P0054.Sat6StableExact.sat_six_eq_thirty
  : IsStableSaturationNumber 6 30
AiMathLab.P0054.Sat7StableExact.sat_seven_eq_fifty_five
  : IsStableSaturationNumber 7 55
```

`IsStableSaturationNumber k s` 的含义是：存在阈值 `N`，使每个 `n ≥ N`
上都有大小为 `s` 的饱和 `k`-Sperner 族，且任意这样的族至少有 `s` 个
成员。这是带全局量词的命题，并不是对名为 `sat` 的 Lean 数值函数求值。

仓库严格区分数学证明、有限计算和 Lean 内核验证，使每项结论都能在恰当的证据层级上复核。

## 项目特性

📐 **精确极值** — 形式化结果证明充分大的布尔格中 `sat(6)=30`、`sat(7)=55`。

🧠 **Lean 4 形式化** — 主要定理及其支撑构造由 Lean 和 mathlib 检查。

🧪 **可复现验证** — Python 测试、确定性生成器、求解器证书和 Lean 构建提供多条独立重放路径。

🗂️ **证据边界** — 明确区分 PROVED、COMPUTED、FORMALIZED 与 UNKNOWN，不把它们当作同等证据。

## 快速开始

安装 Python 3.12、[uv](https://docs.astral.sh/uv/) 和由
[elan](https://github.com/leanprover/elan) 管理的 Lean，然后运行：

```bash
uv sync --locked --python 3.12
uv run ruff check .
uv run mypy
uv run pytest
lake build AiMathLab AiMathLab.P0054Sat7StableExact
lake env lean Problems/P0054/formal/Main.lean
```

统一重放入口为：

```bash
Problems/P0054/release/verify-core.sh
```

## 项目结构

```bash
saturated-sperner-6-7/
├── AiMathLab/                      # Lean 定义与形式化定理
├── artifacts/                      # 归档工件的完整性边界
├── Problems/                       # 证明、实验与发布材料
├── scripts/                        # 生成器与语义验证器
├── tests/                          # 回归与重放测试
├── AiMathLab.lean                  # 根 Lean 模块
├── CITATION.cff                    # 机器可读引用信息
├── lakefile.toml                   # Lake 构建配置
├── pyproject.toml                  # Python 工具配置
└── uv.lock                         # 锁定的 Python 依赖
```

## 证据分级

仓库严格区分三类证据：

- **PROVED**：正文或证明笔记中给出了数学证明；
- **COMPUTED**：有限计算或求解器结果只在记录的范围内成立；
- **FORMALIZED**：Lean 在报告的公理依赖下接受相应定理。

上述两个精确稳定值同时属于 **PROVED** 和 **FORMALIZED**。发现阶段的搜索、
超时和历史计算仍按 **COMPUTED** 或 **UNKNOWN** 标注，不能替代证明。最终文献
检索只说明在已记录范围内没有发现公开等价结果，不构成绝对的创新性或优先权声明。

## 验证细节

需要 Python 3.12、[uv](https://docs.astral.sh/uv/) 和由
[elan](https://github.com/leanprover/elan) 管理的 Lean。锁定版本为 Lean
`v4.33.0-rc1` 与 mathlib `v4.33.0-rc1`。

```bash
uv sync --locked --python 3.12
uv run ruff check .
uv run mypy
uv run pytest
lake build AiMathLab AiMathLab.P0054Sat7StableExact
lake env lean Problems/P0054/formal/Main.lean
```

本轮修订还提供统一重放入口。脚本会保存完整日志，并输出机器可读摘要：

```bash
Problems/P0054/release/verify-core.sh
```

独立入口会打印两个最终定理的公理依赖；预期恰为 `propext`、
`Classical.choice` 和 `Quot.sound`。Lean 源码不含 `sorry`、`admit`、
`axiom`、`unsafe`、`native_decide` 或 `run_tac`。

严格 mypy 门覆盖人工维护的验证器和测试层。机械式 Lean 代码生成器由确定性
重放、生成结果比对、Python 测试和最终 Lean 内核构建检查；仓库不会把它们误写成
已经完成全量类型标注。

## 目录与归档说明

- `AiMathLab/`：Lean 定义、证书、归约与最终定理；
- `Problems/P0054/formal/`：独立入口、陈述对照表和形式化报告；
- `Problems/P0054/paper/`：论文与投稿材料；
- `Problems/P0054/proof/`：自然语言证明过程与审计；
- `Problems/P0054/experiments/`：精确搜索输入、输出和紧凑证书；
- `scripts/`、`tests/`：生成器、语义验证器和回归测试。

超过 GitHub 普通文件上限的 DRAT 轨迹不进入源码 Git 历史。本轮对应的源码、PDF
和九组 CNF/DRAT 文件发布于 [版本 `v1.1.2`](https://github.com/lailai0916/saturated-sperner-6-7/releases/tag/v1.1.2)，
并以 [Zenodo DOI `10.5281/zenodo.21770438`](https://doi.org/10.5281/zenodo.21770438)
归档。旧 `v1.0.0` 与 DOI `10.5281/zenodo.21679078` 仍作为不可变历史版本保留。
完整性边界见 [`artifacts/README.md`](artifacts/README.md)。
纯源码克隆中有五项逐字节归档测试会明确显示为跳过；将归档文件放回对应路径后，
设置 `P0054_REQUIRE_ARCHIVE_ARTIFACTS=1`，任何缺失文件都会成为硬失败。

## 许可协议

引用信息见 [`CITATION.cff`](CITATION.cff)。本修订 DOI 为
[`10.5281/zenodo.21770438`](https://doi.org/10.5281/zenodo.21770438)。
代码与形式化源码采用 Apache-2.0 许可证。
