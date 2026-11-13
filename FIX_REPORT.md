# 霍曼轨道转移 H1 + H2 验收报告

2026-11-13 · 骋原 AI 实验室

## 验收结论

本机 Lean 4.30.0 在独立构建目录运行 `core` 和 `full`。最终结果、命令、退出码和日志哈希见回传包的 `verification/core/verification.json` 和 `verification/full/verification.json`。`full` 覆盖 23 个模块、各入口、算例、两个独立单文件和 22 项公理审计。通过的审计仅依赖 `propext`、`Classical.choice`、`Quot.sound`。

输入为 Drive 指定的 `Hohmann_Transfer_H1_H2_FULL_20261113.zip`，202,196 字节，SHA-256 为 `8b92ca5b6929741a52c47f017b8b986bf588b6c8d4e5b2a679c56ff4bb9d1996`。先核对下载包，再从独立工作副本修复。包内原始 H1 ZIP 与三个合同文件均按原始字节保留。

## 已内核验证

| 公开定理 | 核对内容 |
|---|---|
| `HohmannTransfer.hohmann_transfer`、`HohmannTransfer.exists_hohmann_transfer` | 任意 μ > 0、0 < r₁ < r₂。真实逆时钟、椭圆和圆轨道的牛顿方程、两次切向脉冲、飞行时间及守恒量。 |
| `HohmannOptimality.global_two_impulse_endpoint_optimality` | 端点松弛可行集合上的全局下界及等号条件。两个脉冲各自的下界在 `endpoint_impulses_lower_bound`。 |
| `HohmannOptimality.global_two_impulse_newton_lower_bound` | 对任意同平面同向圆轨道之间的有效两脉冲滑行段，从牛顿方程推导守恒量，再下界两次实际欧氏速度变化之和。 |
| `HohmannOptimality.h1_global_two_impulse_minimum`、`HohmannOptimality.h1_attains_bound_in_kepler_class` | 显式 H1 轨迹具有霍曼成本，并给出比较类 `KeplerArc` 中实际取到下界的见证。 |
| `HohmannOptimality.KeplerArc.newton_arc_equality_endpoints` | 真实欧氏成本取等时，两个端点径向速度均为零，切向速度为霍曼值。允许整体旋转及额外绕行。 |
| `HohmannOptimality.finite_three_impulse_counterexample`、`HohmannOptimality.BiellipticWitness.physical_three_impulse_counterexample` | 1 → 64 → 16 的两段实际椭圆滑行、连接位置与三个实际速度跳变。与 1 → 16 霍曼转移相比，严格 Δv 差大于 9/1000。 |
| `HohmannOptimality.newton_arc_ideal_fuel_lower_bound` | 固定正排气速度的理想火箭模型下，消耗比例随总 Δv 单调。 |

## 修改清单与语义核对

- `Shape`、H1 的 `Parameters`、`Plane` 及 API 探针改为导入所用的 Mathlib 模块。导出器按模块收集这些导入。
- `PhysicalUnits` 修正分母化简。`KeplerConservation` 用真实导数及明确的端点参数完成守恒，并新增真实成本等号定理。`Examples.lean` 明确引用项目的单位结构及参数。
- `Bielliptic` 用 `«example»` 引用 Lean 保留字作为原来的标识符，保留半径 16、64 及全部成本表达式。固定根式形态以便使用有理数界和绝对值符号证明。
- H1 的 `Differentiation`、`Circular` 修复复数坐标链式求导。`Endpoints` 明确根式的正性见证。`Transfer` 用两条端点方程求和，完成椭圆参数唯一性的代数步骤。
- `H1Bridge` 修复速度单位转换及代数改写，并用复数实部、虚部的连续线性映射把显式滑行装入 `KeplerArc`。`BiellipticWitness` 用链式法则核对第二段的时间平移，并精确核对三次跳变范数。
- 验证器读取匹配固定版本的独立缓存，记录工具链、依赖清单和原始日志。H1 源码在工作副本中修复，原 H1 ZIP 仍按字节保存。原工具测试中对工作源码的字节比对改为定理头部比对，另外核对归档 ZIP 的哈希。

`SEMANTIC_COMPARISON.json` 和 `LEAN_REPAIRS.diff` 提供原稿对照。23 个模块中的原有定理和引理陈述、比较集合及关键定义均一致。文本比较只规范化空白与 `«example»` 的标识符引用，并将 `endpoints` 定义中的两个守恒证明字段作为证明体处理。H1 公共入口文件逐字节一致。原合同中未转义的保留字在回归检查时按同一标识符比较。

## 精确环境与复跑

- Lean `4.30.0`，提交 `d024af099ca4bf2c86f649261ebf59565dc8c622`。
- Lake `5.0.0-src+d024af0`。
- Mathlib `c5ea00351c28e24afc9f0f84379aa41082b1188f`。实际 checkout 的提交、干净状态、依赖清单和既有缓存的回放凭据已核对。缓存来自已有的三体 R5 回放，当前验收重新编译全部项目模块，复用已编译的 Mathlib。

在解压后 `project/` 中，用对应 Lean 与 Mathlib 的本机实际路径执行：

```sh
bash scripts/verify.sh core --lean /path/to/lean --mathlib-root /path/to/mathlib
bash scripts/verify.sh full --lean /path/to/lean --mathlib-root /path/to/mathlib
```

若 Mathlib 源码与编译缓存分开存放，追加 `--cache-root /path/to/cache --cache-receipt /path/to/replay/verification.json`。本次实际参数及每条命令见验证 JSON。所有公开陈述和关键定义可用 `python3 scripts/check_contracts.py /path/to/original .` 对照。

## 仅有计算检查的部分

原交接记录中的 13 条符号恒等式、2,688 组端点、42 组霍曼等号端点、3 次独立 ODE 积分和 6 个负对照在 `verification/original-checks/`。飞行时间约为 17.685 倍及 Δv 百分比来自数值比较。严格 Δv 间隔和两段牛顿动力学另有 Lean 证明。16 项本机工具测试只检查交付和审计工具。

## 仍未完成

跨机器独立复跑、4.35.0 迁移和 Physlib 上游审查属于后续工作。当前结果限定于指定的固定中心、同向圆轨道和脉冲模型。
