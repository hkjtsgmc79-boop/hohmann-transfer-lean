# 霍曼轨道转移 H1 + H2 · Lean 4.35.0 迁移

2026-11-13 · 骋原 AI 实验室

## 构建与审计

在独立副本中迁移。Lean 4.35.0 的提交为 `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`，Lake 为 `5.0.0-src+eb6cafb`。对齐 [Physlib 提交](https://github.com/leanprover-community/physlib/tree/adccea9195c7c347a5f8cde1ddf6874f89ea6a9a) 固定的 Mathlib `56a005855ea17e0b0958f73ec801ae140b0a1679` 及其八个传递依赖。验证器核对了实际 checkout 的提交和跟踪文件状态，读取已有的 Mathlib 编译缓存。

验收记录在回传包的 `verification/core/` 与 `verification/full/`。两次验证在各自新建的构建目录中执行。完整验证涵盖 23 个主体模块、各入口、算例、两个独立单文件和 22 项公理审计。审计允许 `propext`、`Classical.choice` 和 `Quot.sound`。原始命令、输出和退出码见各目录的 `verification.json` 与日志。

## 源码改动

- `KeplerConservation` 显式证明 `convert` 在 4.35.0 生成的函数等式，并对半径导数展开逐点加法与幂。
- `KeplerClock` 直接应用除以常数的求导规则。`Differentiation` 和 `Circular` 分别处理函数等式和导数值等式。
- `H1Bridge` 在已有的下界证明上逐项改写单位。`BiellipticWitness` 在时间平移的链式法则中显式化简单位标量。这样避开了新版 `simpa` 对定义等价实例的匹配问题。
- `lean-toolchain`、`lakefile.toml`、`lake-manifest.json` 和 `dependency-lock.json` 固定新版依赖。验证器逐项检查已安装依赖。

`MIGRATION_SEMANTICS.json` 比较 4.30.0 已验证版和本版的 23 个模块。所有既有定理、引理陈述和关键定义匹配。公开定理文件、原合同和 H1 基线 ZIP 按字节核对。具体差异见 `LEAN435_MIGRATION.diff`。

## 验证范围

- H1 含真实开普勒时钟和牛顿方程、两次切向脉冲、转移时间与守恒量。
- H2 含同平面同向圆轨道间的两脉冲全局下界、显式霍曼轨迹在比较类中达到下界，以及取等时的端点速度条件。
- 双椭圆见证含 1 → 64 → 16 的两段真实滑行、三次速度跳变及严格 Δv 差大于 9/1000。
- 双椭圆与霍曼的飞行时间比值仍属于原数值比较。此处验证范围为对齐 Physlib 依赖的独立工程。

复跑方法见 `BUILD_VERIFIED.md`。Lean 4.30.0 验证包独立保存，其 SHA-256 为 `13cbef92b4479776c6871ec108c601be6bd69aceb5c4dc44f2965fcd23132afa`。
