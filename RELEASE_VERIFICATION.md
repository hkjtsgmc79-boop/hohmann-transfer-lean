# 霍曼轨道转移 H1 + H2 验收报告

**作者：马千里（Qianli Ma）** · 骋原 AI 实验室

**版本：v0.2.1**

## 已通过 Lean 内核验证

- 全新构建目录分别执行 `core` 和 `full`。验证覆盖 23 个主体模块、公开入口、算例及两个独立 Lean 单文件。
- H1 构造正质量参数下的向外霍曼转移轨迹，验证牛顿方程、守恒量、两次切向脉冲和飞行时间。
- H2 证明固定中心引力场内同平面同向圆轨道间的两脉冲全局下界，给出实际达到下界的霍曼轨迹与端点取等条件。双椭圆见证验证 `1 → 64 → 16` 的两段滑行与三次速度跳变，严格节省超过内侧圆轨道速度的 `9/1000`。
- `AuditFull.lean` 核查全部 358 个显式命名声明，依赖限于 `propext`、`Classical.choice`、`Quot.sound`。
- 本版源码与此前 Lean 4.35.0 验证版的 23 个模块在文件头注释之后逐字节一致。与 4.30.0 版的声明和关键定义核对见 `RELEASE_SEMANTICS.json`。原合同及 H1 源码归档保持原样。

工具链为 Lean 4.35.0（`eb6cafb7290e8bd5f2937522d8d804f58f02bafc`）和 Mathlib `56a005855ea17e0b0958f73ec801ae140b0a1679`。项目模块从源码重新编译，依赖使用已有的固定版本缓存。原始命令、输出、退出码和哈希见 `verification/core/` 与 `verification/full/`，复跑方法见 `BUILD_VERIFIED.md`。

## 计算检查与上游状态

双椭圆与霍曼的飞行时间倍数和 Δv 百分比来自数值比较。16 项 Python 工具测试覆盖源码导出、合同与审计日志解析。PhyslibAlpha 集成单独跟踪于 [Draft PR #2077](https://github.com/leanprover-community/physlib/pull/2077)。
