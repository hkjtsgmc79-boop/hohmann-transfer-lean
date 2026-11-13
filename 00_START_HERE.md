# 霍曼最优性 H2｜电脑端入口

**交付状态：数学推导和 Lean 候选证明已写出；未通过 Lean 编译。**
H1 旧版源码完整保留，不需要重新下载旧工程。本轮不修改你的三体、量子隧穿或芝诺项目。

## 1. 要验证的两个不同结论

**A. 两次脉冲范围内：** 固定中心天体、牛顿点引力、同平面同向圆轨道、0<r₁<r₂、自由飞行时间与端点相位。对任何有效的两次瞬时点火转移，霍曼转移具有最小总 Δv。竞争轨迹不预设为椭圆、不预设点火切向，也不预设正角动量。

**B. 放宽到三次脉冲：** μ=r₁=1、r₂=16、中间远地点64，存在有限双椭圆转移，总 Δv 严格比霍曼小；它不是去往无穷远的极限构造。

“最省燃料”只作为理想单级、固定正喷气速度、同初始质量等假设下的推论；核心目标函数始终是各次欧氏速度跳变范数之和。

## 2. 环境

- Lean: `leanprover/lean4:v4.30.0`
- Mathlib commit: `c5ea00351c28e24afc9f0f84379aa41082b1188f`
- Python 3.10+ 用于交接脚本。
- 非 Lean 的数学检查需要 SymPy、NumPy、SciPy；无需为了 Lean 构建安装这些包。

脚本只使用已经安装的工具链与已编译 Mathlib 缓存。不下载、不自动安装、不升级、不更改共享 Mathlib 缓存。

## 3. 推荐执行顺序

在包含 `lean-toolchain` 的新解压目录运行：

```bash
bash scripts/verify.sh core --lean /实际路径/bin/lean --mathlib-root /实际路径/mathlib
```

也可设置 `LEAN_BIN` 和 `MATHLIB_ROOT` 后运行 `bash scripts/verify.sh core`。Lean 在 PATH 上时可不传 `--lean`。

核心修复并通过后：

```bash
bash scripts/verify.sh full --lean /实际路径/bin/lean --mathlib-root /实际路径/mathlib
```

每次运行使用新的 `.build-local/<runid>`，避免沿用本项目的旧 olean。不要求 `lake update`。本轮默认入口是核心库；仅执行普通 `lake build` 不等于完整验收。

## 4. PASS 的含义

- `core PASS`：新下界、ODE 到下界、有限反例的精确成本比较、示例、核心单文件及16条重点公理审计通过。
- `full PASS`：再加H1全部轨迹模块、霍曼实际轨迹取到下界、双椭圆实际轨迹与三个速度跳变、完整单文件及2条额外审计通过。
- `BLOCKED`：工具链/缓存/版本未满足；不是通过，也不一定是数学错误。
- `FAIL`：源码编译、公理依赖、固定命题或其他检查失败；保留日志并修复。

公理允许集合：`propext`、`Classical.choice`、`Quot.sound`。没有自行添加的动力学或最优性公理。

## 5. 回传

脚本自动生成 `reports/Hohmann_Transfer_H2_return_<scope>_<runid>.zip`，包含当前源码、构建命令、退出码、源码哈希、日志和公理输出。阻塞或失败也会生成回传包。

请回传最后一次真实运行的包，而不是只发成功截图。修复过程中不得弱化主定理、改动比较集合或把守恒/最优性藏进假设。关键边界见 `docs/SEMANTIC_CONTRACT.md`。
