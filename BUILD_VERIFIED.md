# 霍曼转移 H1 + H2 本机复跑

`FIX_REPORT.md` 为当前验收报告。原来的 `00_START_HERE.md`、`01_LOCAL_CODEX_PROMPT.txt`、`H2_REPORT.md` 和数学规格记录的是交接时状态。

需要 Lean 4.30.0、同工具链的 Lake、Mathlib Git 提交 `c5ea00351c28e24afc9f0f84379aa41082b1188f` 及其已编译缓存。从本目录执行：

```sh
bash scripts/verify.sh core --lean /path/to/lean --mathlib-root /path/to/mathlib
bash scripts/verify.sh full --lean /path/to/lean --mathlib-root /path/to/mathlib
```

脚本逐次创建新的项目构建目录，并保存源码哈希、所有命令及输出。使用独立还原的 R5 缓存时，传入 `--cache-root` 和 `--cache-receipt`。两次验收记录在回传包的 `verification/core/` 和 `verification/full/`。
