# 霍曼转移 H1 + H2 在 Lean 4.35.0 上复跑

本副本使用 Lean 4.35.0 和 Physlib 固定的 Mathlib 提交。迁移与验收见 `MIGRATION_REPORT.md`。`FIX_REPORT.md`、`00_START_HERE.md`、`01_LOCAL_CODEX_PROMPT.txt` 、`H2_REPORT.md` 和 `docs/ORIGINAL_README.md` 记录交接与 4.30.0 验收。

需要 Lean 4.35.0、同工具链的 Lake，以及已编译的 Mathlib 与传递依赖。依赖版本见 `dependency-lock.json`。若这些依赖已在 Physlib 或本工程的 `.lake/packages/` 下，进入本目录并运行：

```sh
bash scripts/verify.sh core --lean /path/to/lean --mathlib-root /path/to/.lake/packages/mathlib
bash scripts/verify.sh full --lean /path/to/lean --mathlib-root /path/to/.lake/packages/mathlib
```

`--mathlib-root` 默认为本工程的 `.lake/packages/mathlib`。使用本工程自己的依赖目录时，可在项目根目录按随包的 `lake-manifest.json` 获取固定依赖，并运行 `lake exe cache get` 获取编译缓存，再运行上述验证。核验脚本逐个核对依赖的 Git 提交和工作区状态，每次把本项目编译产物写入新的目录。回传包的 `verification/core/` 和 `verification/full/` 含实际命令、退出码和日志。
