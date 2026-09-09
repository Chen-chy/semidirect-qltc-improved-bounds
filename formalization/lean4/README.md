# Lean 4 草稿：未编译、未完成

本目录保留此前针对 $t=4,j=2$ 写出的 Lean 源码。**没有通过内核检查，也没有完成完整存在性定理。** 数学正文位于 [PROOF](../../docs/PROOF.zh-CN.md)；不要把数学核验与这里的代码状态混同。

源码目标版本为 Lean `4.19.0`、mathlib `v4.19.0`，不是“最新版”声明。`T4/MainConditional.lean` 的主要命题为 `SemidirectQLTC.T4.t4_parameters_from_certificates`。全局双扇区估计、实际链、shifting 等价等仍是它的显式前提。

在具有固定 Lean 工具链、可获取 mathlib 的环境中，从本目录运行：

```bash
lake update
lake exe cache get
python tools/verify.py --scope modules
```

上述命令会实际构建模块并检查公开命题的传递公理依赖；它尚不保证编译成功。输出位于本目录被忽略的 `verification/`。`lake-manifest.json` 在依赖第一次真正解析后生成；没有伪造一个已解析的锁文件。首次成功解析后应审阅并提交锁文件，必要时调整根 `.gitignore`。

完整形式化目标的验收命令是：

```bash
python tools/verify.py --scope full
```

当前完整目标应失败。即使模块全部编译成功，完整存在性命题和必要语义核验仍没有实现。`--scope modules` 的成功不能提升成 `--scope full` 的成功。

[证明边界](docs/PROOF_BOUNDARY.zh-CN.md)、[未完成义务](docs/obligations.json)、[历史构建记录](../../provenance/lean_attempt/status.json) 和 [构建错误](../../provenance/lean_attempt/build.log) 均保留。根目录普通 CI 不安装 Lean，也不执行或伪装上述构建。

本目录的 `.lean` 证明内容未在发布整理中修改；[原始源码哈希](../../provenance/lean_source_hashes.json) 可核对其身份。以后修正源码时应记录实际编译器版本、构建日志、公理审计和命题语义范围，而不是只更新状态文字。
