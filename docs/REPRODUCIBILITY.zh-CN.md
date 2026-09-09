# 复现说明

## 环境与统一入口

Python 3.10+、标准库。无需 pip 安装、GPU、数据库或第三方数学软件。固定的 Lean/mathlib 环境仅与独立形式化草稿相关，不是有限复算的依赖。输入和参考结果均在仓库内；普通复算不联网。

```bash
python scripts/verify.py
```

从仓库根目录执行。运行日志、程序输出、摘要及各步骤退出码写入 `.artifacts/verification/`。命令拒绝优化模式，因为 `assert` 必须被执行；不要使用 `python -O` 或设置 `PYTHONOPTIMIZE`。

## 可单独运行的检查

```bash
python scripts/check_repository.py
python -m unittest discover -s tests -v
python experiments/semidirect_sanity.py --output .artifacts/geometry.json
python experiments/check_t4_chains.py --output .artifacts/chains.json
python experiments/check_parameters.py --output .artifacts/parameters.json
```

几何程序枚举整个 $P^4$ 和所有左陪集，逐陪集验证作用良定义、跨方向交换、每一点的自由性和非正规性见证。链程序真正构造微分的二元列位向量，用整数 XOR 做精确消元，逐列检查相邻微分复合为零，并对方向 $\{3,4\}$ 的对偶局部矩阵重新构建 shifted 复形。

单元测试包含小型 GF(2) 消元的独立穷举、核基正交性、群律、输入校验和小型 CSS centralizer 度量恒等式。参数程序使用整数及 `Fraction` 核对显示常数的代换，不用浮点数作为证明证书。

## 参考结果

| 局部度数 | 原局部行数 | 原/shifted 同调维数 |
| --- | --- | --- |
| 2 | $(1,1,1,1)$ | $(2,8,12,8,2)$ |
| 3 | $(1,1,2,2)$ | $(10,64,140,64,10)$ |

两例均有 $N=32$。逐次数链维数、微分秩和逐列平方零计数保存在 [只读链基准](../verification/baseline/chains.json)。耗时不是数学输出，跨机器比对时忽略；其他结构字段必须精确匹配。

不能为了通过测试直接重写基准。修改构造时，应说明变更、独立核对新矩阵，并在代码评审中单独更新基准及来源记录。

## CI 的实际范围

[checks.yml](../.github/workflows/checks.yml) 对 push、pull request 和手动触发运行同一个统一入口，计划覆盖 Python 3.10 和 3.13。CI 不安装 Lean，不把有限测试作为主定理验证，不写入仓库，不自动创建 Release。本次本地交付没有执行远端 GitHub Actions。

GitHub Actions 依赖按明确版本配置，并由 Dependabot 提供后续更新建议；版本更新应人工审阅。普通 Python 测试本身不需要联网。CI 的代码检出与 Python 安装需要 GitHub 提供的运行环境。

## 发布快照的完整性

`MANIFEST.sha256` 列出本次发布快照的文件哈希；它证明文件身份，不证明数学正确性。检查与更新命令为：

```bash
python scripts/manifest.py --check
python scripts/manifest.py --write
```

只有在主动修改并审阅仓库后才执行 `--write`；不要在完整性检查失败时用它掩盖未知改变。常规 CI 不要求此历史快照清单在每次开发提交后同步；准备新的 Release 时再更新。运行时 `.artifacts/`、`.git/`、字节码、Lean 缓存和自动生成的运行日志不纳入清单。
