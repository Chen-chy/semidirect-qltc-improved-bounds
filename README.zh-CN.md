# 改进 qLTC 的半直积构造：距离与 soundness 少一个对数损失的研究方案

[English](README.md) · [主定理](docs/THEOREM.zh-CN.md) · [证明正文](docs/PROOF.zh-CN.md) · [复现说明](docs/REPRODUCIBILITY.zh-CN.md)

**我们提出一个四维半直积 qLTC 构造，在保持常数码率和常数校验重量的同时，将 DLV 基准的距离与全局 soundness 下界中的对数损失从三次方改善为二次方。** 这是研究草稿提出的结论，一般论证仍待独立核验；下文的有限测试不能证明渐近结论。

范围为 **$t=4,j=2$**，核心参数为

$$
k=\Theta(n),\qquad d_X,d_Z=\Omega\!\left(\frac{n}{(\log n)^2}\right),
$$
$$
m=\Theta(n),\qquad w_{\max},\Delta_{\max}=O(1),\qquad
\rho=\Omega\!\left(\frac1{(\log n)^2}\right).
$$

这是固定局部数据、指定无限码长序列上的二元 CSS 构造。证明使用已列明的经典码、局部乘积扩张与 DLV 转移/shifting 定理；本文的半直积商几何给出方向分量比例 $\eta=b^{-2}$，再由 $b=\Theta(\log n)$ 得到对数平方参数。见[定理的完整量词与定义](docs/THEOREM.zh-CN.md)。

**验证边界：数学证明稿、有限结构测试、Lean 草稿是三个不同层次。** 本仓库不宣称完整定理已通过 Lean 内核检查，不宣称同行评审、新颖性或指数最优性。普通 CI 检查代码、文档及有限样本，不验证渐近存在性定理。

## 核心结果：两个下界同时改善一个对数因子

| 构造 | 逻辑比特数 | 距离下界 | 全局 soundness 下界 | 校验重量 |
| --- | --- | --- | --- | --- |
| DLV，arXiv:2402.07476v3，Theorem 1.1 | $\Theta(n)$ | $\Omega(n/\log^3 n)$ | $\Omega(1/\log^3 n)$ | $O(1)$ |
| 本研究稿，四维半直积构造 | $\Theta(n)$ | $\Omega(n/\log^2 n)$ | $\Omega(1/\log^2 n)$ | $O(1)$ |

**比较结论：本稿声称的两个渐近保证均比上述 DLV 基准强一个对数因子。** 这里比较的是定理下界，不是同一码长的实测性能，也不是原构造不可能达到更强下界的证明。几何来源是方向分量比例 $\eta=b^{-2}$，配合 $b=\Theta(\log n)$。

这一结果属于 almost-good qLTC：尚未达到同时线性距离与常数 soundness 的 good qLTC 目标。“全球最好”需要更全面的文献和证明审查，本次发布不作该无条件声明。详见[文献比较与范围](docs/COMPARISON.md)。

## 内容导航

| 内容 | 入口 |
| --- | --- |
| 定理、固定参数、两个逻辑距离与全局 tester | [THEOREM](docs/THEOREM.zh-CN.md) |
| 几何、标签提升、立方链、扩张、码率、二元化和量子态证明 | [PROOF](docs/PROOF.zh-CN.md) |
| 外部定理的版本、依赖图及使用位置 | [DEPENDENCIES](docs/DEPENDENCIES.zh-CN.md)、[REFERENCES](REFERENCES.md) |
| Python 标准库复算和只读基准 | [REPRODUCIBILITY](docs/REPRODUCIBILITY.zh-CN.md) |
| 机器可读状态及命题索引 | [STATUS.json](STATUS.json)、[claims.json](claims.json) |
| 未编译、未完成的 Lean 4 模块 | [formalization/lean4](formalization/lean4/README.md) |
| 发布步骤、署名和许可状态 | [PUBLISHING](docs/PUBLISHING.zh-CN.md)、[RIGHTS](RIGHTS.md) |

## 一条命令复算

在仓库根目录，使用 Python 3.10 或以上版本；不需要第三方 Python 包：

```bash
python scripts/verify.py
```

结果写入被 Git 忽略的 `.artifacts/verification/`，不会覆盖 `verification/baseline/`。命令返回成功只表示 **仓库检查、单元测试及有限结构复算成功**。它不运行 Lean。不要使用 `python -O`，因为有限证明检查使用断言；入口会拒绝优化模式。

有限实验使用 $A=\mathbb F_2^2$、$Q=C_2$ 的位交换作用，验证 $|\Lambda|=128$、$|X|=32$、每方向四个大小为八的轨道，并实际构造两个四维复形，检查 $\delta^2=0$、微分秩与 shifting 前后的同调维数。小样本没有被声称满足主定理需要的鲁棒性和谱常数。

## 全局可测试性的含义

对任意 Pauli 误差 $E$，均匀抽测实际列出的校验，有

$$
\Pr[\operatorname{reject}E]\ge
\rho\,\frac{\delta(E)}n,\qquad
\delta(E)=\min_{C\in\operatorname{Cent}(\mathcal S)}\operatorname{wt}(EC).
$$

这里是 **centralizer 距离**，不是到稳定子群的距离；没有误差重量或 syndrome 大小限制。任意量子态版本使用同一 syndrome 距离 observable，见[证明 §9](docs/PROOF.zh-CN.md#quantum-tester)。

## 非目标与发布状态

不包含其他维数的端点研究，不提供完整渐近码族的显式生成程序，也没有提供已经认证的大型鲁棒局部矩阵、解码器或通过内核检查的存在性证明。局部对象的存在性来自明确列出的文献输入。

当前版本为 `0.1.0-draft`，是待维护者发布的研究快照，不是已经创建的 GitHub Release。作者、机构、仓库地址、DOI 和项目许可证均未擅自填写。第三方论文只作引用，不随包分发。见 [来源与改动](provenance/README.md) 和 [许可状态](RIGHTS.md)。
