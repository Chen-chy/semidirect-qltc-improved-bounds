# 命题与外部输入的依赖关系

[主定理](THEOREM.zh-CN.md) · [机器可读索引](../claims.json) · [固定文献版本](../REFERENCES.md)

“手工证明”表示正文给出了数学论证，不表示同行评审或 Lean 验证。“外部输入”必须按指定论文版本阅读；仓库没有用新公理伪装其形式化完成。

| ID | 结论或输入 | 使用位置 |
| --- | --- | --- |
| EXT-KL | 经典码、对称群族及其固定参数输入 | R1；证明 §3 |
| EXT-KP | 同时 product expansion、子元组继承 | R2；证明 §5 |
| EXT-DLV | 局部鲁棒性接口、全局转移、修正版 shifting | R3；证明 §5–7 |
| G1 | 子群、精确计数、处处自由及 $\eta=b^{-2}$ | [§2](PROOF.zh-CN.md#geometry) |
| E1 | lazy 半直积谱范数估计 | [§3](PROOF.zh-CN.md#spectral) |
| E2 | 固定标签群提升，无直接删重 | [§4](PROOF.zh-CN.md#labels) |
| L1 | 局部矩阵与非循环参数选择 | [§5](PROOF.zh-CN.md#local-codes) |
| C1 | 实际面、系数 incidence、$\delta^2=0$ | [§5.1](PROOF.zh-CN.md#cubical-complex) |
| D1 | 两距离 $\Omega(\eta N)$、两全局扩张 $\Omega(\eta)$ | [§6](PROOF.zh-CN.md#global-transfer) |
| RATE1 | shifting 只转移维数，导出正码率 | [§7](PROOF.zh-CN.md#rate) |
| B1 | 二元展开、CSS 交换、单个 $\ell$ 因子、局部性 | [§8](PROOF.zh-CN.md#binary-css) |
| Q1 | centralizer 距离与 syndrome 算子不等式 | [§9](PROOF.zh-CN.md#quantum-tester) |
| A1 | 固定局部数据与对数平方换算 | [§10](PROOF.zh-CN.md#asymptotics) |
| T4 | 同一个码族同时满足全部主参数 | [主定理](THEOREM.zh-CN.md) |

## 关键接口

经典码的良好性不自动推出 $Q_B$ 扩张，也不提供所需局部张量鲁棒性。标签提升保留的是真正生成元集合的谱控制，不能用“删除重复项”替代。DLV 的方向图输入允许多个大分量，本文代入的是基点集合上的 $\eta$，不是带 flags 顶点集合中未说明的归一化。

全局 cycle 扩张公式是两个量的最小值；两个量各自为 $\Omega(\eta)$，不是彼此相乘。正率只使用修正版 shifting 的维数等式，不假定它保 Hamming 重量。场矩阵的二元展开与普通转置不能随意交换；本文按实际二元矩阵及迹对偶基处理。

## 形式化仍缺什么

[Lean 证明边界](../formalization/lean4/docs/PROOF_BOUNDARY.zh-CN.md) 中的未完成项保持开放，包括外部输入的形式化、实际立方链到现有模块的构造、shifting 等价、量子投影算符，以及对整个无限族的一致选择。`t4_parameters_from_certificates` 是显式带前提的参数定理源码，不是闭合的存在性定理。
