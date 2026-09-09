# t=4：实际证明边界

## 当前结论

本包没有完成“t=4 半直积 qLTC 完整存在性定理的 Lean 4 验证”。

1. 所有 Lean 文件目前仍是未经编译的证明源码，可能存在类型、实例推导、战术或 mathlib 接口错误。
2. 新的参数定理是显式带前提的条件定理。它不证明实际半直积族满足这些前提。
3. 构建实测因找不到 `lake` 而没有启动；内核检查和公理审计均为 `NOT_RUN`。

这三点彼此独立。即使随后修复环境并使这些模块编译成功，第 2 点仍然存在。

## 已写入源码的对象与命题

### 四方向几何

`T4/Geometry.lean` 直接使用 `Option (Fin 3)` 作为四个方向。
底层是实际半直积群律、实际子群和左陪集空间，而不是假设群阶的参数记录。

- `subgroup_cardinality`：`|Λ| = M^3 b`。
- `coset_cardinality`：`|X| = M b^3`。
- `free_at_every_coset`：每一个陪集上的方向作用自由。
- `orbitMap_injective` 和 `directional_orbit_cardinality`：方向轨道大小为 `M b`。

`component_size_identity` 只证明 `(M*b)*b^2=M*b^3` 的算术恒等式。
它不是轨道商类型的构造与计数证明。谱隙、生成元集合以及图的分量识别尚未在此包中形式化。

### 实际二元表示

`T4/BinaryPresentation.lean` 从同一个 `BinaryChain` 的 `lower` 和 `upper` 矩阵定义：

- 两个实际 syndrome 线性映射；
- 两个实际边界映射及其复合为零；
- 实际商空间 `ker / im` 和其 `Module.finrank`；
- 实际列数、实际列出的行数、实际 syndrome 重量；
- Pauli 支撑并集重量，以及相同 syndrome 类中的最小重量。

因此后面的码长、逻辑维数、tester 和距离来自同一个矩阵表示，不是彼此无关的数值字段。
但是，这个 `BinaryChain` 仍由调用者提供，其 `boundary_squared` 是输入证明字段。
本包尚未从原稿的 flagged 立方复形和局部系数矩阵生成这一链。

### 正率推导

`T4/ShiftedRate.lean` 中的 `rate_from_shift` 使用：

- 原始二元链；
- 一个实际的 shifted 三项链；
- 一个实际线性等价 `e : originalHomology ≃ₗ[F2] shiftedHomology`；
- shifted 链的维数估计。

在这些输入下，源码通过 rank-nullity 推导同调维数下界。
这里没有声明 `e` 必然存在，没有用 `axiom` 引入 shifting，也没有假设它保 Hamming 重量。

`MainConditional.lean` 选择 `ν=1/100`，使用正数

`rateBracket = 2 - (1 + 2/100)^4`。

参数 `ell` 作为二元限制标量的维数因子只出现一次：
shifted 总维数输入包含 `ell*N*degree^4`，码率常数为

`R = ell * degree^4 * rateBracket / κ`，其中 `n=κ*N`。

### 从 B 尺度到真实对数

`T4/Scale.lean` 使用 `Real.log`，不把 `log n` 换成一个未约束的实数变量。
输入为

`n = κ * 2^s * b^3`, `κ≥1`, `b≥1`, `a*b≤s≤A*b`。

源码推导

`(a*log 2)*b ≤ log n ≤ (log κ + A*log 2 + 3)*b`，

并推导

`c*(a*log 2)^2/(log n)^2 ≤ c/b^2`。

`size_ge_scale` 和 `sizes_unbounded` 处理数值长度序列的无界性。
它们不构造这些长度上的码，更不证明无限个长度上存在满足所需输入的码。

### tester 和局部性

`T4/Assembly.lean` 使用实际二元表示的两个全局 sector inequalities，
推导所有 Pauli 误差的 centralizer-metric tester 不等式。
测试次数分母使用实际列出的全部校验数，冗余行保留。

二元边界的行/列重量输入为 `3L,4L,2L,6L`，由此推导两个校验扇区的
最大校验重量及总参与度均不超过 `6L`。在原稿中 `L=ell*D`。
这些边界稀疏性输入尚未从具体立方 incidence 形式化推导。

## 新的主要条件定理到底断言什么

定理名：

`SemidirectQLTC.T4.t4_parameters_from_certificates`

它接受实际二元链、实际 shifted 链、同调等价 `e`、准确维数公式、
原稿全局扩张/距离不等式和边界稀疏性证明。由这些前提推导显式常数

`R    = ell * degree^4 * rateBracket / κ`

`d0   = d * (a*log 2)^2`

`rho0 = (min aX aZ / (λ/κ)) * (a*log 2)^2`

为正，并得到

`R*n ≤ k ≤ n`, `m=(λ/κ)*n`,

`d_X,d_Z ≥ d0*n/(log n)^2`,

`rho ≥ rho0/(log n)^2`, `w,Δ≤6L`。

这里 `d_X,d_Z` 的下界以“每个非零逻辑类代表的重量至少为相应阈值”表达；
没有为不存在的逻辑类随意定义最小值。

**这不是完整存在性定理。** 其输入不是已经核验的事实，也没有在 Lean 中证明
存在一族同时满足它们的实际半直积构造。把 `hX`、`hZ`、`hd` 等前提包装成
一个 structure 并不消除这项缺口。

## 完整结果仍欠缺的证明

详见同目录 `obligations.json`。主要缺口包括：

- 经典族、半直积谱估计和 literal-generator lift；
- 固定局部矩阵的两向鲁棒性；
- 实际立方复形、复合为零、二元展开、维数及稀疏性；
- DLV 在 `t=4,j=2` 的全局距离与两个全局扩张定理；
- DLV shifted 同调等价的实际构造；
- 所有局部数据和常数对整个无限族的一致选择。

此外，`expectation_of_global_testability` 只是给定 syndrome 分解后的有限非负加权和。
它没有构造稳定子投影算符，没有证明 Loewner-order 算子不等式，不能单独充当
“任意量子态”部分的形式化验证。

## 为什么编译和公理审计也不足以声称整个结果通过

`#print axioms` 可以检查证明依赖是否含 `sorryAx` 或额外公理，
但不能自动认定定理的显式前提已经成立。

本包因此分开记录：源码词法检查、模块构建、传递公理依赖、完整定理覆盖。
默认验收不会把带前提的模块编译成功当成完整 qLTC 存在性证明。
