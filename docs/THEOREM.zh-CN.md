# 主定理：$t=4,j=2$ 的半直积 qLTC

[仓库首页](../README.md) · [证明](PROOF.zh-CN.md) · [依赖清单](DEPENDENCIES.zh-CN.md)

## 1. 范围与量词

本研究稿证明以下结论，使用[外部输入 R1–R3](../REFERENCES.md)。它不是自含地重新证明这些文献的全部结果，也不是 Lean 验证报告。

存在固定有限群 $K$、固定整数 $D,\ell>0$、固定有限域 $\mathbb F_q$（$q=2^\ell$）、固定满行秩局部矩阵 $h_1,\dots,h_4$，以及一个无界参数序列 $B_e\to\infty$。对每个充分大的序列成员，以正文的半直积陪集和四维立方系数复形构造二元 CSS 码 $\mathcal Q_e$。所有局部数据都先于 $e$ 固定。

存在与 $e$ 无关的常数 $R,c_d,c_\rho,c_m,C_m,W,\Delta>0$，使码长 $n_e\to\infty$，且

$$
Rn_e\le k_e\le n_e,\qquad
c_mn_e\le m_e\le C_mn_e,
$$
$$
d_X(\mathcal Q_e),d_Z(\mathcal Q_e)
\ge c_d\frac{n_e}{(\log n_e)^2},
\qquad w_{\max,e}\le W,\quad\Delta_{\max,e}\le\Delta.
$$

均匀抽取所列 $m_e$ 个校验之一的 tester，对所有 Pauli 误差 $E$ 满足

$$
\Pr[\operatorname{reject}E]\ge
\frac{c_\rho}{(\log n_e)^2}\frac{\delta_e(E)}{n_e}.
$$

因此可取 $\rho_e\ge c_\rho/(\log n_e)^2$。对数取自然对数；更换固定底数仅调整常数。距离与 soundness 是下界，没有匹配上界或最优性声明。

## 2. 固定的数据

经典族为 $C_B\subseteq\mathbb F_2^{L_B}$，其坐标传递对称群为 $Q_B$，$|Q_B|=B$，$L_B=\Theta(B)$，且 $s_B=\dim C_B=\Theta(B)$。该族具有统一正相对距离，并有适当的 $Q_B$ Cayley 扩张；正文采用 R1 的固定参数实现。

设

$$
A_B=C_B^*,\quad M=2^{s_B},\quad Q'_B=Q_B\times K,\quad b=|Q'_B|,
\quad P'_B=A_B\rtimes Q'_B.
$$

$C_B^*$ 是代数对偶，不是正交码。$K$ 平凡作用于 $A_B$。取

$$
\Lambda_B=\{((a_1,g),\ldots,(a_4,g)):\textstyle\sum_i a_i=0\},
\quad X_B=(P'_B)^4/\Lambda_B.
$$

这是左陪集空间，使用左乘作用，不假设 $\Lambda_B$ 正规。固定标签群将对称 multiset walk 提升成真正、无单位元的对称生成元集合 $S'_B$，其大小 $D$ 与 $B$ 无关。局部矩阵列与生成元标签的对应属于构造数据；不得先独立任意排列后继续沿用同一系数复形。

取固定 $0<\nu<(2^{1/4}-1)/2$（例如 $\nu=1/32$），并按正文选取两向鲁棒局部矩阵，行数比例满足

$$
r_1/D,r_2/D\in[\nu/2,\nu],\qquad
r_3/D,r_4/D\in[1-\nu,1-\nu/2].
$$

“任意鲁棒局部码”不是本定理的量词；本定理要求同时满足给定率区间与两向鲁棒性的元组。

## 3. 实际二元 CSS 表示

令 $c_j=\dim_{\mathbb F_q} C_j$。在一致二元基下展开 $\partial_j$ 为 $B_j$，定义

$$
H_X=B_2,\qquad H_Z=B_3^T,\qquad H_XH_Z^T=0.
$$

准确数量是

$$
n=\ell c_2,\quad m=\ell(c_1+c_3),\quad
k=\ell\dim_{\mathbb F_q}H_2(C).
$$

$m$ 统计实际列出的全部二元校验，包括冗余。两个逻辑距离分别定义为

$$
d_Z=\min\{|z|:z\in\ker H_X\setminus\operatorname{im}H_Z^T\},
\quad
d_X=\min\{|x|:x\in\ker H_Z\setminus\operatorname{im}H_X^T\}.
$$

正码率保证非零逻辑类存在。最大校验重量统计每一列出的稳定子生成元的支撑，参与度统计同一个量子比特参与的所有列出校验数。

## 4. 全局 tester 的距离与量子态版本

对稳定子群 $\mathcal S$，

$$
\delta(E)=\min_{C\in\operatorname{Cent}(\mathcal S)}\operatorname{wt}(EC).
$$

Pauli 重量是 $X$、$Z$ 分量支撑的并集大小。逻辑 Pauli 属于 centralizer，距离为零；本定理不要求 tester 拒绝逻辑变换。所有误差和所有 admissible syndromes 都在量词范围内。

令 $\Pi_\sigma$ 为可实现 syndrome $\sigma$ 的投影，$\delta_\sigma$ 为产生该 syndrome 的最小 Pauli 重量。定义

$$
\mathsf D=\sum_\sigma\delta_\sigma\Pi_\sigma,\qquad
\mathsf H_{\mathrm{test}}=\frac1m\sum_j\frac{I-S_j}{2}.
$$

则

$$
\mathsf H_{\mathrm{test}}\succeq
\frac{c_\rho}{n(\log n)^2}\mathsf D.
$$

对任意密度算符取期望，得到任意量子态不等式。这里没有将 $\mathsf D$ 替换成未定义的“量子 Hamming 距离”。

## 5. 参数来源与限制

核心恒等式为 $N=|X_B|=Mb^3$ 和 $\eta=b^{-2}$。方向图允许多个扩张分量；每个方向恰有 $b^2$ 个大小为 $Mb$ 的分量。DLV 在次数二给出两个距离 $\Omega(\eta N)$ 和两个全局扩张 $\Omega(\eta)$。修正版 shifting 给出正码率；固定域二元化只改变常数。最后 $n=\Theta(2^{s_B}b^3)$ 和 $s_B=\Theta(B)$ 导出 $b=\Theta(\log n)$。

结论不覆盖每个指定整数码长，不声称 $K=1$ 的直接删重方案有效，不给出常数 soundness 或线性距离，不把有限样本当成渐近证明，也不宣称完整 Lean 形式化已经完成。
