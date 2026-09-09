# 四维半直积 qLTC 的证明稿

[主定理与定义](THEOREM.zh-CN.md) · [命题依赖](DEPENDENCIES.zh-CN.md) · [文献与固定版本](../REFERENCES.md)

**文档性质：依赖已列外部定理的数学研究稿，非 Lean 验证证书。** 本文整理已有手工核验论证，并将系数复形的实际 incidence 写出。外部定理仍作为数学输入，没有在本仓库中重新形式化证明。本次发布整理不构成独立同行评审或新颖性审查。

定理范围是 $t=4,j=2$、允许固定辅助群 $K$、固定域和固定局部矩阵，以及指定无限长度序列。全文隐含常数与族参数 $B$ 无关。准确量词、centralizer 距离及量子态 distance observable 以 [THEOREM](THEOREM.zh-CN.md) 为准。

证明路线为：经典输入与半直积扩张 → 固定标签群 → 左陪集与方向分量 → 固定鲁棒局部码 → DLV 双扇区扩张 → shifting 正率 → 二元 CSS 与全局 tester → 对数平方换算。几何论证本身不依赖扩张，故先行给出。

<a id="inputs"></a>

## 1. 使用的外部输入

[R1] Tali Kaufman and Alexander Lubotzky, *Edge Transitive Ramanujan Graphs and Highly Symmetric LDPC Good Codes*, arXiv:1108.2960v1。使用 Theorems 3、4、6、11。提供固定 4093 的群/经典码族、坐标传递对称、正率与正相对距离。

[R2] Gleb Kalachev and Pavel Panteleev, *Maximally Extendable Product Codes are Good Coboundary Expanders*, arXiv:2501.01411v2。使用 Corollary 3 和 Lemma E2：固定率区间中存在同时 product expanding 的元组及其全对偶元组；性质传给子元组；常数不随局部长度增长。

[R3] Irit Dinur, Ting-Chun Lin and Thomas Vidick, *Expansion of higher-dimensional cubical complexes with application to quantum locally testable codes*, arXiv:2402.07476v3，2025-09-04 修订。使用 Definition 6.4、Theorem 3.6 及式 (14)(15)、Theorem 4.1、Lemma 4.2、Definition 5.9、Theorem 5.10 和 Lemma 5.13。使用的是包含 shifting 码率修正的 v3，不是修正前的计数论证。

[R4] Noga Alon, Alexander Lubotzky and Avi Wigderson, *Semi-direct product in groups and zig-zag product in graphs: connections and applications*，作者公开的 `alwproc1.pdf`。半直积扩张的背景来源。本文直接给出需要的算子估计，不以“zigzag”名称代替证明。

关于来源中个别表述：不直接照抄 [R3] Corollary 3.7 的局部行数次序或二元维数写法，而是使用其 Theorem 4.1 和 §4.1 的实际计算，独立得到本文的行数配置与二元维数。局部存在性仅需“所有充分大的局部长度”，不需要“所有正整数长度”这一更强表述。

<a id="geometry"></a>

## 2. 半直积陪集与方向分量

设经典码为 $C_B$，坐标数 $L_B$，$Q_B$ 是坐标传递的对称群，$|Q_B|=B$。令

$$
A_B=C_B^*,\quad s_B=\dim_{\mathbb F_2}C_B,\quad M=2^{s_B},
\quad Q'_B=Q_B\times K,\quad b=|Q'_B|,
\quad P'_B=A_B\rtimes Q'_B.
$$

$K$ 对 $A_B$ 的作用为平凡作用。群律为 $(a,g)(a',g')=(a+g a',gg')$。$C_B^*$ 是代数对偶，而不是正交码。

在 $\Gamma=(P'_B)^4$ 中取

$$
\Lambda=\{((a_1,g),\ldots,(a_4,g)):a_1+a_2+a_3+a_4=0\}.
$$

乘积的 $A$ 坐标和等于 $\sum_i a_i+g\sum_i a'_i=0$，逆元也满足同一条件，故 $\Lambda$ 是子群。
最后一个 $a_i$ 由前三个确定，因而

$$
|\Lambda|=M^3b,\qquad |\Gamma/\Lambda|=Mb^3=:N.
$$

这里 $\Gamma/\Lambda$ 是左陪集集，使用左乘作用，完全不需要 $\Lambda$ 正规。

令 $\Gamma_i$ 为第 $i$ 个坐标子群。$\Gamma_i$ 在 $\Gamma$ 中正规，并且 $\Gamma_i\cap\Lambda=\{1\}$：另三个坐标为单位元迫使公共 $g=1$，零和条件再迫使 $a_i=0$。因此在任意陪集 $h\Lambda$ 上

$$
\operatorname{Stab}_{\Gamma_i}(h\Lambda)
=\Gamma_i\cap h\Lambda h^{-1}
=h(\Gamma_i\cap\Lambda)h^{-1}=\{1\}.
$$

每个方向轨道都正则，大小 $|P'_B|=Mb$；轨道数是 $b^2$，方向分量比例为

$$
\eta=\frac{Mb}{Mb^3}=b^{-2}.
$$

不同坐标子群的作用交换。只要 $S'_B$ 是 $P'_B$ 的对称生成元集合，相应方向图就是 $b^2$ 个同构 Cayley 扩张分量的并。这满足 [R3] Definition 6.4。不能把这些方向图误写成整个 $X_B$ 上的连通扩张图。

<a id="spectral"></a>

## 3. 经典输入与半直积谱估计

[R1] 的固定经典族可以取 $G_e=\operatorname{PSL}_2(4093^e)$，$Q_B=G_e\rtimes T$，$|T|=4094$。经典码的坐标为无向边，因而

$$
L_B=4094|G_e|/2=B/2,\qquad s_B=\Theta(B),
$$

并存在不依赖 $B$ 的相对距离下界 $\delta_0>0$。只需固定一个满足正距离要求的局部循环码，不需要逐 $B$ 重新选择局部码。

$Q_B$ 的扩张不是从“对称”推出的。由于 $S_0\subset G_e$ 对 $T$ 不变，在 $G_e\times T$ 坐标下，将均匀 $S_0$ 右步与均匀 $T$ 右步各取一半，得到

$$
M_Q=\tfrac12(M_{G_e}\otimes I+I\otimes J_T).
$$

若 $M_G$ 的第二代数特征值 $\le\lambda_0<1$，则总均值零子空间上的绝对谱界为

$$
\max\{(1+\lambda_0)/2,1/2\}<1.
$$

这一估计也容许 $M_G$ 有特征值 $-1$。固定次幂可将 $Q$ 步的非平凡范数压到任意预定 $\mu>0$。

$A_B$ 上的特征标由 $c\in C_B$ 编号：$\chi_c(a)=(-1)^{a(c)}$。坐标求值泛函是一个 $Q_B$ 轨道，均匀 $Q_B$ 抽样与均匀经典坐标抽样一致，包括求值泛函有重复的情况。

必须使用 lazy 求值步，其非平凡特征值为

$$
1-\operatorname{wt}(c)/L_B\in[0,1-\delta_0].
$$

不加 lazy 时可能出现 −1，不能只凭经典码距离宣称绝对谱隙。

在 $P_B=A_B\rtimes Q_B$ 上，令 $U$ 对每个纤维 $\{a\}\times Q_B$ 平均，$T$ 为纤维内 $Q$ 步，$W=(I+R_{(e_0,1)})/2$。对 $T=U+E$ 有 $\|E\|\le\mu$，$\|W\|\le1$；$UWU$ 在均值零子空间上的范数 $\le1-\delta_0$。因此

$$
\|TWT\|_{1^\perp}
\le1-\delta_0+2\mu+\mu^2.
$$

例如 $\mu\le\delta_0/8$ 足以使右侧 $\le1-\delta_0/2$。再取固定次幂，得到非平凡范数至多任意给定 $\varepsilon>0$ 的有界度对称 multiset。其度数可先通过补单位步安排为二的幂，再取幂；这个操作不会把谱隙变为零。

<a id="labels"></a>

## 4. 补全固定标签群引理：不是直接删重

需要将对称 multiset 变成真正的生成元集合，且不能令开销随 B 增长。

设 multiset 度数 $d_0$ 为二的幂，群元素 $p$ 的重数为 $m_p$，故 $\sum_p m_p=d_0$ 且 $m_p=m_{p^{-1}}$。假定其非平凡谱范数 $\le\varepsilon<1$。给定 $\zeta>0$，可先不失一般性取 $\zeta<1$。

取 $K=\mathbb F_2^h$，$L=|K|$ 足够大，$d_0\mid L$。对每个整数 $1\le m\le d_0-1$，构造

$$
T_m\subset K\setminus\{0\},\qquad
|T_m|=mL/d_0,
\qquad
\left|\sum_{z\in T_m}\chi(z)\right|\le\zeta L/d_0
$$

对每个非平凡特征标 $\chi$ 都成立。$T_m$ 只依赖 $m,d_0,\zeta$，不依赖 $B$，也不依赖具体群元素。

下面给出自足的存在性论证。记 $k=mL/d_0$，在 $K\setminus\{0\}$ 上独立以概率 $p=k/(L-1)$ 选择元素。对包括平凡特征标在内的每个 $\chi$，定义

$$
Y_\chi=\sum_{z\ne0}\chi(z)(I_z-p).
$$

求和项独立、均值为零、绝对值≤1，展开四次方即得

$$
\mathbb E Y_\chi^4\le3L^2.
$$

令 $u=\zeta L/(4d_0)$。Markov 不等式及联合界表明，对所有 $m$ 和 $\chi$，同时有 $|Y_\chi|<u$ 的失败概率至多

$$
\frac{768d_0^5}{\zeta^4L}.
$$

取 $L$ 使之 $<1$，且 $u\ge1$。平凡特征标控制实际集合大小与 $k$ 的差；添加或删除少于 $u$ 个非零元素可使大小准确为 $k$。对非平凡 $\chi$，原均值为 $-p$，绝对值 $\le1$，修正后的 Fourier 和绝对值小于 $2u+1\le4u=\zeta L/d_0$。由此得到全部 $T_m$。

若 $m=d_0$，令 $T_{d_0}=K$。$m_1=d_0$ 会使原 walk 为恒等算子，与非平凡谱范数 $<1$ 矛盾，故单位元不需要这种情形。

现在对每个 $p$ 取 $T_p=T_{m_p}$，定义

$$
S'=\{(p,z):z\in T_p\}\subset P\times K.
$$

有 $|S'|=L$。不同二元组确实不同；$m_p=m_{p^{-1}}$ 及 $K$ 中 $z=-z$ 保证 $S'$ 对逆封闭；群单位元 $p=1$ 所对应的 $T_p$ 排除 $0$，故群单位元不在 $S'$ 中。

按 $K$ 的特征标分解正则表示。在平凡特征标上，归一化邻接算子为

$$
L^{-1}\sum_p|T_p|R_p=\sum_p(m_p/d_0)R_p,
$$

即原 multiset walk。在非平凡 $\chi$ 上，利用支撑数 $\le d_0$，算子范数 $\le$

$$
L^{-1}\sum_p\left|\sum_{z\in T_p}\chi(z)\right|\le\zeta.
$$

所以 $S'$ 的非平凡谱范数 $\le\max\{\varepsilon,\zeta\}<1$，特别是它生成 $P\times K$。整个标签库可以事先固定；$L,K$、最终方向度数 $D=L$ 均与 $B$ 无关。该论证保证标签库的统一性与精确基数。

<a id="local-codes"></a>

## 5. 固定局部矩阵与选择次序

固定

$$
0<\nu<(2^{1/4}-1)/2.
$$

例如 ν=1/32。取四个满行秩矩阵 h_i:F_q^D→F_q^{r_i}，要求

$$
r_1/D,r_2/D\in[\nu/2,\nu],\qquad
r_3/D,r_4/D\in[1-\nu,1-\nu/2].
$$

[R2] Corollary 3 与子元组继承性，加上 [R3] 的 product-expansion-to-robustness，给出两向 κ-robustness；κ>0 仅依赖固定区间与 t，不依赖 D、B。这里需要元组与全对偶元组，不需要把所有 mixed tuples 再假定为 robust。

因此无循环选择：先固定 ν 和率区间并取得 κ；再将谱范数 λ 压至足够小；再选固定标签库和足够大的 D；最后用局部存在性选择 q=2^ℓ 与 h₁,…,h₄。之后只让 B 增长。q 即使很大，也不是 B 的函数。

令

$$
\gamma=\kappa^4 2^{-64}-\lambda>0.
$$

[R3] Theorem 3.6 的证明给出了这个可用的显式正余量。因为谱界可以任意小，选取 λ 以使 γ>0 不增加任何随 B 增长的参数。


<a id="cubical-complex"></a>

### 5.1 具体 flagged 立方复形与系数微分

以下约定固定复形的实际 incidence，而不是只列出维数。令四个方向的置换为 $a_i:X_B\to X_B$，$a\in S'_B$；不同方向的置换两两交换。类型 $I\subseteq\{1,2,3,4\}$ 的面写成

$$
f=(x,(a_i)_{i\in I},(b_i)_{i\notin I}),\qquad
x\in X_B,\quad a_i\in S'_B,\quad b_i\in\{0,1\}.
$$

因此 $|\mathcal X(I)|=ND^{|I|}2^{4-|I|}$。二进制 flag 属于面数据；即使若干方向乘积在 $X_B$ 上重合，也不合并这些带 flag 的面。

面 $f$ 携带系数空间 $V_I=\bigotimes_{i\notin I}\mathbb F_q^{r_i}$。令 $C^j=\bigoplus_{|I|=j}\bigoplus_{f\in\mathcal X(I)}V_I$。给定 $i\notin I$ 和生成元标签 $a$，从该面向类型 $I\cup\{i\}$ 的贡献，把基点变为 $x$（$b_i=0$）或 $a_i^{-1}x$（$b_i=1$），删去 flag $b_i$ 并加入标签 $a$。同时在第 $i$ 个系数因子上应用线性泛函

$$
(v_1,\ldots,v_{r_i})\longmapsto\sum_{c=1}^{r_i}h_i[c,a]v_c.
$$

对所有 $i,a$ 求和即定义 $\delta_j:C^j\to C^{j+1}$。不同方向的基点变换交换，不同张量因子的收缩也交换；每个连续加入两个不同方向的项出现两次。在特征二中两次相加为零，故 $\delta_{j+1}\delta_j=0$。在固定标准系数基下取转置，得到 $\partial_j=\delta_{j-1}^T$ 及 $\partial_j\partial_{j+1}=0$。

直接数面与系数因子可得

$$
c_j=ND^j2^{4-j}\sum_{|I|=j}\prod_{a\notin I}r_a.
$$

原复形的链同调与对应余链同调在各次数具有相同维数，因为二者的微分互为转置；使用同调维数不等式时不混淆逻辑代表的实际重量。有限实现与该 incidence 约定对应，见 [check_t4_chains.py](../experiments/check_t4_chains.py)。

<a id="global-transfer"></a>

## 6. DLV 全局转移：恰好只损失一个 η

对固定 D，t=4 的面数为

$$
|\mathcal X(k)|=N\binom4k D^k2^{4-k}.
$$

[R3] Theorem 3.6 在次数 2 同时给出 cosystolic、systolic 距离与 cocycle、cycle 全局扩张。其 cycle 扩张是两个量的最小值，而非乘积：

$$
\varepsilon_{\rm cyc}(2)\ge
\min\left\{
\frac{\varepsilon_{\rm cocyc}(2)}{2(4096D^5)^4},\quad
\frac{\mu_{\rm cosyst}(3)}{(8D)^4|\mathcal X(2)|}
\right\}.
$$

直接代入 |X(2)|=24ND²、|X(3)|=8ND³ 和式 (14)，得到可用的保守界

$$
\mu_{\rm cosyst}(2)\ge\frac{3\gamma}{32D^2}\eta N,
\qquad
\mu_{\rm syst}(2)\ge\frac{3\gamma}{2^{17}D^6}\eta N,
$$

$$
\varepsilon_{\rm cocyc}(2)\ge\frac{\gamma}{(8D)^9}\eta,
\qquad
\varepsilon_{\rm cyc}(2)\ge\frac{\gamma}{2^{76}D^{29}}\eta.
$$

最后一式中第二个候选项是 γη/(3·2²⁰D⁷)，不小于展示的保守界。所有 D 的幂都是固定常数。因此两扇区 soundness 都为 Ω(η)，不是 Ω(η²)。

这里用的是到 ker 的全局距离，不是仅限小误差的 coboundary 估计。

<a id="rate"></a>

## 7. 正码率：只使用修正版 shifting 的维数恒等式

原复形的链维数为

$$
c_j=ND^j2^{4-j}\sum_{|I|=j}\prod_{a\notin I}r_a.
$$

朴素 c₂−c₁−c₃ 计数不能证明正率，不能将其替换为 shifting。

取 T={3,4}，将 h₃、h₄ 换成对偶校验矩阵，并使用 shifted grading |I△T|。于是全部 r'_i≤νD。[R3] Theorem 4.1 保证

$$
\dim H^2(C)=\dim H^2(C').
$$

全方向面 I={1,2,3,4} 在 shifted 次数 2，故 c'₂≥ND⁴；Lemma 4.2 给出

$$
\sum_jc'_j=N\prod_i(D+2r'_i)\le ND^4(1+2\nu)^4.
$$

因此，令 β=2−(1+2ν)⁴>0，便有

$$
\dim H^2(C)=\dim H^2(C')
\ge c'_2-c'_1-c'_3
\ge2c'_2-\sum_jc'_j
\ge\beta ND^4.
$$

这一论证只转移同调维数。距离与 soundness 仍在原复形上用 §6 证明，不需要假设 shifting 保重量。

<a id="binary-css"></a>

## 8. 二元 CSS、局部性及两个逻辑扇区

对 ∂₂ 和 ∂₃ 分别在一致的二元基下展开为 B₂ 和 B₃，取

$$
H_X=B_2,\qquad H_Z=B_3^T.
$$

于是 H_XH_Z^T=B₂B₃=0。不能先独立展开场转置并默认得到二元转置。

相同二元基的迹配对 Gram 矩阵是可逆的，且逐标量/逐面分块。若 A 是场矩阵，则

$$
\operatorname{bin}(A)^T
=G_{\rm domain}\operatorname{bin}(A^T)G_{\rm codomain}^{-1}.
$$

因此 cochain 一侧与真正 H_Z 所定义的一侧通过面内可逆变换对应。这保持面块是否为零，故保留面块逻辑距离与全局扩张，只在转成二元重量时损失固定因子。

准确长度、列出的校验数与逻辑比特数为

$$
n=\ell c_2,\quad m=\ell(c_1+c_3),\quad
k=\ell(c_2-\operatorname{rank}_{\mathbb F_q}\partial_2-
\operatorname{rank}_{\mathbb F_q}\partial_3)
=\ell\dim H_2(C).
$$

只有一个 ℓ 因子。c₂≤24ND⁴，结合 §7 可取 k/n≥β/24>0。

由高行数两个因子还可得

$$
4(1-\nu)^2\ell ND^4\le n\le24\ell ND^4,
\qquad
\frac{1-\nu}{6}\le\frac mn\le\frac{10}{(1-\nu)^2}.
$$

字段 ∂₂ 的行、列重量分别≤3D、4D，∂₃ 的行、列重量分别≤2D、6D。二元展开后

$$
w_{\max}\le6\ell D,\qquad \Delta_{\max}\le6\ell D.
$$

这些都是实际列出的校验，保留冗余；不能改为任意独立稳定子基。

每个次数 2 的面块含至多 ℓD² 个二元坐标。若 α=γ/(2⁷⁶D²⁹)，则两个二元校验矩阵都满足

$$
|Hu|\ge\frac{\alpha}{\ell D^2}\eta\,
\operatorname{dist}_{\rm bin}(u,\ker H)
$$

对所有 u 成立。由于二元重量≥面块重量，由 §6 还可取

$$
d_X,d_Z\ge\frac{\gamma}{2^{20}\ell D^{10}}\eta n.
$$

这些明确但很小的常数只为核对量词和参数依赖，不主张优化。

<a id="quantum-tester"></a>

## 9. 全局 quantum tester 与任意量子态

设 E=X^xZ^z，d_x=dist(x,ker H_Z)、d_z=dist(z,ker H_X)。令

$$
\delta(E)=\min_{C\in\operatorname{Cent}(\mathcal S)}\operatorname{wt}(EC).
$$

因为 centralizer 要求两个分量分别进入相应的核，而 Pauli 重量是两个支撑的并集，

$$
\max(d_x,d_z)\le\delta(E)\le d_x+d_z.
$$

取 a=α/(ℓD²)>0，则违背的列出校验数满足

$$
v(E)=|H_Zx|+|H_Xz|\ge a\eta(d_x+d_z)\ge a\eta\delta(E).
$$

均匀随机抽测 m 个校验之一时

$$
\Pr[\mathrm{reject}\ E]\ge a\eta\frac nm\frac{\delta(E)}n.
$$

m/n 有常数上下界，所以 ρ=Ω(η)。没有误差重量或 syndrome 大小的限制。

为了核对任意量子态的解释：CSS 正号稳定子不含 −I；对每个实际可实现的 syndrome σ，任取具有该 syndrome 的 Pauli E_σ，则 E_σ 将码空间等距映到整个 syndrome 子空间。令其正交投影为 Π_σ，并令 δ_σ 是该 syndrome 的最小 Pauli 重量。由低重量算子的 Pauli 展开可知，重量≤a 的误差作用于码空间所得的线性张成，恰等于 ⊕_(δ_σ≤a) im Π_σ。于是

$$
\mathsf D=\sum_\sigma\delta_\sigma\Pi_\sigma
$$

是对应的距离 observable，而

$$
\mathsf H_{\rm test}=\frac1m\sum_j\frac{I-S_j}{2}
=\sum_\sigma\frac{|\sigma|}{m}\Pi_\sigma.
$$

逐 syndrome 不等式即给出 H_test ⪰ (ρ/n)D，对任意量子态取期望仍成立。逻辑 Pauli 的 centralizer 距离为零，所以没有要求局部测试器拒绝码空间中的逻辑变换。

<a id="asymptotics"></a>

## 10. 最终参数代换及无限族

有 b=|K|B=Θ(B)，s_B=Θ(B)，n=Θ(N)=Θ(2^{s_B}b³)。因此

$$
\log n=s_B\log2+3\log b+O(1)=\Theta(B)=\Theta(b).
$$

代入 η=b⁻²，即得到结论中的 d_X,d_Z=Ω(n/log²n) 与 ρ=Ω(1/log²n)。KL 的群阶沿 e→∞ 无界，所有已固定局部数据不变，从而获得无限族。

这不证明覆盖每个指定码长，不证明固定 K=1 的直接去重方案，不证明常数 soundness 或线性距离，也不证明对数平方指数最优。本文不作优先权/新颖性认定。



## 11. 证明与有限复算的关系

正文中的一般推导和文献输入承担渐近定理；Python 脚本只交叉检查有限结构和代数代换。运行方式、实际结果和 Lean 边界见 [REPRODUCIBILITY](REPRODUCIBILITY.zh-CN.md) 与 [VERIFICATION_STATUS](VERIFICATION_STATUS.zh-CN.md)。不要从两个小型样本推断局部鲁棒性、渐近 soundness 或所有族成员的存在性。
