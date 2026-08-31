# 将零点区域接口压缩为经典形式的重构计划

## 1. 背景与目标

当前 `formal/ChenTheorem/Lemma6/ZeroFreeRegion.lean` 中的
`PrimitiveZeroFreeRegion` 声称：存在固定正常数，使所有本原 Dirichlet
特征的 `L` 函数在

\[
\operatorname{Re}s \ge 1-cq^{-1/300}
\]

内对任意虚部高度一致非零。这个固定宽度、无限高度的区域明显强于经典
零点区域。经典区域的宽度会随虚部高度缩小，而且还需要处理可能的
Siegel 实零点。

本重构的目标是：

- 把唯一未解决的零点区域输入改写成经典强度；
- 不显式携带 exceptional character，而用高度区域与固定
  `ε = 1/300` 的 Siegel 下界组成混合区域；
- 在半宽度区域内提供足够宽松但可供方程 (21) 使用的 `L'/L` 界；
- 将 `Equation21.lean` 的无限高度轮廓极限改成有限高度矩形加原线尾部；
- 保持 `eq21_characterIntegral_bound`、Lemma 6 及其下游最终 statement 不变；
- 不增加新的 `sorry`。

## 2. 经典混合零点区域

### 2.1 宽度定义

定义

\[
\Delta(q,t)=\min\left(
  \frac{c_0}{\log(q(|t|+2))},
  c_1q^{-1/300}
\right).
\]

其中：

- 第一项是 de la Vallée-Poussin 型的高度相关区域；
- 第二项来自固定取 `ε = 1/300` 后的 Siegel 型下界；
- `c₁` 一般是不可有效计算的常数；
- `min` 给出对非例外零点和可能的 Siegel 零点都统一有效的距离。

Lean 中先加入辅助定义：

```lean
noncomputable def primitiveZeroFreeWidth
    (c₀ c₁ : ℝ) (q : ℕ) (t : ℝ) : ℝ :=
  min
    (c₀ / Real.log ((q : ℝ) * (|t| + 2)))
    (c₁ * (q : ℝ) ^ ((-1 : ℝ) / 300))
```

所有实际使用点都有 `2 ≤ q`，所以对数的参数大于 `1`，宽度的正性可以
统一证明。

### 2.2 非消失与对数导数界

非消失部分采用严格不等号：

\[
1-\Delta(q,\operatorname{Im}s)<\operatorname{Re}s
\quad\Longrightarrow\quad
L(s,\chi)\ne0.
\]

使用严格不等号可以避免额外承诺边界上无零点。后续证明会把轮廓放进
半宽度区域，因此自动获得严格余量。

`L'/L` 不再沿用当前过弱的高度增长界，而在缩小一半的区域中陈述：

\[
\operatorname{Re}s\ge 1-\frac{1}{2}\Delta(q,\operatorname{Im}s)
\]

时

\[
\left|\frac{L'}{L}(s,\chi)\right|
\le C\left(
  q^{1/300}+\log(q(|\operatorname{Im}s|+2))+1
\right)^2.
\]

这一界允许靠近可能的 Siegel 零点时出现 `q^(1/300)` 损失。对本项目的
`q ≤ (log x)^100`，该损失平方后至多为 `(log x)^(2/3)`，远小于方程
(21) 已预留的 `(log x)^90`。

建议用结构体打包数据，避免在 `Equation21.lean` 中反复解构长合取。例如：

```lean
structure PrimitiveZeroFreeRegionData where
  cHeight : ℝ
  cSiegel : ℝ
  cLogDeriv : ℝ
  cHeight_pos : 0 < cHeight
  cSiegel_pos : 0 < cSiegel
  cLogDeriv_pos : 0 < cLogDeriv
  nonvanishing :
    ∀ (q : ℕ) (_ : NeZero q) (χ : DirichletCharacter ℂ q),
      2 ≤ q → χ.IsPrimitive → ∀ s : ℂ,
        1 - primitiveZeroFreeWidth cHeight cSiegel q s.im < s.re →
          DirichletCharacter.LFunction χ s ≠ 0
  logDeriv_bound :
    ∀ (q : ℕ) (_ : NeZero q) (χ : DirichletCharacter ℂ q),
      2 ≤ q → χ.IsPrimitive → ∀ s : ℂ,
        1 - primitiveZeroFreeWidth cHeight cSiegel q s.im / 2 ≤ s.re →
          ‖deriv (DirichletCharacter.LFunction χ) s /
              DirichletCharacter.LFunction χ s‖ ≤
            cLogDeriv *
              ((q : ℝ) ^ ((1 : ℝ) / 300) +
                Real.log ((q : ℝ) * (|s.im| + 2)) + 1) ^ 2

def PrimitiveZeroFreeRegion : Prop :=
  Nonempty PrimitiveZeroFreeRegionData
```

保留唯一未解决的解析输入：

```lean
theorem primitive_zero_free_region : PrimitiveZeroFreeRegion := by
  sorry
```

此处的 `sorry` 仍代表一个很深的经典解析数论结果，但其 statement 不再
超出经典强度。

## 3. 方程 (21) 的有限高度

### 3.1 固定多对数高度

新增一个使用自然数幂的高度：

```lean
noncomputable def lemma6Equation21Height (x : ℕ) : ℝ :=
  Real.log (x : ℝ) ^ 10
```

指数 `10` 有以下优点：

- 明显大于平滑尺度指数 `1.1`；
- 使用自然数幂，Lean 中的正性和幂运算整理更简单；
- 对经典区域而言仍只有 `O(log log x)` 的高度成本；
- 配合完整阶平滑核时，尾部衰减远强于最终需要的指数节省。

### 3.2 统一进入半宽度区域

证明最终一致的区域包含关系：对充分大的 `x`，若

```text
2 ≤ q,
(q : ℝ) ≤ (Real.log x)^100,
|t| ≤ lemma6Equation21Height x,
```

则

\[
\frac{2}{\sqrt{\log x}}<\Delta(q,t).
\]

应将此结论拆成两个分量证明。

高度分量满足

\[
\log(q(|t|+2))
\le O(\log\log x)
\ll\sqrt{\log x},
\]

所以最终

\[
\frac{2}{\sqrt{\log x}}
<\frac{c_0}{\log(q(|t|+2))}.
\]

Siegel 分量满足

\[
q^{-1/300}\ge(\log x)^{-1/3},
\]

而

\[
(\log x)^{-1/2}=o((\log x)^{-1/3}),
\]

所以最终

\[
\frac{2}{\sqrt{\log x}}<c_1q^{-1/300}.
\]

由 `lt_min` 合并即可得到统一结论。因此

\[
\gamma_x=1-\frac{1}{\sqrt{\log x}}
\]

严格位于半宽度区域内。在有限矩形中所有点的实部都不小于 `γₓ`，虚部
绝对值都不超过 `T(x)`，故整个矩形同时满足非消失和 `L'/L` 界。

## 4. 重构 `Equation21.lean`

### 4.1 替换固定宽度接口

当前 `Eq21ZeroFreeBound` 重复编码了固定宽度区域。应删除它，或将它改为
对 `PrimitiveZeroFreeRegionData` 的轻量别名。以下定理需要改为直接接收
经典区域数据：

- `differentiableOn_eq21LogDerivIntegrand`；
- `eq21LogDeriv_finite_rectangle`；
- 移位线上的点态 `L'/L` 估计；
- 移位线截断积分的估计；
- 最终的 `eq21_characterIntegral_bound`。

`differentiableOn_eq21LogDerivIntegrand` 不应再使用仅依赖实部的固定半平面
作为区域。对有限矩形中的每个点，应先由 `|s.im| ≤ T(x)` 和
`γₓ ≤ s.re` 得到动态非消失，再应用商的可微性。

### 4.2 保留有限矩形恒等式

现有有限矩形 Cauchy-Goursat 证明可以继续复用，但只在

```lean
T := lemma6Equation21Height x
```

处实例化。轮廓为

\[
1-\frac1{\sqrt{\log x}}
\le\operatorname{Re}s
\le1+\frac1{\log x},
\qquad
|\operatorname{Im}s|\le T(x).
\]

### 4.3 删除无限高度机制

以下机制依赖固定左竖线在所有高度都处于零点区域，应删除或替换：

- `Eq21LogDerivHorizontalEdgesVanish`；
- `eq21LogDerivHorizontalEdgesVanish_of_pointwiseDecay`；
- `eq21LogDeriv_horizontalEdgesVanish`；
- 通过 `T → ∞` 得到完整竖线积分相等的
  `eq21LogDeriv_verticalIntegral_eq`；
- 对整条 `γ` 线的全实轴可积性要求。

不要尝试定义或估计 `|t| > T(x)` 的 `γ` 线积分，因为那里已经超出所用
经典零点区域，`L'/L` 可能遇到零点。

### 4.4 新的轮廓组装不等式

将原 `α` 线全积分拆成截断部分和两条尾部。有限矩形给出截断竖线之间
的精确关系；取范数后得到

\[
\|I_\alpha\|
\le
\|I_{\gamma,[-T,T]}\|
+\|H_+\|+\|H_-\|
+\|I_{\alpha,|t|>T}\|.
\]

四项分别处理：

1. `γ` 线截断积分：使用半宽度区域中的新 `L'/L` 界；
2. 上水平边：使用有限矩形中的动态零点区域和完整阶核衰减；
3. 下水平边：同上；
4. `α` 线尾部：因 `α > 1`，直接使用绝对收敛半平面内已经证明的
   Dirichlet 级数或对数导数界，不依赖零点区域。

Mathlib 层面可以选择：

- 用 `Set.Icc (-T) T` 的集合积分分解全实轴积分；或
- 继续使用 `intervalIntegral` 表示截断部分，并证明它与相应集合积分一致。

应优先选择能最少改动现有有限矩形定理的表示。

## 5. 补强完整阶平滑核估计

现有代码为了证明可积性和主区间估计，常把精确核降成四次尾界或
`(1+t^2)⁻¹`。这些粗界不能单独支持多对数高度下方程 (21) 所需的
指数节省。

必须保留核的完整阶数，证明类似

\[
|K_x(\sigma+it)|
\le
\sigma^{-1}
\left(
  1+\left(\frac{t}{(\log x)^{1.1}}\right)^2
\right)^{-(\lfloor\log x\rfloor+1)/2}.
\]

当

\[
T(x)=(\log x)^{10}
\]

时，

\[
\frac{T(x)}{(\log x)^{1.1}}=(\log x)^{8.9}.
\]

再提升到约 `log x` 阶后，所得衰减远强于任意固定对数幂，也远强于
最终需要吸收的

\[
\exp(-c\sqrt{\log x}).
\]

应新增以下类型的辅助结论：

- `α` 线上 `|t| ≥ T(x)` 的完整阶核界；
- 水平边上对 `γₓ ≤ σ ≤ αₓ` 一致的完整阶核界；
- 核衰减吸收 `x^α`、pair polynomial、`L'/L` 和固定对数幂的最终渐近
  不等式；
- `α` 线两条尾部的积分范数界；
- 两条水平边积分范数界。

已有的四次尾界仍可保留，用于普通可积性和主区间积分；只有新出现的
有限高度误差项必须使用完整阶界。

## 6. 对最终对数预算的影响

在

\[
q\le(\log x)^{100}
\]

下，

\[
q^{1/300}\le(\log x)^{1/3},
\qquad
q^{1/150}\le(\log x)^{2/3}.
\]

因此新的 `L'/L` 界只增加不到一个完整 `log x` 次幂的主要损失；高度
对数在 `|t| ≤ (log x)^10` 内只是 `O(log log x)`。当前
`eq21_characterIntegral_bound` 的 `(log x)^90` 有足够余量，最终 statement
无需改变。

实现时仍应明确记录每个新损失，并证明它们统一被 `(log x)^90` 吸收，
避免只依赖非形式化的“大量余量”说明。

## 7. 建议实施顺序

为保持每个阶段可编译，按以下顺序进行。

1. 在 `ZeroFreeRegion.lean` 中加入 `primitiveZeroFreeWidth` 和新的数据结构，
   更新唯一 `sorry` 的 statement 及文件注释。
2. 在 `Equation21.lean` 中加入 `lemma6Equation21Height`，证明宽度正性、
   高度对数上界、Siegel 分量下界，以及有限矩形最终位于半宽度区域。
3. 将 `Eq21ZeroFreeBound` 的消费者迁移到新数据结构，但暂时保留有限矩形
   定理的整体形状。
4. 建立完整阶核在 `α` 线尾部和水平边上的统一估计。
5. 证明 `α` 线尾部和两条水平边的显式误差界。
6. 将移位线的全实轴积分定理改为 `[-T(x),T(x)]` 上的截断积分定理。
7. 用有限矩形恒等式、截断 `γ` 线、水平边和 `α` 线尾部重新证明
   `eq21_characterIntegral_bound`。
8. 删除不再使用的无限高度 Prop、极限定理和误导性注释。
9. 全量构建并审计 `sorry`、警告和公理依赖。

## 8. 验收标准

重构完成后应满足：

- 项目内仍然只有 `primitive_zero_free_region` 这一处解析数论 `sorry`；
- 该 `sorry` 的 statement 使用高度相关的经典混合区域；
- 非消失使用严格区域，`L'/L` 使用半宽度区域；
- 文件中不再声称固定宽度零点区域对虚部高度一致；
- `Equation21.lean` 不再通过 `T → ∞` 移动固定左竖线；
- 只在 `|t| ≤ (log x)^10` 的有限矩形内使用零点区域；
- `γ` 线只出现截断积分，不要求全实轴上的非消失或可积性；
- `α` 线尾部和两条水平边由完整阶平滑核显式控制；
- `eq21_characterIntegral_bound`、Lemma 6 以及主定理的公开 statement 不变；
- 不引入新的 `sorry`、非标准公理或非 `sorry` 警告；
- `lake build` 全量通过。

## 9. 风险与注意事项

- 最大的形式化工作量不在新零点区域定义，而在全实轴积分向有限截断积分
  的重构和尾部积分分解。
- 不能仅将现有区域公式替换成 `log(q(|t|+2))`；否则无限高度轮廓证明会
  立即失效。
- 不能只使用现有四次尾界；多对数截断方案依赖平滑核完整的
  `⌊log x⌋+1` 阶衰减。
- 如果未来要求所有常数有效或需要显式数值版本，就不能再用压缩后的
  Siegel 项隐藏 exceptional character，而应改用显式 exceptional-character
  接口并追踪可能的留数。当前 Lemma 6 的定性渐近目标不要求这一步。
