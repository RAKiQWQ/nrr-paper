# 广义 Nandakumar–Ramana Rao 问题的 Lean 形式化

原稿的给定凸体、给定测度分类已在 Lean 中完成。最终声明位于
[PrimePowerTopologyConclusion.lean](NRR/PrimePowerTopologyConclusion.lean)：

```lean
NRR.prescribedCounterexamples : NRR.PrescribedCounterexamples
NRR.primePowerExistence : NRR.PrimePowerExistence
NRR.fullClassification : NRR.FullClassification
```

对每个 `d ≥ 3`、`n ≥ 2`，先给定满维紧凸体 `K` 及关于 Lebesgue 测度
绝对连续、在 `K` 上总质量为一的概率测度 `μ`。任意 `d−1` 个连续单块
泛函都有等质量、等泛函值的凸 `n` 分割，当且仅当 `n` 是素数幂。
泛函定义在全部非空紧凸集上，使用 Hausdorff 拓扑。
[精确目标与量词](NRR/Statement.lean) · [原稿](round7/proof.md)

## 复核

工具链固定为 Lean **4.24.0** 和 mathlib **v4.24.0**，由
`lean-toolchain`、`lakefile.toml`、`lake-manifest.json` 指定。

```powershell
lake exe cache get
.\scripts\verify.ps1 -LeanThreads 1
```

脚本先确认每个 `NRR/**/*.lean` 都在默认导入闭包中，再执行 `lake build`、
`lake env lean ProofAudit.lean` 及 `python ../scripts/verify.py`。Windows 上可用
`-LeanBin 'C:\path\to\lean-4.24.0-windows\bin'` 指定工具链。
`ProofAudit.lean` 审计全部项目声明及私有辅助声明的传递公理依赖，只允许
`propext`、`Classical.choice`、`Quot.sound`，并检查最终定理的精确类型。
Python 有限精确算术检查用于交叉核对，不能替代 Lean 证明。
[验收记录](VERIFICATION.md)

## 证明链

负向定理通过平面修正、内柱定位、全部分割空间的紧性及全局连续拼接，
构造适配预先给定 `K,μ` 的反例，没有额外图表、密度下界或矩条件。
[负向主定理](NRR/PrescribedCounterexamples.lean)

正向证明使用真实配置空间、相对奇异链和取向特征：

1. [素数幂持久性](NRR/PrimePowerTopologyPrimePowerPersistence.lean) 算出实际
   洗牌入射符号，符号特征抵消相对取向；内部二项式系数的素数整除性使
   首个扭曲微分为零，最低类存活到整个配置空间。
2. [悬挂与 Euler 目标](NRR/PrimePowerTopologyAssociatedBMTargetNonzero.lean)
   由实际紧化悬挂、自然性及纤维作用的次数，证明正确取向下的目标非零。
3. [真正的扭曲基本循环](NRR/PrimePowerTopologyTwistedFundamentalCycle.lean)
   每个自由标号轨道取一个阶梯单形。带符号 transfer 展开为全部阶梯单形
   的有向和；链级 transfer 单射给出循环条件，无需除以群阶。
4. [局部检测](NRR/PrimePowerTopologyStaircaseLocalHomology.lean) 选定点只属于
   恒等排列的阶梯单形。[实际局部图](NRR/PrimePowerTopologyStaircaseLocalChart.lean)
   给出同调同构，[染色余循环](NRR/SingularHomologySimplexLocalDetection.lean)
   在恒等单形上取一，因而真实阶梯类非零。
5. [Euler 装配](NRR/PrimePowerTopologyStaircaseEulerSource.lean) 经实际环境与
   法向塌缩得到非零障碍，排除无零等变映射。
   [解析桥梁](NRR/PrimePowerExistencePowerConclusion.lean) 使用连续等质量幂图
   及正背景极限，得到公平分割，最后组成完整分类。

有序基本类直接投影后的 Euler 像恒为零；最终证明使用独立构造的轨道代表
循环，再通过 transfer 与有序循环比较。
[投影消失定理](NRR/PrimePowerTopologyAssociatedBMFundamental.lean)

## 原稿的附加结论

- [平面局部构造](NRR/PlanarExistence.lean) 及
  [全部可取总绕数](NRR/EndWindingRange.lean)。
- [稳健反例](NRR/RobustCounterexamples.lean)：近似等质量仍有严格正间隙，
  包括三维均匀球的六块反例。
- [六等分球帽与穿柱](NRR/BallCapSix.lean)：任意方向实际帽体积分数、
  六分之一体积凸块与内柱内部正体积相交、五个六分位高度的严格界。
- [普通矩多项式](NRR/BallPolynomialCounterexample.lean) 和
  [加性尾项](NRR/BallAdditiveMomentsPolynomial.lean) 的单位球反例。
- [所有维数共用同一对有理多项式](NRR/CubeEuclideanDimensions.lean)：先选
  `Pₙ,Qₙ`，再遍历所有 `d ≥ 3` 与标准立方体的每份真实等体积凸分割；
  四矩是以 `n/2^d` 归一化的 `x₁,x₂,(1+x₁)x_d,x₂x_d` 积分。
- [限制、归一化及环境分割截取](NRR/PrescribedPartitionCorollaries.lean)。

原稿及 Lean 定理给出存在性，未提取具体多项式系数、次数上界或数值全局
间隙。引用文献中二维任意块数等背景结果不属于本工程的证明目标。
[证明对应表](round7/formalization-plan.md) · [第三方来源与许可](third_party/README.md)
