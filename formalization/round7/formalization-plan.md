# 原稿与 Lean 证明对应表

更新于 2026-11-28，Lean/mathlib 4.24.0。主分类的无条件证明项已完成：
`NRR.fullClassification : NRR.FullClassification`，保持原稿先给定凸体与测度
的量词顺序。最终类型没有待提供的拓扑障碍、非零基本类或 Thom 假设。

## 主命题

| 原稿结论 | Lean 接口 | 源码 |
| --- | --- | --- |
| 给定凸体与测度的非素数幂反例 | `prescribedCounterexamples : PrescribedCounterexamples` | [PrescribedCounterexamples](../NRR/PrescribedCounterexamples.lean) |
| 素数幂公平分割 | `primePowerExistence : PrimePowerExistence` | [Conclusion](../NRR/PrimePowerTopologyConclusion.lean) |
| 完整分类 | `fullClassification : FullClassification` | [Conclusion](../NRR/PrimePowerTopologyConclusion.lean) |
| 实际配置空间等变零点定理，环境维数至少二 | `configuration_equivariant_has_zero` | [Conclusion](../NRR/PrimePowerTopologyConclusion.lean) |
| 原测度上的解析桥梁 | `universalFairness_of_configuration_zero` | [PowerConclusion](../NRR/PrimePowerExistencePowerConclusion.lean) |

## 正向拓扑证明

| 步骤 | 已验证对象与结论 | 模块 |
| --- | --- | --- |
| 相邻 Fuks 层 | 真实有限圆盘附着、普通相对同调、胞腔基、三层长正合 | [GeneralCellHomology](../NRR/PrimePowerTopologyGeneralCellHomology.lean)、[FuksTriple](../NRR/PrimePowerTopologyFuksTriple.lean) |
| 扭曲比较 | 自由轨道奇异链、等变填充、底次投影满射与高层低次消失 | [TwistedBottomComparison](../NRR/PrimePowerTopologyTwistedBottomComparison.lean) |
| 所有素数的持久性 | 真实洗牌符号、特征抵消、素数幂内部二项式整除、最低类存活 | [PrimePowerPersistence](../NRR/PrimePowerTopologyPrimePowerPersistence.lean) |
| 实悬挂 | 好邻域、实际塌缩、约化悬挂同构、proper 映射自然性与欧氏迭代 | [Geometry](../NRR/SingularHomologyBMSuspensionGeometry.lean)、[GeometricIteration](../NRR/PrimePowerTopologyBMSuspensionGeometricIteration.lean) |
| Euler 目标 | 纤维重标号作用等于 `sign^d`，解悬挂到存活最低类，正确取向的目标非零 | [TargetNonzero](../NRR/PrimePowerTopologyAssociatedBMTargetNonzero.lean) |
| 真正扭曲循环 | 每个轨道取一代表，transfer 展开为全部实际阶梯链，链级单射检测循环 | [FundamentalCycle](../NRR/PrimePowerTopologyTwistedFundamentalCycle.lean) |
| 源非零 | 选定点仅在恒等单形中，真实局部同调同构，染色余循环取一 | [LocalChart](../NRR/PrimePowerTopologyStaircaseLocalChart.lean)、[SimplexLocalDetection](../NRR/SingularHomologySimplexLocalDetection.lean)、[LocalHomology](../NRR/PrimePowerTopologyStaircaseLocalHomology.lean) |
| 环境与法向像 | 阶梯类是实际环境塌缩像，普通局部检测与 transfer 自然性给法向像非零 | [Ambient](../NRR/PrimePowerTopologyStaircaseAmbient.lean)、[EulerSource](../NRR/PrimePowerTopologyStaircaseEulerSource.lean) |
| Euler 障碍与分类 | 秩一法向群闭包含在素数幂时为同构，Euler 非零排除无零截面，接解析桥梁 | [EulerThomPrimePower](../NRR/PrimePowerTopologyEulerThomPrimePower.lean)、[Conclusion](../NRR/PrimePowerTopologyConclusion.lean) |

群阶在模素数系数下不必可逆，证明没有除以群阶。有序基本类的直接投影
被 Euler 映射消去；最终证明构造独立的轨道代表循环，通过 transfer 检测。

## 负向与原稿强化

| 原稿部分 | 接口或范围 | 模块 |
| --- | --- | --- |
| 圆柱零水平矩刚性 | 实际块为水平层及相邻层分离 | [CylinderRigidity](../NRR/CylinderRigidity.lean)、[CylinderExtension](../NRR/CylinderExtension.lean) |
| 平面局部修正 | `LocalModel.exists_planar_correction`、`balanced_square_rigidity` | [PlanarExistence](../NRR/PlanarExistence.lean)、[LocalModel](../NRR/LocalModel.lean) |
| 精确绕数范围 | `actualTotals_eq_coset`，六块绕数重数 | [EndWindingRange](../NRR/EndWindingRange.lean) |
| 任意给定凸体与测度反例 | 定位、全分割空间紧性、统一邻域及连续拼接 | [PrescribedCounterexamples](../NRR/PrescribedCounterexamples.lean) |
| 稳健性及六块球反例 | 近似等质量的严格间隙及原广义命题的否定 | [RobustCounterexamples](../NRR/RobustCounterexamples.lean) |
| 三维球帽的直接核验 | 任意法向帽体积、六分之一块穿柱正体积、五个内部六分位 | [BallCapSix](../NRR/BallCapSix.lean) |
| 球上的普通矩有理多项式 | 有限矩、多项式逼近及加性尾项 | [BallPolynomialCounterexample](../NRR/BallPolynomialCounterexample.lean)、[BallAdditiveMomentsPolynomial](../NRR/BallAdditiveMomentsPolynomial.lean) |
| 三维立方体全部分割 | `exists_rational_polynomials_for_partitions`，含严格正间隙 | [CubePartitionLocalStacks](../NRR/CubePartitionLocalStacks.lean) |
| 同一对多项式跨所有维数 | `exists_same_polynomials_all_dimensions`，先选多项式后遍历全部维数与真实分割 | [CubeEuclideanDimensions](../NRR/CubeEuclideanDimensions.lean) |
| 高维乘积刚性与实际积分 | BM 等号、逐块集合乘积分解、保体积换元、`n/2^d` 与末坐标 | [CubeProductRigidity](../NRR/CubeProductRigidity.lean)、[CubeEuclideanDimensions](../NRR/CubeEuclideanDimensions.lean) |
| 测度和分割传递 | 限制归一化与环境分割截取 | [PrescribedPartitionCorollaries](../NRR/PrescribedPartitionCorollaries.lean) |

## 验收与范围

[默认入口](../NRR.lean) 覆盖每个项目源文件；[ProofAudit](../ProofAudit.lean)
检查全部项目及私有声明，只允许 `propext`、`Classical.choice`、`Quot.sound`。
[统一脚本](../scripts/verify.ps1) 运行覆盖检查、完整构建、公理审计和
[精确算术脚本](../../scripts/verify.py)。[最新验收记录](../VERIFICATION.md)。

`classification_iff` 只是逻辑等价，验收检查的是无条件的两个具体证明项。
主分类不替代上表各独立强化。文献中二维任意块数等背景结果不在本工程
范围内；正向声明为 `BodyPartition`，负向对环境分割的适用性另由截取引理
给出。原稿是存在性证明，未有效提取具体多项式系数、次数上界和数值间隙。
历史 149、235 文件的统计仅适用于当时快照。
