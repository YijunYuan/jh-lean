# JH 原像与第二原像安全界的 Lean 形式化

本项目形式化 Changlun Li、Hongli Li、Yijun Yuan、Fengmei Liu、Shanwen Wang、Honggang Hu 所著 *Near-n-Bit Preimage and Second-Preimage Security of the JH Mode* 中的固定目标原像界，以及采用共同占用阈值的固定原消息第二原像界。以下编号均以该文为准。[Lean 库入口](JH.lean) · [英文 README](README.md)

## 源码目录与导入

从主定理读起可直接 `import JH`，也可以分别导入 `JH.Preimage`、`JH.SecondPreimageBound`、`JH.RandomTarget` 或 `JH.Parameters.WeightedOptimality`。每个 `*Spec.lean` 与证明放在同一目录。下表按论文的证明顺序列出目录，也可用于迁移原先直接导入子模块的代码。

| 论文位置 | 在哪里读 | 模块怎样分组 |
| --- | --- | --- |
| §2.2、§3.2 的置换实验与式 (8) | [预言机](JH/Oracle) | 实验、程序和新鲜查询前沿在目录顶层。`Lazy` 放惰性采样，`Independent` 放独立应答和坐标带，`Coupling` 放单步及完整试验的耦合。例如原来的 `JH.Oracle.CoupledTrial` 现为 `JH.Oracle.Coupling.Trial`。 |
| §3.1–3.2 的记录图演化 | [图基础](JH/Graph) · [逐轮演化](JH/Graph/Evolution) | 通用的走法、嫁接和 Menger 定理在 `Graph`。记录图专用的 `RecordEvolution`、`Round`、`StoppedGraph` 在 `Graph.Evolution`。 |
| §3.3 的残余图连通性 | [连通性](JH/Connectivity) | 引理 1 的端点、引理 2 的偏移测试、引理 3 的路径见证与概率界放在一起。原 `Graph` 下的 `FlowWitness*` 和 `Probability` 下的 `FlowTail*` 都移到这里，文件名沿用原名。 |
| §3.4 的势与账户 | [势函数](JH/Potential) · [单步漂移](JH/Potential/Drift) · [势越界](JH/Potential/Barrier) | 从 `Weights` 和 `Patterns` 读到 `Drift.Charge`、`Drift.Mean`，最后到 `Barrier.Tail`。原来的 `JH.Probability.Barrier` 仍提供通用的超鞅估计。 |
| §3.4 的占用与首次相交 | [边界增长](JH/Boundary) | `ForwardEvents`、`BackwardEvents` 和 `Mean` 给出逐轮估计。`OccupancyTail`、`IntersectionPopulation` 和 `IntersectionTail` 将它们用于停止事件。 |
| §2.4 的概率工具与式 (11) | [概率](JH/Probability) · [随机带](JH/Probability/Tape) | `Probability` 保留条件分布、停止不等式和首次停止事件的合并。`Tape.AdaptiveMean`、`Tape.Tests` 提供多处尾界共用的逐前缀估计。 |
| §3.2 的原消息与定理 2(2) | [第二原像](JH/SecondPreimage) | 从 `OriginalPhase` 读到 `Trace` 和 `Coverage`，再看 `PreloadedCache` 与 `Coupling` 如何处理披露前后的预算。[最终概率界](JH/SecondPreimageBound.lean) |
| §3.5、附录 A.1–A.4 | [有限证书与参数](JH/Parameters) · [加权最优化](JH/Parameters/WeightedOptimality) | `Certificate`、`Uniform` 给出有限界及显式取参。`WeightedOptimality.Lower`、`Upper` 和 `Limits` 对应加权损失的下界、上界和极限。[最优化定理](JH/Parameters/WeightedOptimality.lean) |

移动子模块只需调整 `import`。例如引理 3 的概率证明现在用 `import JH.Connectivity.FlowTail`，其中的声明仍使用原有的 Lean 命名空间。

## 从主定理进入证明

| 论文结果 | Lean 声明及其内容 |
| --- | --- |
| 定理 2(1)，式 (A.5) | 对独立于置换选定的摘要，在等权证书和访问预算下，成功率至多为 $5\cdot 2^{-\lambda-3}<2^{-\lambda}$。其中一项预算用于控制耦合分离项 $\binom{Q}{2}/N^2$。[`preimage_finite`](JH/Preimage.lean) |
| 定理 2(2) | 先固定原消息，再披露其求值轨迹。若原消息至多有 `L` 个填充分组，前后两侧均取 `C = 2 Bpot + 2L`，则成功率至多为 `6 · 2^(−λ−3) < 2^(−λ)`。[`second_preimage_finite`](JH/SecondPreimageBound.lean) |
| 式 (37)–(39)、(A.9) | `uniform_parameter_feasibility` 给出一般的等权取参。`preimage_explicit_sqrt` 取 `χ = ⌈√(n/2)⌉`、`λ = ⌊√(2n)⌋`，适用于 `n ≥ 4`。[参数构造](JH/Parameters/Uniform.lean) · [显式原像界](JH/Preimage.lean) |
| 式 (A.3)–(A.5)、(A.11) | 正权重 θ 决定单步费用系数 J 和漂移分子 D，有限证书给出相同的固定目标概率界。最优权重为 `Binh^(1/d)`。[`preimage_weighted_finite`](JH/Preimage.lean) · [权重最优化](JH/Analysis/Convex.lean) |
| 式 (A.12) 的加权部分、(A.14) | 在 `λ = 1` 的固定目标加权证书族内，最小损失为 `C∗√n + log₂ n + O(1)`。`C∗` 是 (A.14) 的最小值。`query_lower_bound` 把可行证书用于真实实验。[常数的极小值](JH/Analysis/WeightedConstant.lean) · [`loss_asymptotic`](JH/Parameters/WeightedOptimality.lean) |

定理 3 的联合第二原像界采用不同的前向、后向占用阈值。式 (35)–(36)、(A.6)–(A.7) 以及式 (40) 的显式第二原像参数界见论文。数值参数的代入由配套的精确算术检查器核验。Lean 的第二原像主定理对应上表中的定理 2(2)。

## 预算与参数

论文中的 `q` 是提交候选消息前的新鲜查询预算，`Q = q + Lα` 还计入候选消息的验证。Lean 的 `FixedTargetBudget q` 和第二原像定理形参 `q` 都已计入验证，对应论文的 `Q`。第二原像实验在披露后使用这份预算。设原消息有 `ℓ` 个填充分组，完整程序的耦合须覆盖披露前后的 `ℓ + Q` 次新鲜访问。`Padding` 要求编码单射且分组序列非空。应用论文的具体数值时，式 (4) 提供从消息位长到填充分组数的上界。[原像实验](JH/PreimageSpec.lean) · [第二原像实验](JH/SecondPreimageSpec.lean) · [填充](JH/Model.lean)

| `Params` 中的名称 | 论文符号 | 含义 |
| --- | --- | --- |
| `N`、`U` | N、U | 半状态空间大小 `2^n` 和预算因子 `2^s` |
| `pi` | $B_{\mathrm{path}}$ | 同一行到同一列的顶点不交残余路径条数阈值 |
| `Pi`、`Theta` | $B_{\mathrm{ver}}$、$B_{\mathrm{pair}}$ | 单侧端点支撑及端点对的上界，见 (12) |
| `nu`、`Gamma` | $B_{\mathrm{inh}}$、$B_{\mathrm{pot}}$ | 继承次数参数和势阈值，$B_{\mathrm{pot}}=B_{\mathrm{ver}}B_{\mathrm{inh}}$ |
| `Psi`、`sprPsi L` | $C_0$、$C$ | $2B_{\mathrm{pot}}$ 和 $2B_{\mathrm{pot}}+2L$，见 (24)、(A.1) |

证明中名为 `ledger` 的量是式 (18) 的 *account*，由平移势与单点模式的嫁接计数组成。式 (30) 中的因子 8 乘整个括号。核对证书中的不等号、取整和预算时可直接查阅完整的量化声明。[证书定义](JH/Parameters/CertificateSpec.lean) · [停止图与账户](JH/Graph/Evolution/StoppedGraphSpec.lean)

## 按论文顺序查阅

| 论文位置 | 对应的定义与证明 |
| --- | --- |
| §2.2、§3.1，式 (3)、(6)、(7) | 一条记录的输入速率和输出容量确定异或偏移。虚拟起点确保验证见证至少使用一个分组。继承闭包与嫁接终止给出残余图的严格阈值。[压缩与路径](JH/ModelProofs.lean) · [嫁接阈值](JH/Graph/Evolution/RecordEvolution.lean) |
| §2.4，式 (5) | 有限时域非负超鞅的 Ville 最大不等式。[停止时刻证明](JH/Probability/Stopping.lean) |
| §3.2，式 (8)–(11) | 惰性置换与独立应答在共同历史上的分离概率由 (8) 控制。第二原像另外计入原轨迹重复容量的概率 (9)。首次偏离与返回给出到 (10) 中目标列的路径。[自适应耦合](JH/Oracle/Coupling/Trial.lean) · [原消息阶段](JH/SecondPreimage/OriginalPhase.lean) · [返回路径](JH/SecondPreimage/Trace.lean) |
| §3.3，定理 1、引理 1–3 | 有向 Menger 定理允许分离集包含端点。它给出引理 1 的端点界，再由引理 2 的偏移测试和引理 3 的路径编码得到 (14)。[Menger 定理](JH/Graph/Menger.lean) · [端点支撑](JH/Connectivity/Endpoints.lean) · [偏移测试](JH/Connectivity/ShiftTest.lean) · [编码计数](JH/Connectivity/FlowTailBounds.lean) |
| §3.4，式 (15)–(22) | 平移势、受限支撑计数及引理 4 的单步费用控制各个账户。对账户应用有限指数估计，再取并集得到首次势越界的上界。[平移势](JH/Potential/Weights.lean) · [单步均值](JH/Potential/Drift/Mean.lean) · [势越界](JH/Potential/Barrier/Tail.lean) |
| §3.4，式 (23)–(29) | 对一条线选择有继承的轮次，得到占用尾界。两侧顶点总数的期望和逐轮相交概率给出共同阈值下的 (29)。[占用](JH/Boundary/OccupancyTail.lean) · [顶点数](JH/Boundary/IntersectionPopulation.lean) · [首次相交](JH/Boundary/IntersectionTail.lean) |
| §3.5，式 (30)–(34) | 四类首次停止事件加上置换耦合项给出原像界。第二原像另外计入原消息的容量碰撞项。[首次停止](JH/Probability/FirstStop.lean) · [证书推论](JH/Parameters/Certificate.lean) |
| 引言中提及的均匀消息目标归约 | 若目标由哈希均匀原消息产生，且对手只看到摘要，成功率至多为 `ε_spr + (N / D) ε_pre`，其中 `D = 2^(α+1) − 2` 是长度从 1 到 α 的消息数。§2.2 还给出独立抽取目标时的固定目标平均界。[随机目标归约](JH/RandomTarget.lean) |

## 构建核验

本发布版使用 Lean 4.36.0 和 mathlib v4.36.0，mathlib 锁定提交为 `fc4f59e577feb1a4956671bc04ac18aaaf8cd842`。`*Spec.lean` 保存定义和完整命题，配套模块给出证明。`statements.sha256` 校验登记文件的完整内容，包括注释。核验脚本先检查校验值，再构建库，并在独立的 `JH.Audit` 模块逐项检查命题类型与传递公理。[依赖锁](lake-manifest.json) · [核验脚本](verify.ps1) · [审计入口](JH/Audit.lean)

在项目根目录运行 `./verify.ps1`。若已有与锁文件匹配的编译缓存，也可运行 `./verify.ps1 -CacheRoot './.lake/packages'`。允许的基础公理为 `propext`、`Classical.choice` 和 `Quot.sound`。
