# 一张表已经够好，怎样在排序之前知道？

固定规模 $n$，对均匀随机排列执行普通 Shellsort，用 $C(w,\pi)$ 记预定表 $w$ 在输入 $\pi$ 上的实际键比较数。两种选表任务很接近，却需要不同的证据。

**要确认精确最优，可以先排除一批表。** 间隔 $h$ 的一趟有 $n-h$ 个不在链首的槽。线性插入处理每个这样的槽都至少做一次键比较，即使数组原本有序。于是每张表都有一个只须看间隔就能算出的下界
$$
S(w)=\sum_{h\in w}(n-h)\le \mathbb E_\pi C(w,\pi).
$$
如果已知一张表的均值至多为 $B$，则 $S(w)>B$ 的候选全部出局。若只求最小值，$S(w)=B$ 的表也不可能改进已有见证；若要找全并列赢家，仅凭这个下界则不能排除等号。Lean 给出保留等号时保持精确最小值的证书。余下的候选仍可能很多。[精确最小值的剪枝条件](https://github.com/EternalYMZ/Shellsort-gap-table-generation/blob/73b376a6ada92ee96a2e1af83878cd27bdae2c33/Shellsort/OptimalScanPruning.lean)

**要找到一张平均达到 $O(n\log n)$ 的表，可以接受常数倍差距。** 从项目指定的候选族随机抽表，用独立于将来输入的排列实跑评分。困难在于，若测试设有比较上限，一张偶尔极差的表可能因测试被截断而显得便宜。证明先控制各组结束时平方位移的高阶矩，再界定尾部过大的候选所占比例，才能说明截断损失。这里抽表与抽测试排列是两次不同的随机选择。[实际前缀的矩估计](https://github.com/EternalYMZ/Shellsort-gap-table-generation/blob/73b376a6ada92ee96a2e1af83878cd27bdae2c33/Shellsort/ActualMenuMoment.lean) · [抽表后的尾界](https://github.com/EternalYMZ/Shellsort-gap-table-generation/blob/73b376a6ada92ee96a2e1af83878cd27bdae2c33/Shellsort/PredrawnMenuMoment.lean)

本仓库公开核验了这些中间估计及剪枝定理。随机选出达阶表的完整规划开销有解析论证；对每个 $n$ 廉价确定精确最优表，以及最优首项常数是否收敛，仍待证明。
