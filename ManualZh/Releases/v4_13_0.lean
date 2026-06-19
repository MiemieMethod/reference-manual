/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Joachim Breitner
-/

import VersoManual

import Manual.Meta.Markdown

open Manual
open Verso.Genre


#doc (Manual) "Lean 4.13.0 (2024-11-01)" =>
%%%
tag := "release-v4.13.0"
file := "v4.13.0"
%%%

```markdown
**完整变更日志**：https://github.com/leanprover/lean4/compare/v4.12.0...v4.13.0

### 语言功能、策略和元程序

* `structure` 命令
  * [#5511](https://github.com/leanprover/lean4/pull/5511) 允许结构父级成为类型同义词。
  * [#5531](https://github.com/leanprover/lean4/pull/5531) 允许结构字段的默认值不可计算。

* `rfl` 和 `apply_rfl`策略
  * [#3714](https://github.com/leanprover/lean4/pull/3714)、[#3718](https://github.com/leanprover/lean4/pull/3718) 改进了 `rfl`策略并提供更好的错误消息。
  * [#3772](https://github.com/leanprover/lean4/pull/3772) 使 `rfl` 不再使用内核defeq 作为地面术语。
  * [#5329](https://github.com/leanprover/lean4/pull/5329) 使用 `@[refl]` 标记 `Iff.refl` (@Parcly-Taxel)
  * [#5359](https://github.com/leanprover/lean4/pull/5359) 确保 `rfl`策略尝试 `Iff.rfl` (@Parcly-Taxel)

* `unfold`策略
  * [#4834](https://github.com/leanprover/lean4/pull/4834) 让 `unfold` 执行局部定义的 zeta-delta 缩减，合并 Mathlib `unfold_let`策略的功能。

* `omega`策略
  * [#5382](https://github.com/leanprover/lean4/pull/5382) 修复了 [#5315](https://github.com/leanprover/lean4/issues/5315) 中的虚假错误
  * [#5523](https://github.com/leanprover/lean4/pull/5523) 支持 `Int.toNat`

* `simp`策略
  * [#5479](https://github.com/leanprover/lean4/pull/5479) 让 `simp` 应用具有高阶模式的规则。

* `induction`策略
  * [#5494](https://github.com/leanprover/lean4/pull/5494) 修复了 `induction` 的“pre-策略”块始终缩进，避免意外使用它。

* `ac_nf`策略
  * [#5524](https://github.com/leanprover/lean4/pull/5524) 添加了 `ac_nf`（`ac_rfl` 的对应项），用于标准化有关结合性和交换性的表达式。使用 `BitVec` 表达式对其进行测试。

* `bv_decide`
  * [#5211](https://github.com/leanprover/lean4/pull/5211) 使 `extractLsb'` 成为 `bv_decide` 理解的原语，而不是 `extractLsb` (@alexkeizer)
  * [#5365](https://github.com/leanprover/lean4/pull/5365) 添加 `bv_decide` 诊断。
  * [#5375](https://github.com/leanprover/lean4/pull/5375) 为 `ofBool (a.getLsbD i)` 和 `ofBool a[i]` 添加 `bv_decide` 标准化规则 (@alexkeizer)
  * [#5423](https://github.com/leanprover/lean4/pull/5423) 增强了 `bv_decide` 的重写规则
  * [#5433](https://github.com/leanprover/lean4/pull/5433) 在 API 上呈现 `bv_decide` 反例
  * [#5484](https://github.com/leanprover/lean4/pull/5484) 使用 `bv_decide` 中的 `Nat` fvar 处理 `BitVec.ofNat`
  * [#5506](https://github.com/leanprover/lean4/pull/5506)、[#5507](https://github.com/leanprover/lean4/pull/5507) 添加 `bv_normalize` 规则。
  * [#5568](https://github.com/leanprover/lean4/pull/5568) 概括 `bv_normalize` 管道以支持更通用的预处理过程
  * [#5573](https://github.com/leanprover/lean4/pull/5573) 使用当前的 `BitVec` 重写获取最新的 `bv_normalize`
  * 清理：[#5408](https://github.com/leanprover/lean4/pull/5408)、[#5493](https://github.com/leanprover/lean4/pull/5493)、[#5578](https://github.com/leanprover/lean4/pull/5578)


* 精化改进
  * [#5266](https://github.com/leanprover/lean4/pull/5266) 保留 `elab_as_elim` 过程中过度应用的参数的顺序。
  * [#5510](https://github.com/leanprover/lean4/pull/5510) 概括了 `elab_as_elim` 以允许任意动机应用。
  * [#5283](https://github.com/leanprover/lean4/pull/5283)、[#5512](https://github.com/leanprover/lean4/pull/5512) 优化命名参数抑制显式参数的方式。重大更改：一些以前省略的显式参数现在可能需要显式 `_` 参数。
  * [#5376](https://github.com/leanprover/lean4/pull/5376) 修改实例的投影实例绑定器信息，使类型中隐含的实例参数成为隐式参数。
  * [#5402](https://github.com/leanprover/lean4/pull/5402) 如果可能，将 Universe 元变量错误本地化到 `let` 绑定和 `fun` 绑定器。使“无法合成元变量”错误优先于未解决的 宇宙层级 错误。
  * [#5419](https://github.com/leanprover/lean4/pull/5419) 当归约性设置为 `.reducible` 时，不得在 `match` 表达式的判别式中归约 `ite`
  * [#5474](https://github.com/leanprover/lean4/pull/5474) 在失败时具有自动参数报告参数/字段
  * [#5530](https://github.com/leanprover/lean4/pull/5530) 使具有卫生名称的类型的自动实例名称变得卫生。

* 派生处理程序
  * [#5432](https://github.com/leanprover/lean4/pull/5432) 使 `Repr` 派生实例处理显式类型参数

* 功能性诱导
  * [#5364](https://github.com/leanprover/lean4/pull/5364) 在上下文中添加更多平等性，更仔细的清理。

* 短绒棉
  * [#5335](https://github.com/leanprover/lean4/pull/5335) 修复了抱怨匹配/策略组合的未使用变量 linter
  * [#5337](https://github.com/leanprover/lean4/pull/5337) 修复了未使用的变量 linter 抱怨某些通配符模式

* 其他修复
  * [#4768](https://github.com/leanprover/lean4/pull/4768) 修复了当 `..` 出现且下一行带有 `.` 时的解析错误

* 元编程
  * [#3090](https://github.com/leanprover/lean4/pull/3090) 处理 `Meta.evalExpr` 中的电平参数 (@eric-wieser)
  * [#5401](https://github.com/leanprover/lean4/pull/5401) `Inhabited (TacticM α)` 实例 (@alexkeizer)
  * [#5412](https://github.com/leanprover/lean4/pull/5412) 公开内核.check 用于调试目的
  * [#5556](https://github.com/leanprover/lean4/pull/5556) 改进了 `inferType` 中的“无效投影”类型推断错误。
  * [#5587](https://github.com/leanprover/lean4/pull/5587) 允许 `MVarId.assertHypotheses` 设置 `BinderInfo` 和 `LocalDeclKind`。
  * [#5588](https://github.com/leanprover/lean4/pull/5588) 添加了 `MVarId.tryClearMany'`，它是 `MVarId.tryClearMany` 的变体。



### 语言服务器、小部件和 IDE 扩展

* [#5205](https://github.com/leanprover/lean4/pull/5205) 减少了策略块中自动完成的延迟。
* [#5237](https://github.com/leanprover/lean4/pull/5237) 修复了当将文本光标从右侧移动到标识符时，VS Code 中的符号出现突出显示不突出显示的情况。
* [#5257](https://github.com/leanprover/lean4/pull/5257) 修复了报告的多个错误自动完成实例。
* [#5299](https://github.com/leanprover/lean4/pull/5299) 当精化器无法提供上下文特定的自动完成时，允许自动完成报告全局标识符的完成情况。
* [#5312](https://github.com/leanprover/lean4/pull/5312) 修复了更改模块标头后的空格时服务器崩溃的问题。
* [#5322](https://github.com/leanprover/lean4/pull/5322) 修复了自动完成报告不存在的命名空间的多个实例。
* [#5428](https://github.com/leanprover/lean4/pull/5428) 确保在等待精化时始终将一些最近的文件范围报告为进度。


### 漂亮的印刷

* [#4979](https://github.com/leanprover/lean4/pull/4979) 制作漂亮的打印机转义标识符（标记）。
* [#5389](https://github.com/leanprover/lean4/pull/5389) 使格式化程序使用当前标记表。
* [#5513](https://github.com/leanprover/lean4/pull/5513) 在格式化令牌时使用可破坏的空格而不是不可破坏的空格。


### 图书馆

* [#5222](https://github.com/leanprover/lean4/pull/5222) 减少 `Json.compress` 中的分配。
* [#5231](https://github.com/leanprover/lean4/pull/5231) 上游 `Zero` 和 `NeZero`
* [#5292](https://github.com/leanprover/lean4/pull/5292) 重构 `Lean.Elab.Deriving.FromToJson` (@arthur-adjedj)
* [#5415](https://github.com/leanprover/lean4/pull/5415) 实现 `Repr Empty` (@TomasPuverle)
* [#5421](https://github.com/leanprover/lean4/pull/5421) 实现 `To/FromJSON Empty` (@TomasPuverle)

* 逻辑
  * [#5263](https://github.com/leanprover/lean4/pull/5263) 允许仅使用 `Decidable (¬p)` 简化 `dite_not`/`decide_not`。
  * [#5268](https://github.com/leanprover/lean4/pull/5268) 修复了 `ite_eq_left_iff` 上的活页夹
  * [#5284](https://github.com/leanprover/lean4/pull/5284) 关闭 `Inhabited (Sum α β)` 实例
  * [#5355](https://github.com/leanprover/lean4/pull/5355) 为 `LawfulBEq` 添加简单引理
  * [#5374](https://github.com/leanprover/lean4/pull/5374) 为产品添加 `Nonempty` 实例，允许成功精化更多 `partial` 功能
  * [#5447](https://github.com/leanprover/lean4/pull/5447) 更新 Pi 实例名称
  * [#5454](https://github.com/leanprover/lean4/pull/5454) 使一些实例参数隐式
  * [#5456](https://github.com/leanprover/lean4/pull/5456) 添加 `heq_comm`
  * [#5529](https://github.com/leanprover/lean4/pull/5529) 将 `@[simp]` 从 `exists_prop'` 移动到 `exists_prop`

* `Bool`
  * [#5228](https://github.com/leanprover/lean4/pull/5228) 填补了布尔引理中的空白
  * [#5332](https://github.com/leanprover/lean4/pull/5332) 为 Bool.xor 添加符号 `^^`
  * [#5351](https://github.com/leanprover/lean4/pull/5351) 删除 `_root_.and`（和或/非/异或），而是导出/使用 `Bool.and`（等）。

* `BitVec`
  * [#5240](https://github.com/leanprover/lean4/pull/5240) 删除具有复杂 RHS 的 BitVec simps
  * [#5247](https://github.com/leanprover/lean4/pull/5247)`BitVec.getElem_zeroExtend`
  * [#5248](https://github.com/leanprover/lean4/pull/5248) BitVec 的简化引理，改进融合
  * [#5249](https://github.com/leanprover/lean4/pull/5249) 从一些 BitVec 引理中删除 `@[simp]`
  * [#5252](https://github.com/leanprover/lean4/pull/5252) 将 `BitVec.intMin/Max` 从缩写更改为定义
  * [#5278](https://github.com/leanprover/lean4/pull/5278) 添加 `BitVec.getElem_truncate` (@tobiasgrosser)
  * [#5281](https://github.com/leanprover/lean4/pull/5281) 为 `bv_decide` 添加 udiv/umod 位爆破 (@bollu)
  * [#5297](https://github.com/leanprover/lean4/pull/5297) `BitVec` 无符号阶理论结果
  * [#5313](https://github.com/leanprover/lean4/pull/5313) 为 UInt 添加更多基本 BitVec 排序理论
  * [#5314](https://github.com/leanprover/lean4/pull/5314) 添加 `toNat_sub_of_le` (@bollu)
  * [#5357](https://github.com/leanprover/lean4/pull/5357) 添加 `BitVec.truncate` 引理
  * [#5358](https://github.com/leanprover/lean4/pull/5358) 引入 `BitVec.setWidth` 来统一 ZeroExtend 和截断 (@tobiasgrosser)
  * [#5361](https://github.com/leanprover/lean4/pull/5361) 一些 BitVec GetElem 引理
  * [#5385](https://github.com/leanprover/lean4/pull/5385) 添加 `BitVec.ofBool_[and|or|xor]_ofBool` 定理 (@tobiasgrosser)
  * [#5404](https://github.com/leanprover/lean4/pull/5404) 更多 `BitVec.getElem_*` (@tobiasgrosser)
  * [#5410](https://github.com/leanprover/lean4/pull/5410) `Nat.{mul_two, two_mul, mul_succ, succ_mul}` 的 BitVec 类似物 (@bollu)
  * [#5411](https://github.com/leanprover/lean4/pull/5411) `BitVec.toNat_{add,sub,mul_of_lt}` 用于 BitVector 非溢出推理 (@bollu)
  * [#5413](https://github.com/leanprover/lean4/pull/5413) 为 `BitVec.[and|or|xor]` 添加 `_self`、`_zero` 和 `_allOnes` (@tobiasgrosser)
  * [#5416](https://github.com/leanprover/lean4/pull/5416) 为 `BitVec.[and|or|xor]` 添加 LawCommIdentity + IdempotOp (@tobiasgrosser)
  * [#5418](https://github.com/leanprover/lean4/pull/5418) BitVec 的可判定量词
  * [#5450](https://github.com/leanprover/lean4/pull/5450) 添加 `BitVec.toInt_[intMin|neg|neg_of_ne_intMin]` (@tobiasgrosser)
  * [#5459](https://github.com/leanprover/lean4/pull/5459) 缺少 BitVec 引理
  * [#5469](https://github.com/leanprover/lean4/pull/5469) 添加 `BitVec.[not_not, allOnes_shiftLeft_or_shiftLeft, allOnes_shiftLeft_and_shiftLeft]` (@luisacicolini)
  * [#5478](https://github.com/leanprover/lean4/pull/5478) 添加 `BitVec.(shiftLeft_add_distrib, shiftLeft_ushiftRight)` (@luisacicolini)
  * [#5487](https://github.com/leanprover/lean4/pull/5487) 添加 `sdiv_eq`、`smod_eq` 以允许 `sdiv`/`smod` 位爆破 (@bollu)
  * [#5491](https://github.com/leanprover/lean4/pull/5491) 添加 `BitVec.toNat_[abs|sdiv|smod]` (@tobiasgrosser)
  * [#5492](https://github.com/leanprover/lean4/pull/5492) `BitVec.(not_sshiftRight, not_sshiftRight_not, getMsb_not, msb_not)` (@luisacicolini)
  * [#5499](https://github.com/leanprover/lean4/pull/5499) `BitVec.Lemmas` - 删除非终端 simps (@tobiasgrosser)
  * [#5505](https://github.com/leanprover/lean4/pull/5505) 取消 `BitVec.divRec_succ'`
  * [#5508](https://github.com/leanprover/lean4/pull/5508) 添加 `BitVec.getElem_[add|add_add_bool|mul|rotateLeft|rotateRight…` (@tobiasgrosser)
  * [#5554](https://github.com/leanprover/lean4/pull/5554) 添加 `Bitvec.[add, sub, mul]_eq_xor` 和 `width_one_cases` (@luisacicolini)

* `List`
  * [#5242](https://github.com/leanprover/lean4/pull/5242) 改进 `List.mergeSort` 引理的命名
  * [#5302](https://github.com/leanprover/lean4/pull/5302) 提供 `mergeSort` 比较器 autoParam
  * [#5373](https://github.com/leanprover/lean4/pull/5373) 修复 `List.length_mergeSort` 的名称
  * [#5377](https://github.com/leanprover/lean4/pull/5377) 上游 `map_mergeSort`
  * [#5378](https://github.com/leanprover/lean4/pull/5378) 修改有关 `mergeSort` 的引理签名
  * [#5245](https://github.com/leanprover/lean4/pull/5245) 避免在没有 List.Impl 的情况下导入 `List.Basic`
  * [#5260](https://github.com/leanprover/lean4/pull/5260) 列表 API 的审核
  * [#5264](https://github.com/leanprover/lean4/pull/5264) 列表 API 的审核
  * [#5269](https://github.com/leanprover/lean4/pull/5269) 删除 HashMap 的重复 Pairwise 和 Sublist
  * [#5271](https://github.com/leanprover/lean4/pull/5271) 从 `List.head_mem` 和类似内容中删除 @[simp]
  * [#5273](https://github.com/leanprover/lean4/pull/5273) 关于 `List.attach` 的引理
  * [#5275](https://github.com/leanprover/lean4/pull/5275) `List.tail_map` 的反方向
  * [#5277](https://github.com/leanprover/lean4/pull/5277) 更多 `List.attach` 引理
  * [#5285](https://github.com/leanprover/lean4/pull/5285) `List.count` 引理
  * [#5287](https://github.com/leanprover/lean4/pull/5287) 在 `List.filter` 中使用布尔谓词
  * [#5289](https://github.com/leanprover/lean4/pull/5289) `List.mem_ite_nil_left` 和类似物
  * [#5293](https://github.com/leanprover/lean4/pull/5293) `List.findIdx` / `List.take` 引理的清理
  * [#5294](https://github.com/leanprover/lean4/pull/5294) 在 `List.getElem_take` 上切换素数
  * [#5300](https://github.com/leanprover/lean4/pull/5300)更多`List.findIdx`定理
  * [#5310](https://github.com/leanprover/lean4/pull/5310) 修复 `List.all/any` 引理
  * [#5311](https://github.com/leanprover/lean4/pull/5311) 修复 `List.countP` 引理
  * [#5316](https://github.com/leanprover/lean4/pull/5316) `List.tail` 引理
  * [#5331](https://github.com/leanprover/lean4/pull/5331) 修复 `List.getElem_mem` 的隐式性
  * [#5350](https://github.com/leanprover/lean4/pull/5350) `List.replicate` 引理
  * [#5352](https://github.com/leanprover/lean4/pull/5352) `List.attachWith` 引理
  * [#5353](https://github.com/leanprover/lean4/pull/5353) `List.head_mem_head?`
  * [#5360](https://github.com/leanprover/lean4/pull/5360) 关于 `List.tail` 的引理
  * [#5391](https://github.com/leanprover/lean4/pull/5391) `List.erase` / `List.find` 引理的审查
  * [#5392](https://github.com/leanprover/lean4/pull/5392) `List.fold` / `attach` 引理
  * [#5393](https://github.com/leanprover/lean4/pull/5393) `List.fold` 相关器
  * [#5394](https://github.com/leanprover/lean4/pull/5394) 关于 `List.maximum?` 的引理
  * [#5403](https://github.com/leanprover/lean4/pull/5403) 关于 `List.toArray` 的定理
  * [#5405](https://github.com/leanprover/lean4/pull/5405) `List.set_map` 方向相反
  * [#5448](https://github.com/leanprover/lean4/pull/5448) 添加有关 `List.IsPrefix` 的引理 (@Command-Master)
  * [#5460](https://github.com/leanprover/lean4/pull/5460) 缺少 `List.set_replicate_self`
  * [#5518](https://github.com/leanprover/lean4/pull/5518) 将 `List.maximum?` 重命名为 `max?`
  * [#5519](https://github.com/leanprover/lean4/pull/5519) 上游 `List.fold` 引理
  * [#5520](https://github.com/leanprover/lean4/pull/5520) 在 `List.getElem_mem` 等上恢复 `@[simp]`。
  * [#5521](https://github.com/leanprover/lean4/pull/5521) 列表简化修复
  * [#5550](https://github.com/leanprover/lean4/pull/5550) `List.unattach` 和简单引理
  * [#5594](https://github.com/leanprover/lean4/pull/5594) 感应友好型 `List.min?_cons`

* `Array`
  * [#5246](https://github.com/leanprover/lean4/pull/5246) 清理 Array.Lemmas 的导入
  * [#5255](https://github.com/leanprover/lean4/pull/5255) 拆分 Init.Data.Array.Lemmas 以实现更好的引导
  * [#5288](https://github.com/leanprover/lean4/pull/5288) 将 `Array.data` 重命名为 `Array.toList`
  * [#5303](https://github.com/leanprover/lean4/pull/5303) 清理 `List.getElem_append` 变体
  * [#5304](https://github.com/leanprover/lean4/pull/5304)`Array.not_mem_empty`
  * [#5400](https://github.com/leanprover/lean4/pull/5400) 数组/基本中的重组
  * [#5420](https://github.com/leanprover/lean4/pull/5420) 使 `Array` 函数可半简化或使用结构递归
  * [#5422](https://github.com/leanprover/lean4/pull/5422) 重构 `DecidableEq (Array α)`
  * [#5452](https://github.com/leanprover/lean4/pull/5452) 数组重构
  * [#5458](https://github.com/leanprover/lean4/pull/5458) 重构后清理数组文档字符串
  * [#5461](https://github.com/leanprover/lean4/pull/5461) 在 `Array.swapAt!_def` 上恢复 `@[simp]`
  * [#5465](https://github.com/leanprover/lean4/pull/5465) 改进 Array GetElem 引理
  * [#5466](https://github.com/leanprover/lean4/pull/5466) `Array.foldX` 引理
  * [#5472](https://github.com/leanprover/lean4/pull/5472) @[simp] 关于 `List.toArray` 的引理
  * [#5485](https://github.com/leanprover/lean4/pull/5485) `toArray_concat` 的反向简单方向
  * [#5514](https://github.com/leanprover/lean4/pull/5514) `Array.eraseReps`
  * [#5515](https://github.com/leanprover/lean4/pull/5515) 上游 `Array.qsortOrd`
  * [#5516](https://github.com/leanprover/lean4/pull/5516) 上游 `Subarray.empty`
  * [#5526](https://github.com/leanprover/lean4/pull/5526) 修复 `Array.length_toList` 的名称
  * [#5527](https://github.com/leanprover/lean4/pull/5527) 减少数组中已弃用引理的使用
  * [#5534](https://github.com/leanprover/lean4/pull/5534) 清理数组 GetElem 引理
  * [#5536](https://github.com/leanprover/lean4/pull/5536) 修复 `Array.modify` 引理
  * [#5551](https://github.com/leanprover/lean4/pull/5551) 上游 `Array.flatten` 引理
  * [#5552](https://github.com/leanprover/lean4/pull/5552) 将数组“bang”`[]!` 索引的明显情况切换为依赖于假设 (@TomasPuverle)
  * [#5577](https://github.com/leanprover/lean4/pull/5577) 将缺失的 sim 添加到 `Array.size_feraseIdx`
  * [#5586](https://github.com/leanprover/lean4/pull/5586)`Array/Option.unattach`

* `Option`
  * [#5272](https://github.com/leanprover/lean4/pull/5272) 从 `Option.pmap/pbind` 中删除 @[simp] 并添加 simpl 引理
  * [#5307](https://github.com/leanprover/lean4/pull/5307) 恢复 Option simp confluence
  * [#5354](https://github.com/leanprover/lean4/pull/5354) 从 `Option.bind_map` 中删除 @[simp]
  * [#5532](https://github.com/leanprover/lean4/pull/5532) `Option.attach`
  * [#5539](https://github.com/leanprover/lean4/pull/5539) 修复 `Option.mem_toList` 的显式性

* `Nat`
  * [#5241](https://github.com/leanprover/lean4/pull/5241) 将 @[simp] 添加到 `Nat.add_eq_zero_iff`
  * [#5261](https://github.com/leanprover/lean4/pull/5261) Nat 按位引理
  * [#5262](https://github.com/leanprover/lean4/pull/5262) `Nat.testBit_add_one` 不应是全局简单引理
  * [#5267](https://github.com/leanprover/lean4/pull/5267) 保护一些 Nat 按位定理
  * [#5305](https://github.com/leanprover/lean4/pull/5305) 重命名 Nat 按位引理
  * [#5306](https://github.com/leanprover/lean4/pull/5306) 添加 `Nat.self_sub_mod` 引理
  * [#5503](https://github.com/leanprover/lean4/pull/5503) 将 @[simp] 恢复到上游 `Nat.lt_off_iff`

* `Int`
  * [#5301](https://github.com/leanprover/lean4/pull/5301) 将 `Int.div/mod` 重命名为 `Int.tdiv/tmod`
  * [#5320](https://github.com/leanprover/lean4/pull/5320) 将 `ediv_nonneg_of_nonpos_of_nonpos` 添加到 DivModLemmas (@sakehl)

* `Fin`
  * [#5250](https://github.com/leanprover/lean4/pull/5250) 缺少关于 `Fin.ofNat'` 的引理
  * [#5356](https://github.com/leanprover/lean4/pull/5356) `Fin.ofNat'` 使用 `NeZero`
  * [#5379](https://github.com/leanprover/lean4/pull/5379) 从 Fin 引理中删除一些 @[simp]
  * [#5380](https://github.com/leanprover/lean4/pull/5380) 缺少 Fin @[simp] 引理

* `HashMap`
  * [#5244](https://github.com/leanprover/lean4/pull/5244) (`DHashMap`|`HashMap`|`HashSet`).(`getKey?`|`getKey`|`getKey!`|`getKeyD`)
  * [#5362](https://github.com/leanprover/lean4/pull/5362) 删除上次使用的 `Lean.(HashSet|HashMap)`
  * [#5369](https://github.com/leanprover/lean4/pull/5369)`HashSet.ofArray`
  * [#5370](https://github.com/leanprover/lean4/pull/5370) `HashSet.partition`
  * [#5581](https://github.com/leanprover/lean4/pull/5581) `HashMap`/`Set` 的 `Singleton`/`Insert`/`Union` 实例
  * [#5582](https://github.com/leanprover/lean4/pull/5582)`HashSet.all`/`any`
  * [#5590](https://github.com/leanprover/lean4/pull/5590) 为 `HashMap`/`Set.Raw` 添加 `Insert`/`Singleton`/`Union` 实例
  * [#5591](https://github.com/leanprover/lean4/pull/5591)`HashSet.Raw.all/any`

* `Monads`
  * [#5463](https://github.com/leanprover/lean4/pull/5463) 上游一些单子引理
  * [#5464](https://github.com/leanprover/lean4/pull/5464) 调整 monad 引理上的 simp 属性
  * [#5522](https://github.com/leanprover/lean4/pull/5522) 更多一元简单引理

* 简单引理清理
  * [#5251](https://github.com/leanprover/lean4/pull/5251) 删除多余的 simp 注释
  * [#5253](https://github.com/leanprover/lean4/pull/5253) 删除无法触发的 Int simpl 引理
  * [#5254](https://github.com/leanprover/lean4/pull/5254) iff 两侧出现的变量应该是隐式的
  * [#5381](https://github.com/leanprover/lean4/pull/5381) 清理多余的简单引理


### 编译器、运行时和 FFI

* [#4685](https://github.com/leanprover/lean4/pull/4685) 修复了 C `run_new_frontend` 签名中的拼写错误
* [#4729](https://github.com/leanprover/lean4/pull/4729) IR 检查器建议使用 `noncomputable`
* [#5143](https://github.com/leanprover/lean4/pull/5143) 为 Lake 添加共享库
* [#5437](https://github.com/leanprover/lean4/pull/5437) 删除（语法上）重复导入 (@euprunin)
* [#5462](https://github.com/leanprover/lean4/pull/5462) 将 `src/lake/lakefile.toml` 更新为调整后的 Lake 构建过程
* [#5541](https://github.com/leanprover/lean4/pull/5541) 在构建之前删除新的共享库，以更好地支持 Windows
* [#5558](https://github.com/leanprover/lean4/pull/5558) 使用 MSVC 编译 `lean.h` (@kant2002)
* [#5564](https://github.com/leanprover/lean4/pull/5564) 删除不合格的 size-0 数组 (@eric-wieser)


### Lake
  * Reservoir 构建缓存。 Lake 现在将在构建之前尝试从 Reservoir 获取包的预构建副本。仅对leanprover 或leanprover 社区组织中由Reservoir 索引的版本上的软件包启用此功能。用户可以通过在 CLI 上传递 --no-cache 或将 LAKE_NO_CACHE 环境变量设置为 true 来强制 Lake 从源构建包。 [#5486](https://github.com/leanprover/lean4/pull/5486)、[#5572](https://github.com/leanprover/lean4/pull/5572)、[#5583](https://github.com/leanprover/lean4/pull/5583)、[#5600](https://github.com/leanprover/lean4/pull/5600)、[#5641](https://github.com/leanprover/lean4/pull/5641)、 [#5642](https://github.com/leanprover/lean4/pull/5642)。
  * [#5504](https://github.com/leanprover/lean4/pull/5504) Lake new 和 Lake init 现在默认生成 TOML 配置。
  * [#5878](https://github.com/leanprover/lean4/pull/5878) 修复了一个严重问题：当尝试清理名称不正确所需的依赖项时，Lake 会删除路径依赖项。

  * **重大变更**
    * [#5641](https://github.com/leanprover/lean4/pull/5641) 包内目标的 Lake 构建将不再构建包的依赖项包级额外目标依赖项。在技​​术层面上，包的 extraDep 方面不再传递地构建其依赖项的 extraDep 方面（其中包括其 extraDepTargets）。

### 文档修复

* [#3918](https://github.com/leanprover/lean4/pull/3918) `@[builtin_doc]` 属性 (@digama0)
* [#4305](https://github.com/leanprover/lean4/pull/4305) 解释借位语法 (@eric-wieser)
* [#5349](https://github.com/leanprover/lean4/pull/5349) 添加了 `groupBy.loop` 的文档 (@vihdzp)
* [#5473](https://github.com/leanprover/lean4/pull/5473) 修复了 `BitVec.mul` 文档字符串中的拼写错误 (@llllvvuu)
* [#5476](https://github.com/leanprover/lean4/pull/5476) 修复了 `Lean.MetavarContext` 中的拼写错误
* [#5481](https://github.com/leanprover/lean4/pull/5481) 删除提及 `Lean.withSeconds` (@alexkeizer)
* [#5497](https://github.com/leanprover/lean4/pull/5497) 更新了 `toUIntX` 函数的文档和测试 (@TomasPuverle)
* [#5087](https://github.com/leanprover/lean4/pull/5087) 提到 `inferType` 不能确保类型正确性
* 对文档字符串中的拼写进行了许多修复，(@euprunin)： [#5425](https://github.com/leanprover/lean4/pull/5425) [#5426](https://github.com/leanprover/lean4/pull/5426) [#5427](https://github.com/leanprover/lean4/pull/5427) [#5430](https://github.com/leanprover/lean4/pull/5430) [#5431](https://github.com/leanprover/lean4/pull/5431) [#5434](https://github.com/leanprover/lean4/pull/5434) [#5435](https://github.com/leanprover/lean4/pull/5435) [#5436](https://github.com/leanprover/lean4/pull/5436) [#5438](https://github.com/leanprover/lean4/pull/5438) [#5439](https://github.com/leanprover/lean4/pull/5439) [#5440](https://github.com/leanprover/lean4/pull/5440) [#5599](https://github.com/leanprover/lean4/pull/5599)

### CI 的变化

* [#5343](https://github.com/leanprover/lean4/pull/5343) 允许通过注释添加 `release-ci` 标签 (@thorimur)
* [#5344](https://github.com/leanprover/lean4/pull/5344) 在工作流程中正确设置检查级别 (@thorimur)
* [#5444](https://github.com/leanprover/lean4/pull/5444) Mathlib 的 `lean-pr-testing-NNNN` 分支应使用电池的 `lean-pr-testing-NNNN` 分支
* [#5489](https://github.com/leanprover/lean4/pull/5489) 更新 `lean-pr-testing` 分支时提交 `lake-manifest.json`
* [#5490](https://github.com/leanprover/lean4/pull/5490) 在 `pr-release.yml` 中使用单独的机密进行注释和分支

```
