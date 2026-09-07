# LeanEval 陈定理提交

提交日期：2026-09-07。

- 当前提交：[lean-eval-submissions #1696](https://github.com/leanprover/lean-eval-submissions/issues/1696)
- 自动验证：[run 34135760424](https://github.com/leanprover/lean-eval-submissions/actions/runs/34135760424)
- 评测源码：[固定提交 947f799](https://github.com/lixiang90/chen_theorem/tree/947f7990ef9b9a0f1bd021f5ed489020d42e0d5b)
- 原形式化证明：[提交 3264ad6](https://github.com/lixiang90/chen_theorem/tree/3264ad6acafa64ada18a309f48350d9acfd261ef)
- 声明的系统：**OpenAI Codex (GPT-6 + GPT-5.6 Sol)**，在人类指导下完成。

## 题目与提交资格

官方题目 `chen_theorem`、statement revision 1 要求：存在无穷多个素数 `p`，
使 `p + 2` 为素数或两个素数的乘积。本项目的 `Chen.chen_twin` 对任意正偶数
平移成立，提交将其特化为 2，并显式转换到官方的 `HasAtMostTwoPrimeFactors`。

LeanEval 按用户、声明模型、题目和题目版本分别记录成功结果，没有仅限首个
证明者的条件。已有 [#1584](https://github.com/leanprover/lean-eval-submissions/issues/1584)
在北京时间 2026-09-01 被接受；本提交不作首次形式化或首次提交的优先权声明。

## 官方自动验证流程

官方首先按 `lakefile.toml` 的 `name` 和相邻 `Submission.lean` 识别题目，
冻结源码提交并保留加密归档。压缩源码上限为 10 MiB，因此本项目使用独立的
`codex/lean-eval-chen` 分支，仅包含评测源码，不含论文扫描件、PDF、Git 历史或缓存。

评测在可信生成工作区上只覆盖 `Submission.lean` 与 `Submission/**/*.lean`，
不采用提交方修改的题目、`Solution.lean`、配置或依赖版本。
固定环境为 Lean `v4.33.0`，Mathlib
`6f1ef4e5dd604a435bddba4747b13970cd65d2a1`。
Comparator 在 landrun 沙箱中独立构建题目和解答，检查精确陈述及允许的公理，
并通过 nanoda 独立内核重放；成功后才记入公开结果。

当前官方主入口要求私有 GitHub 仓库及两个只读 App。本项目源码已经公开，
因此采用官方仍开放的 GitHub issue API 入口。该通道至少开放至
2026-09-30；没有要求为此次公开源码提交安装额外 App。

## 可重现的准备过程

打包脚本从原项目的已提交 Git blobs 读取证明，保留来源哈希，把本地模块
重定位到 `Submission/`，显式保持原源码的 `autoImplicit` 设置，并加入题目桥接。
`scripts/lean_eval_compat.json` 记录固定 Mathlib 版本的逐项兼容性修改；
脚本要求每段原文恰好匹配一次，并在来源元数据中记录补丁文件的 LF 规范化哈希。
原项目的 Lean 4.32.2 证明文件保持不变。PNT/Mertens/Perron 的 Apache-2.0
许可证、NOTICE 和来源信息保留在对应目录下。

```text
git clone https://github.com/leanprover/lean-eval.git .submission-work/lean-eval
git -C .submission-work/lean-eval checkout 6b4b87b672f5301f24983a12fda65dac608453ce
python formal/scripts/prepare_lean_eval.py --benchmark-dir .submission-work/lean-eval --output-dir .submission-work/source --source-rev 3264ad6acafa64ada18a309f48350d9acfd261ef --benchmark-rev 6b4b87b672f5301f24983a12fda65dac608453ce
```

在提交工作区按官方固定版本安装依赖和检查器后，运行：

```text
lake update
lake build Solution
lake test
```

## 已验证与官方待验收结果

- **固定 Lean 4.33.0 / Mathlib 环境下，完整 `lake build Solution` 通过（9,120 个 Lake 构建任务）。**
- 提交桥接和官方最终定理的传递公理审计均通过：

```text
'Submission.chen_theorem' depends on axioms: [propext, Classical.choice, Quot.sound]
'chen_theorem' depends on axioms: [propext, Classical.choice, Quot.sound]
```

- 原项目 Lean 4.32.2 下全部 9,571 个声明的审计仍有效；记录见 [STATUS.md](STATUS.md)。
- 429 个生成文件的复现比对通过，包含七处兼容性修改；可信文件与固定 Git blobs 的 SHA-256 一致。
- 官方识别脚本恰好识别一个 `chen_theorem` 提交，可信文件与补丁哈希检查通过。
- 大小写敏感导入检查通过；提交只依赖固定 Mathlib 及其正常传递依赖。
- 最终提交归档为 **1,024,230 字节**，低于 10 MiB。
- 修复版已提交为 #1696。**官方 comparator / nanoda 验收结果待返回**，以自动验证链接为准；本地构建通过不等于已获官方接受。

官方 `Challenge.lean` 保留题目模板自带的占位证明，它不是提交证明的依赖。
上述公理审计检查的是 `Submission.chen_theorem` 和官方 `Solution` 的实际证明。

## 迁移记录

首次提交 [#1695](https://github.com/leanprover/lean-eval-submissions/issues/1695)
通过格式检查和归档，但未通过固定版本编译，未进入 nanoda 重放。
官方日志报告 Fourier、Mertens、ShiftedLemma5 的兼容问题。

本地完整迁移共调整七个模块，均保留定理陈述及数学假设：显式使用
`Circle.norm_coe`；删除新版 `simp` 后多余的两处 `rfl`；直接通过
`Finset.mem_filter` 和 `Finset.mem_image` 提取成员条件；更新旧的
`setOf Nat.Prime` 写法；为新版指数积分引理显式证明指数 `1` 为正。
全部修改记录在 `scripts/lean_eval_compat.json`，并随评测源码以
`COMPATIBILITY.json` 发布。

Windows 默认并发曾导致内存分配失败，最终成功构建使用进程环境变量
`LEAN_NUM_THREADS=4`。原项目证明文件未作迁移修改。

修复版表单原文保存在 [lean-eval-resubmission.md](lean-eval-resubmission.md)，
首次表单保存在 [lean-eval-submission.md](lean-eval-submission.md)。

来源：[提交入口](https://lean-lang.org/eval/submit/)、
[API 与结果规则](https://github.com/leanprover/lean-eval-submissions)、
[验证器说明](https://github.com/leanprover/lean-eval/blob/main/SECURITY.md)。
