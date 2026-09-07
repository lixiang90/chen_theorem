# LeanEval 陈定理提交

提交日期：2026-09-07。

- 官方提交：[lean-eval-submissions #1695](https://github.com/leanprover/lean-eval-submissions/issues/1695)
- 自动验证：[run 34127446780](https://github.com/leanprover/lean-eval-submissions/actions/runs/34127446780)
- 评测源码：[固定提交 a8d8292](https://github.com/lixiang90/chen_theorem/tree/a8d8292ba85931a416c44bc2a9be295b65966fda)
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

## 已验证与待返回的结果

- 原项目全部 9,571 个声明的公理审计通过；完整记录见 [STATUS.md](STATUS.md)。
- 使用官方精确定义的题目桥接已在原工具链中通过类型检查，仅依赖三个标准公理。
- 官方源码识别脚本恰好识别一个 `chen_theorem` 提交。
- 可信文件与固定 benchmark Git blobs 的 SHA-256 一致。
- 用固定 Git revisions 重新打包的 428 个文件经比对，证明、题目和许可证文本一致，来源元数据及所有 SHA-256 一致。
- Linux 大小写敏感的本地导入检查通过；提交只依赖固定 Mathlib 及其正常传递依赖。
- 提交归档为 1,022,756 字节，低于 10 MiB。
- 官方提交格式检查、源码归档已成功；comparator/nanoda 验收正在运行。
- 本地 Lean 4.33.0 依赖缓存仍在下载，尚未将完整版本迁移检查记为通过。

只有官方结果返回成功，才能将本提交标为 LeanEval 接受。
提交表单原文保存在 [lean-eval-submission.md](lean-eval-submission.md)。

来源：[提交入口](https://lean-lang.org/eval/submit/)、
[API 与结果规则](https://github.com/leanprover/lean-eval-submissions)、
[验证器说明](https://github.com/leanprover/lean-eval/blob/main/SECURITY.md)。
