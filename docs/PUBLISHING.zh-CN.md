# 发布到 GitHub

## 1. 发布对象与尚需维护者决定的元数据

建议仓库名：`semidirect-qltc-t4`。建议描述：

```text
Semidirect qLTC manuscript: log-squared distance and soundness losses at constant rate and locality.
```

建议标签：`quantum-codes`、`qltc`、`css-codes`、`expander-graphs`、`lean4`、`reproducible-research`。首次版本标记为研究预发布 `v0.1.0-draft`，不要写成“完整 Lean 验证版”。

上传前由维护者确认作者/贡献者、公开范围及软件和文档许可。当前没有替你指定作者、机构、许可证或 DOI，详见 [RIGHTS](../RIGHTS.md)。需要作者引用元数据时，再基于实际信息添加 `CITATION.cff`；不要把占位姓名发布出去。

压缩包根目录已经是仓库根目录结构。上传时包含 `.github/`、`.gitignore` 等隐藏文件；不要再把整个项目嵌套进远端仓库的同名子目录。

## 2. 本地检查与提交

在解压后的 `semidirect-qltc-t4` 目录执行：

```bash
python scripts/verify.py
python scripts/manifest.py --check

git init -b main
git add .
git commit -m "Prepare t=4 qLTC research snapshot"
```

以上提交使用你本机已有 Git 身份；本包未创建假作者提交。若你在确认署名、许可证等信息后修改了文件，应先重新核对内容，再执行 `python scripts/manifest.py --write` 更新发布清单。

## 3. 创建远端并推送

安装并登录 GitHub CLI 后，以下命令会创建一个**公开**仓库并推送当前提交；确认内容适合公开后再执行：

```bash
gh auth status
gh repo create semidirect-qltc-t4 --public --source=. --remote=origin --push
```

只供内部审阅时把 `--public` 改成 `--private`。这是需要你主动执行的发布动作，本次整理没有执行它。已有远端仓库时，不运行创建命令，而是使用其实际地址配置 `origin` 并推送。

命令参数参考 [GitHub CLI 官方文档](https://cli.github.com/manual/gh_repo_create)。可在网页中新建空仓库后按该仓库显示的 Git 命令上传；不要让网页自动另建一个冲突的 README 或许可证。

## 4. 上传后确认与预发布

确认 README 数学公式及相对链接正常，检查 `.github/workflows/checks.yml` 的实际运行结果。该工作流只检查仓库与有限实验，不会运行 Lean；不要把它命名或宣传为完整定理验证。

在主分支检查通过、元数据与权限确认后，可建立标签并创建预发布：

```bash
git tag -a v0.1.0-draft -m "t=4 research manuscript and finite checks"
git push origin v0.1.0-draft
gh release create v0.1.0-draft --verify-tag --prerelease \
  --title "Improved qLTC parameter guarantees" --notes-file RELEASE_NOTES.md
```

这些命令是发布操作说明，不是已执行记录。无完整形式化证明时，应继续保留 [验证边界](VERIFICATION_STATUS.zh-CN.md) 和 [Lean 状态](../formalization/lean4/README.md)。
