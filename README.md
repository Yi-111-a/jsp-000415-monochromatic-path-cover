# jsp-000415-monochromatic-path-cover

## English

- **JSP id:** JSP-000415
- **Title:** Can every edge-colored complete graph have its vertices covered by few paths whose edges all share one color?
- **Catalog:** https://github.com/TheJustinSunPrize/awards/blob/main/problems/catalog-0401-0500.md#JSP-000415
- **Status:** WIP / PARTIAL — harness may be green on intermediate lemmas, but the **full catalog statement is not yet formalized**.
- **Prize claim:** **NOT claiming** the Justin Sun Prize yet.
- **Owner:** [Yi-111-a](https://github.com/Yi-111-a) (public Lean repo for a future claim must be owned by this account).

### Prize rules reminder

Only a **complete** Lean formalization of the **original** catalog problem is eligible.
Partial mathematics or incomplete Lean (`sorry`/`admit`, unproved assumptions) is not eligible.
Do not put Lean sources into `TheJustinSunPrize/awards`; catalog PRs should link out only.
Pin a full 40-character commit SHA when claiming later.

### Build

```bash
curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh
cd lean
lake build
```

See `lean/lean-toolchain` for the pinned toolchain. See `ACCEPTANCE.md` for the prize gate and required headline theorem name(s).

### Verification

```bash
scripts/harness.sh   # lake build + sorry/admit count + #print axioms → HARNESS_LOG.md
scripts/status.sh    # structured status output
```

## 中文

- **题目编号：** JSP-000415
- **标题：** 任意边染色完全图的顶点集能否被同色单色路径覆盖？
- **目录条目：** https://github.com/TheJustinSunPrize/awards/blob/main/problems/catalog-0401-0500.md#JSP-000415
- **状态：** 进行中 / **部分结果** — harness 在中间引理上可能已通过，但**完整原题陈述尚未形式化**。
- **领奖：** **尚未**就 Justin Sun Prize 提出 claim。
- **仓库所有者：** Yi-111-a（未来 claim 的公开 Lean 仓库必须由该账号拥有）。

### 规则提醒

仅接受对**原题完整陈述**的**完整** Lean 形式化；部分数学或含 `sorry`/`admit` 的不完整形式化不具备资格。
不要把 Lean 源码放进 awards 仓库；目录 PR 只放链接。claim 时需钉死完整 40 位 commit SHA。

### 构建

```bash
curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh
cd lean
lake build
```
