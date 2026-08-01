# Data and code availability package

## 1. Draft statement — blocked until the revision DOI exists

This work is theoretical and does not generate or analyse empirical datasets.
The supporting artifact package contains the Lean 4 formalization, exact
search programs, construction verifiers, certificate generators, CNF
instances, DRAT proofs, verification scripts, manifests, checksums, tests,
and locked dependency metadata.  The current public baseline is [GitHub release
`v1.0.0`](https://github.com/lailai0916/saturated-sperner-6-7/releases/tag/v1.0.0).
Its immutable Zenodo archive has DOI
[`10.5281/zenodo.21679078`](https://doi.org/10.5281/zenodo.21679078).

Both identifiers were public and resolving when last checked, but they predate
the present revision.  Publish GitHub release `v1.1.0` and a new Zenodo version,
then replace this baseline paragraph with the resolving revision URL and
version DOI before submission.  Do not modify v1.0.0 in place.

## 2. Repository and identifier actions

1. Build and verify a revision-synchronized artifact from the final source
   snapshot.
2. Publish GitHub release `v1.1.0` and create a new version of the existing
   Zenodo record.
3. Confirm that the public archive includes the license, citation metadata,
   software/environment versions, verification entry points, and the nine
   archived CNF/DRAT pairs listed by the release manifest.
4. Update the manuscript, Supplement, submission metadata, and this file only
   after the new release URL and version DOI resolve; keep the Zenodo concept
   DOI relationship intact.
5. Recompute the final asset checksum after any package change; never reuse a
   checksum from a superseded archive.

## 3. Chinese author check

- 数据类型：本文不产生经验数据；公开对象是证明、代码、形式化文件和证书工件。
- 公开位置：GitHub 用于可浏览源码与版本发布，Zenodo 用于不可变归档和 DOI。
- 当前状态：GitHub `v1.0.0` 与 Zenodo DOI 已公开，但早于本次修订。投稿前必须
  发布 `v1.1.0` 和新的 Zenodo 版本，并回填新版本 DOI。
- 隐私边界：电话只在期刊私有投稿系统填写，不进入 GitHub、Zenodo 或论文正文。
