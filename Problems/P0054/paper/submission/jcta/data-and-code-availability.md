# Data and code availability package

## 1. Ready-to-paste statement

This work is theoretical and does not generate or analyse empirical datasets.
The supporting artifact package contains the Lean 4 formalization, exact
search programs, construction verifiers, certificate generators, CNF
instances, DRAT proofs, verification scripts, manifests, checksums, tests,
and locked dependency metadata.  Source and release materials are available
at **[GITHUB_RELEASE_URL]**.  The immutable archive of release `v1.0.0` is
available from Zenodo at **[ZENODO_DOI_URL]**.

Do not paste this statement into a submitted manuscript until both identifiers
resolve publicly and the GitHub tag and Zenodo record refer to byte-identical
release assets.

## 2. Repository and identifier actions

1. Create a public GitHub repository for the curated artifact source.
2. Publish tag and release `v1.0.0` with the full review/artifact archive and
   its SHA-256 checksum as release assets.
3. Connect the repository to Zenodo or upload the same release files directly.
4. Reserve the Zenodo DOI if final typesetting still needs the identifier, and
   publish the record only after its metadata and files have been checked.
5. Add the GitHub release URL and Zenodo DOI URL to `manuscript.tex` and the
   ordinary English manuscript.
6. Confirm that the public archive includes the license, citation metadata,
   software/environment versions, verification entry points, and the nine
   archived CNF/DRAT pairs listed by the release manifest.
7. Recompute the final asset checksum after any package change; never reuse a
   checksum from a superseded archive.

## 3. Chinese author check

- 数据类型：本文不产生经验数据；公开对象是证明、代码、形式化文件和证书工件。
- 公开位置：GitHub 用于可浏览源码与版本发布，Zenodo 用于不可变归档和 DOI。
- 当前缺项：公开 GitHub 发布地址、Zenodo DOI，以及二者与最终工件字节一致性的
  复核。
- 隐私边界：电话只在期刊私有投稿系统填写，不进入 GitHub、Zenodo 或论文正文。
