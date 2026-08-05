# The Nandakumar–Ramana Rao theorem in Lean

This repository contains a Lean 4 formalization of the theorem proved by
**Arseniy Akopyan, Sergey Avvakumov, and Roman Karasev** [1].

## The Theorem

Any convex body in the plane can be partitioned into `m` convex parts of equal area
and equal perimeter, for every integer `m ≥ 2`.

In the formal statement, a convex body is a compact convex subset of the plane with nonempty
interior. Area is two-dimensional Lebesgue measure, and perimeter is the one-dimensional
Hausdorff measure of the boundary.

The public Lean statement and its proof are in
[`HumanVerification/Main.lean`](HumanVerification/Main.lean):

```lean
theorem HumanVerification.equalAreaEqualPerimeterPartition
```

## Background

The problem was posed by **R. Nandakumar and N. Ramana Rao** in
*Fair partitions of polygons: An elementary introduction* [2]. They asked whether every planar
convex body admits such a partition into an arbitrary prescribed number of convex parts.

The case of three parts was established by **Imre Bárány, Pavle V. M. Blagojević, and András
Szűcs** [3]. Topological methods later proved the conjecture when the number of parts is a prime
power [4, 5]. A related result on simultaneous convex fair partitions of \(d\) measures in \(\mathbb{R}^d\) was proved in [6].

The full result for an arbitrary number of parts was proved by **Arseniy Akopyan, Sergey
Avvakumov, and Roman Karasev** [1]. A preprint appeared in 2018, and the final paper was
published in *Advances in Mathematics* in 2026.

- **Published article:** [Convex fair partitions into an arbitrary number of pieces — *Advances in Mathematics*](https://www.sciencedirect.com/science/article/pii/S0001870826001490)
- **DOI:** [10.1016/j.aim.2026.110927](https://doi.org/10.1016/j.aim.2026.110927)
- **arXiv:** [arXiv:1804.03057](https://arxiv.org/abs/1804.03057)

## Repository structure

- [`NRR/`](NRR/) contains the formal proof of the equal-area, equal-perimeter partition theorem.
- [`HumanVerification/Main.lean`](HumanVerification/Main.lean) gives the public geometric
  formulation and proves it from the formal development in `NRR/`.

## Verification

The project is pinned to the Lean and Mathlib versions recorded in `lean-toolchain` and
`lake-manifest.json`.

From the repository root, run:

```bash
./scripts/verify.sh
```

Equivalently, the main checks are:

```bash
lake build
python3 scripts/check_dependencies.py
lake env lean HumanVerification/Main.lean
lake env lean HumanVerification/Check.lean
python3 scripts/audit_project.py
```

`HumanVerification/Check.lean` also verifies by definitional equality that the public plane,
area, perimeter, and partition predicate use the intended Mathlib definitions. The dependency
check confirms that Mathlib comes from the official repository, is at the exact commit recorded
in `lake-manifest.json`, and has no local modifications.

Lean reports that the main theorem depends only on the standard foundational axioms used by
Mathlib: `propext`, `Classical.choice`, and `Quot.sound`. The project contains no `sorry`, `admit`,
project-specific `axiom`, `unsafe`, or `implemented_by` declarations.

The formalization was developed and prepared for verification with assistance from
**Aristotle** and **ChatGPT**. The resulting proof term is checked independently by the Lean
kernel.

## References

1. Arseniy Akopyan, Sergey Avvakumov, and Roman Karasev,
   [*Convex fair partitions into an arbitrary number of pieces*](https://www.sciencedirect.com/science/article/pii/S0001870826001490),
   *Advances in Mathematics* **493** (2026), Article 110927.
   [arXiv:1804.03057](https://arxiv.org/abs/1804.03057)

2. R. Nandakumar and N. Ramana Rao,
   [*Fair partitions of polygons: An elementary introduction*](https://link.springer.com/article/10.1007/s12044-012-0076-5),
   *Proceedings of the Indian Academy of Sciences — Mathematical Sciences* **122** (2012),
   459–467. [arXiv:0812.2241](https://arxiv.org/abs/0812.2241)

3. Imre Bárány, Pavle V. M. Blagojević, and András Szűcs,
   [*Equipartitioning by a convex 3-fan*](https://www.sciencedirect.com/science/article/pii/S000187080900262X),
   *Advances in Mathematics* **223** (2010), 579–593.
   [DOI: 10.1016/j.aim.2009.08.016](https://doi.org/10.1016/j.aim.2009.08.016)

4. Pavle V. M. Blagojević and Günter M. Ziegler,
   [*Convex equipartitions via equivariant obstruction theory*](https://arxiv.org/abs/1202.5504),
   *Israel Journal of Mathematics* **200** (2014), 49–77.
   [Published article](https://link.springer.com/article/10.1007/s11856-014-1006-6)

5. Roman Karasev, Alfredo Hubard, and Boris Aronov,
   [*Convex equipartitions: The spicy chicken theorem*](https://arxiv.org/abs/1306.2741),
   *Geometriae Dedicata* **170** (2014), 263–279.

6. Pablo Soberón,
   [*Balanced convex partitions of measures in* $\mathbb{R}^d$](https://www.cambridge.org/core/journals/mathematika/article/abs/balanced-convex-partitions-of-measures-in-d/980CC476E4C821C0C5158560C8C1A347),
   *Mathematika* **58** (2012), no. 1, 71–76.
   [DOI: 10.1112/S0025579311001914](https://doi.org/10.1112/S0025579311001914) ·
   [arXiv:1010.6191](https://arxiv.org/abs/1010.6191)

## Software

- [Lean 4](https://lean-lang.org/)
- [Mathlib](https://leanprover-community.github.io/)
