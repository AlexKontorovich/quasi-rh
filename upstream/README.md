# Vendored OpenAI proof components

## Source and local adaptation

`OAI/NumberTheory/DirichletL` began as the exact 286-module transitive import
closure of

```text
OAI.NumberTheory.DirichletL.RowCompletion.ZeroFreeRegion
```

from OpenAI's [`math` repository][source] at commit
`fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`. The clean closure contains
190,290 lines and 9,276,274 bytes. It supplies the concrete Eisenstein
arithmetic, both Poisson passages, Gauss--Jacobi conversion, cubic-theta
reflection, quadratic large sieve, Mellin continuation, and unconditional
reflection models reused here.

The committed OAI tree contains 287 Lean modules, 190,912 lines, and
9,304,027 bytes. Of the 286 upstream modules, 263 remain byte-for-byte
identical and 23 are locally modified. The additional module is
`CubicSieve/DescentScale.lean`. Each modified file carries a notice on its
first line.

The local change parameterizes the canonical descent step and reserve while
preserving OpenAI's historical fixed-scale interfaces. This removes the
hard-coded `1 / 20` reserve from the new mean-square entry point and permits
any positive reserve. The complete 24-file adaptation (23 modified files and
one added file) is archived in
[`openai-positive-descent.patch`](patches/openai-positive-descent.patch). It
is a patch against the OpenAI repository root, so its paths begin with
`lean/OAI/`. Its SHA-256 digest is

```text
714dfb93362515af706897384a11c99e20ae5b96775094b5b6c6927a97c5962e
```

The direct `11 / 12` proof lives under `ElevenTwelfths/`. It uses the new
arbitrary-positive-reserve mean square and the lower-level OpenAI components;
it neither invokes the packaged `ZeroFreeRegion` theorem nor obtains
`11 / 12` by weakening OpenAI's `7 / 8` result.

## Dependency compatibility patch

The build pins Rellich--Kondrachov commit
`70f85d4c1bf99c6e7d61e8be4daa6f3664d08d23` and uses OpenAI's Lean 4.34.1
compatibility patch
[`rellich-kondrachov-lean4341.patch`](patches/rellich-kondrachov-lean4341.patch).
Its SHA-256 digest is

```text
0c121d8517dfeadc93ef24fe2deb56beec7cb3998e2552dee8f61c780b1408c8
```

The idempotent hook in `lakefile.lean` validates the dependency origin and
revision, applies the patch before dependency resolution in a fresh checkout,
and verifies it again after a Lake update. Consequently `lake exe cache get`
can be the first build command; no unrecorded manual edit inside `.lake/` is
required.

## License

The upstream source is Apache-2.0 licensed. The upstream license is reproduced
in [`LICENSE`](LICENSE), and the repository-wide copy is at
[`../LICENSE`](../LICENSE). Dependencies retain their own licenses.

[source]: https://github.com/openai/math/tree/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/lean/OAI/NumberTheory/DirichletL
