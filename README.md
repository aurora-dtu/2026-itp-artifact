# Securing the foundations of an intermediate language for probabilistic program verification – Artifact

_This is the artifact for ITP'26 submission #138._

This artifact contains the Lean project of the formalization of the submitted paper. The paper contains hyperlinks to the source files to ease comparison and navigation between the paper and the formalization.

## Accessing formalization

One can access the generated documentation anonymously online at https://anonymous.4open.science/w/2026-itp-artifact-641A/doc/, or locally by navigating to `doc/` and starting a local server (for example with `cd doc && python3 -m http.server` and then visiting http://localhost:8000).

Refer to [`Paper.lean`](https://anonymous.4open.science/w/2026-itp-artifact-641A/doc/Paper.html) for an overview linking all definitions, theorems, and lemmas from the paper to their respective Lean formulation.

## Interacting with formalization

We recommend setting up Lean using [the official guide](https://lean-lang.org/install/). The project was tested and built using the following toolchain:

```
❯ elan --version && lake --version && lean --version
elan 4.1.2 (58e8d545e 2025-05-26)
Lake version 5.0.0-src+7e01a1b (Lean version 4.28.0)
Lean (version 4.28.0, arm64-apple-darwin24.6.0, commit 7e01a1bf5c70fc6167d49c345d3bf80596e9a79b, Release)
```

Once setup, open the project in your editor and access the files. The initial setup might take a while as Mathlib takes some time to download and cache.


If you wish to build from the command line follow the steps below:

```
❯ lake exe cache get
❯ lake build
```
