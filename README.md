<!---
This file was generated from `meta.yml`, please do not edit manually.
Follow the instructions on https://github.com/coq-community/templates to regenerate.
--->
# copland-manifest-tools

[![Docker CI][docker-action-shield]][docker-action-link]

[docker-action-shield]: https://github.com/ku-sldg/copland-manifest-tools/actions/workflows/docker-action.yml/badge.svg?branch=main
[docker-action-link]: https://github.com/ku-sldg/copland-manifest-tools/actions/workflows/docker-action.yml




This library provides definitions and tools for working with Copland manifests in Rocq. It includes utilities for validating, generating, and manipulating manifests, as well as providing a framework for building and extending manifest-related functionality.

## Meta

- Author(s):
  - Will Thomas
- License: [Creative Commons Attribution Share Alike 4.0 International](LICENSE)
- Compatible Coq versions: 8.20 later
- Compatible OCaml versions: 4.12 or later
- Additional dependencies:
  - [RocqCandy](https://github.com/ku-sldg/rocq-candy)
  - [CoplandSpec](https://github.com/ku-sldg/copland-spec)
  - [CLITools](https://github.com/ku-sldg/rocq-cli-tools)
  - [EasyBakeCakeML](https://github.com/durbatuluk1701/EasyBakeCakeML)
  - [Dune](https://dune.build) 3.17 or later
- Related publication(s): none

## Building and installation instructions

The easiest way to install the latest released version of copland-manifest-tools
is via [OPAM](https://opam.ocaml.org/doc/Install.html):

```shell
opam repo add -a --set-default ku-sldg/opam-repo https://github.com/ku-sldg/opam-repo.git
opam repo add coq-released https://coq.inria.fr/opam/released
opam install rocq-copland-manifest-tools
```

To instead build and install manually, do:

``` shell
git clone https://github.com/ku-sldg/copland-manifest-tools.git
cd copland-manifest-tools
dune build
dune install
```



