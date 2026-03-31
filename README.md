# Isabelle Big Integer

This fork of Mihai Spinei's [original repository](https://github.com/mspinei/IsabelleBigInteger), which includes contributions by Peter Lammich and Mihai Spinei, aims to add change of basis to the big numbers to enable its use in [Pastèque](https://m-fleury.github.io/pasteque/) since big numbers need to be printable in a base 10 representation.

## Running 

> **_NOTE_**: Isabelle/LLVM project linked as git submodule. To clone and make a project local Isabelle/LLVM copy:
```shell
git clone --recursive <repo_link>
```

> Run with (this will build Isabelle/LLVM):

```shell
isabelle jedit -d . -l Isabelle_LLVM src/BigInt.thy
```
> **_NOTE_**: To use another (pre-built) Isabelle_LLVM repo, modify path inside `ROOTS`.

##
