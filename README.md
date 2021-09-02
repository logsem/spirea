# Iris NVM

## Overview of the development

* [`lang`](src/lang) - The definition of the language.
  * [`lang/syntax.v`](src/lang/syntax.v) - Syntax of the language.
  * [`lang/memory.v`](src/lang/memory.v) - Semantics of the memory subsystem.
  * [`lang/lang.v`](src/lang/lang.v) - Semantics of the language.
* [`algebra`](src/algebra) - Resource algebras.
  * [`algebra/view.v`](src/algebra/view.v) - The resource algebra of views. Used
    pervasively.
* [`base`](src/base) - The base program logic. The instantiation of the Iris and
  Perennial program logic, the base post crash modality, etc.
  * [`base/adequacy.v`](src/base/adequacy.v) - The adequacy result for the recovery weakest
    precondition of the base logic.
  * [`base/primitive_laws.v`](src/base/primitive_laws.v) - Contains, among other things, the state
    interpretation used in the base logic.
* [`high`](src/high) - The high-level logic. The definition of `dprop`, `wp`, etc.
  * [`high/resources`](src/high/resources) - Contains some of the resource algebras/CAMERAs used in
    the high-level logic.
* [`extra`.v](src/extra.v) - Auxiliary definitions and lemmas that are not
  specific to the logic.

## Development

### Updating dependencies

The dependencies are included as git submodules.

The following git command updates all the dependencies:
```
git submodule update --recursive --remote --merge
```

