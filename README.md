# Spirea

## Overview of the development

* [`lang`](src/lang) - The definition of the language.
  * [`lang/syntax.v`](src/lang/syntax.v) - Syntax of the language.
  * [`lang/memory.v`](src/lang/memory.v) - Semantics of the memory subsystem.
  * [`lang/lang.v`](src/lang/lang.v) - Semantics of the language.
* [`algebra`](src/algebra) - Resource algebras.
  * [`algebra/view.v`](src/algebra/view.v) - The resource algebra of views. Used
    pervasively.
* [`base`](src/base) - The low-level program logic. The instantiation of the Iris and
  Perennial program logic, the base post crash modality, etc.
  * [`base/adequacy.v`](src/base/adequacy.v) - The adequacy result for the recovery weakest
    precondition of the base logic.
  * [`base/primitive_laws.v`](src/base/primitive_laws.v) - Contains, among other things, the state
    interpretation used in the base logic.
* [`high`](src/high) - The high-level logic. The definition of `dprop`, `wp`, etc.
  * [`high/dprop.v`](src/high/dprop.v) - Defines the domain of propositions _dProp_.
  * [`high/resources`](src/high/resources) - Contains some of the resource algebras/CAMERAs used in
  * [`high/recovery_weakestpre.v`](src/high/recovery_weakestpre.v) - The
    definition of the recovery weakest precondition in the high-level logic as
    well as the proof of the idempotence rule.
  * [`high/weakestpre_na.v`](src/high/weakestpre_na.v) - WP lemmas about
    _non-atomic_ location.
  * [`high/weakestpre_at.v`](src/high/weakestpre_at.v) - WP lemmas about
    _atomic_ location.
* [`extra`.v](src/extra.v) - Auxiliary definitions and lemmas that are not
  specific to the logic.
* [`examples`](src/examples) - Contains examples.

## Development

### Clone

The project uses submodules. So to clone it and the associated submodules use
the following command:

```
git submodule update --init --recursive
```

### Updating dependencies

The dependencies are included as git submodules.

The following git command updates all the dependencies (the option `--recursive
` may be necessary as well but it seems to not be the case):

```
git submodule update --remote --merge
```

