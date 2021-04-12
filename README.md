# Iris NVM

* [lang](src/lang) - The definition of the language.
  * [lang/syntax.v](src/lang/syntax.v) - Syntax of the language.
  * [lang/memory.v](src/lang/memory.v) - Semantics of the memory subsystem.
  * [lang/lang.v](src/lang/lang.v) - Semantics of the language.
* [base](src/base) - The base program logic. The instantiation of the Iris and
  Perennial program logic, the base post crash modality, etc.
* [high](src/high) - The high-level logic. The definition of `dprop`, `wp`, etc.
* [extra.v](src/extra.v) - Definitions and lemmas that are not specific to the logic.
