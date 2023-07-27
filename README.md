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

## Correspondence to OOPSLA 23 paper

The rules in Figure 5.

| Rule                      | Coq                                                                   |
|---------------------------|-----------------------------------------------------------------------|
| lb-knowledge              | `store_lb_persistent`, `flush_lb_persistent`, `persist_lb_persistent` |
| lb-persistent-flush-store | `persist_lb_to_flush_lb` and `flush_lb_to_store_lb`                   |
| obj-noflush-nobuffer      | `buffer_free_objective` and `flush_free_objective`                    |
| mapsto-store-lb           | `mapsto_na_store_lb` and `mapsto_at_store_lb`                         |
| mapsto-lb-pers            | `mapsto_na_persist_lb`                                                |
| mapsto-na-store-lb        | `mapsto_na_store_lb_incl`                                             |
| post-fence-no-flush       | `post_fence_no_flush`                                                 |
| pfs-pf                    | `post_fenc_sync_post_fence`                                           |
| rec-in-if-rec             | `crashed_in_if_rec`                                                   |
| PC-na-mapsto              | `post_crash_mapsto_na`                                                |
| PC-at-mapsto              | `post_crash_mapsto_at`                                                |
| PC-invariant              | `post_crash_know_protocol`                                            |
| PC-PCF                    | `post_crash_flush_post_crash`                                         |
| PC-persist-lb             | `post_crash_persist_lb`                                               |
| PCF-flush-lb              | `post_crash_flush_flush_lb`                                           |
| rec-in-agree              | `crashed_in_agree`                                                    |

The rules in Figure 6.

| Rule          | Coq                                  |
|---------------|--------------------------------------|
| Ht-flush      | `wp_flush_lb`                        |
| Ht-fence-sync | `wp_fence_sync`                      |
| Ht-fence      | `wp_fence` and `wp_fence_prop`       |
| Ht-na-alloc   | `wp_alloc_na`                        |
| Ht-at-alloc   | `wp_alloc_at`                        |
| Ht-na-read    | `wp_load_na`                         |
| Ht-na-write   | `wp_store_na`                        |
| Ht-at-read    | `wp_load_at` and `wp_load_at_simple` |
| Ht-at-write   | `wp_store_at`                        |

## Development

The `main` branch is currently developed using Coq version 8.17.1.

### Clone

The project uses submodules. To clone it and the associated submodules use the
following command:

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

