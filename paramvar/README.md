# Parametricity Variants

This folder is conceptually the same a translation
and should be a subfolder there.
It was moved into its own metacoq-subfolder in order
to show all work of this project.

## Project goals

This folder is part of the project "Parametricity translations and subterm relations for nested inductive types".

The goal of this project was to take a look at the unary parametricity translation and understand it deeply to reimplement it in MetaCoq.
There is already a MetaCoq implementation of the parametricity translation
but the old one uses multiplications in de Bruijn terms and needs a complicated
manual management of translation tables.

The new translation automated much of the manual labor and uses a environment
functions to replace liftings and de Bruijn multiplications.

Another part of the project is to find a dual principle of the unary parametricity translation on inductive types.
The parametricity translation is a relation on objects and for container
types coincides with a statement expressing that predicates are fulfilled for all elements in the container type. We call such a statement the ∀∀ statement of a type.

Analogously to the ∀∀ statement an ∃∃ statement can be formulated expressing 
that at least one predicate is fulfilled on at least one element.
This predicate has an application in nested subterm relations.
To complete the predicates, one can also think about ∀∃ and ∃∀.

For the ideas behind ∀∀, ∀∃, ∃∀ and ∃∃, one can look at this [note](https://nightly.link/NeuralCoder3/container/workflows/main/main/PDF.zip).

All four statements were developed, defined and implemented as a plugin using MetaCoq.

## Future work

* extend ∃∃ to fixpoints
* research possible extension of ∃∃ to terms
* extend ∀∃ and ∃∀ to handle complex type patterns
* handle universe error for nested and guarded containers in ∃∃
* a more general code base for all translations
* research universe error for nested containers in ∀∀
* implement nested subterm relations

## Compilation

ocaml-variants.4.09.1+flambda is needed with Coq coq-metacoq 1.0~beta1+8.12,
coq 8.12.0, coq-equations 1.2.3+8.12.

Please follow the instructions under [https://acp_20.discourse.ps.uni-saarland.de/t/coq-installation/18](https://acp_20.discourse.ps.uni-saarland.de/t/coq-installation/18).
The additional libraries like smpl, quickchick and vst are not needed.

Run `./configure local` followed by `make` and `make checker`
in metacoq/.
Then execute make inside the paramvar directory.

## Demo file

The demo file is located in `showcase.v`.

## Documentation

An online documentation containing the comments for all files
can be found under [https://neuralcoder3.github.io/metacoq/toc.html](https://neuralcoder3.github.io/metacoq/toc.html).

## Files

| File | Content |
| ---- | ------- |
| showcase | shows the feature of the translations |
| | |
| debug             | Commands to debug MetaCoq terms and programs |
| de_bruijn_print   | Pretty prints MetaCoq terms with parenthesis and explicit tRel numbers |
| makeFresh         | Postprocesses terms and inductive definitions to guarantee fresh names |
| translation_utils | General translation interface for terms and types. Copied from translations and changed to generate fresh names |
| param_unary       | Unary parametricity translation with pruning and  |
| param_exists      | ∃∃ translation of types |
| param_other | ∀∃ and ∃∀ translations |
| param_all | combined commands, user interface and notations |
| | |
| param_eq | connection between lifting and environments |
| param_comp | compares legacy unary parametricity and new version |
| param_exists_test | tests for ∃∃ |
| param_other_test | tests for ∀∃ and ∃∀ |
| param_test | tests for ∀∀ |

## Code

The code is available on [github](https://github.com/NeuralCoder3/metacoq/tree/unary-param/paramvar).

## Comments and explanation

Extensive comments are in the files.

