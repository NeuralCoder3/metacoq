# Parametricity Variants

This folder is conceptually the same a translation
and should be a subfolder there.
It was moved into its own metacoq-subfolder in order
to show all work of this project.

Tests are showcased in test/

| File | Content |
| ---- | ------- |
| debug             | Commands to debug MetaCoq terms and programs |
| de_bruijn_print   | Pretty prints MetaCoq terms with parenthesis and explicit tRel numbers |
| makeFresh         | Postprocesses terms and inductive definitions to guarantee fresh names |
| translation_utils | General translation interface for terms and types. Copied from translations and changed to generate fresh names |
| param_unary       | Unary parametricity translation with pruning and  |
| param_exists      | ∃∃ translation of types |
| --- | --- |
| Notation | TODO |
| param_other | TODO |

Extensive comments are in the files.
For the ideas behind ∀∀, ∀∃, ∃∀ and ∃∃, one can look at this [note](https://nightly.link/NeuralCoder3/container/workflows/main/main/PDF.zip).