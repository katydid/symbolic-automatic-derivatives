# ReProving Agda in Lean

This project translates the paper ([Symbolic and Automatic Differentiation of Languages - Conal Elliott](http://conal.net/papers/language-derivatives)) from Agda to LeanProver.

The goals of this project are to:

  - Discover the differences between Agda and Lean4.
  - Define proofs on `Type` instead of `Prop`, since each proof represents a different parse of the language.
  - Avoid tactics if possible, in favour of simple `trfl` (our version of `rfl`).

## Links

  * The original paper: [Symbolic and Automatic Differentiation of Languages - Conal Elliott](http://conal.net/papers/language-derivatives)
  * If you are interested in [collaborating with Conal Elliott](https://github.com/conal/Collaboration)
  * Want to read the Agda code with the ability to "Go to Definition", but you do not want to install Agda. Then download the zip file in this gist: [Generated HTML from the original Agda code](https://gist.github.com/awalterschulze/aecd70ccb5448f17992913ccde359a2e).
  * We [streamed](https://www.twitch.tv/awalterschulze) the development the foundations of this repo. You can find the recordings in this [Youtube Playlist](https://www.youtube.com/watch?v=OoKNpfUNpfU&list=PLYwF9EIrl42Qr52nnmeuSXp47S79sB3W0).

## Requirements

This project requires setting up lean, see the [official documentation](https://lean-lang.org/lean4/doc/quickstart.html).

## Differences from the Agda implementation

### Equality `≡`

Lean has `Prop` and `Type` and Agda has `Set`, which we can think of as `Type` in Lean. We want out proofs to be proof revelant, since each proof represents a different parse of our language. This means the theorems have to be defined on `Type`. For example we have equality redefined in terms of `Type` as `TEq` (using the syntax `≡`) and  we replace `rfl` with `trfl`, but we do not a replacement tactic for `rfl`.

```
inductive TEq.{tu} {α: Type tu} (a b: α) : Type tu where
  | mk : a = b -> TEq a b

def trfl {α : Type u} {a : α} : TEq a a := TEq.mk rfl
```

We needed to redefine the following types and functions to use `Type` instead of `Prop`:

| Description  | Prop  | Type  |
| :---         | :---: | :---: |
| equality     | `=`   | `≡` in [Tipe.lean](./Sadol/Tipe.lean)  |
| equivalance  | `Mathlib.Logic.Equiv.Defs.Equiv`  | `TEquiv` or `<=>` in [Function.lean](./Sadol/Function.lean) |
| decidability | `Decidable`  | `Decidability.Dec` in [Decidability.lean](./Sadol/Decidability.lean) |

### Simply renamings

Some things we renamed since they are simply called different things in Agda and Lean, while others were renamed to be closer to the Lean convention.

| Description  | Original Agda | Translated Lean |
| :---         | :---:         | :---:           |
|              | `Set`         | `Type`          |
| universe levels  | `ℓ`, `b`  | `u`, `v`        |
| parametric types | `A`, `B`  | `α`, `β`        |
| isomorphism      | `↔`       | `<=>`           |
| extensional isomorphism | `⟷` | `∀ {w: List α}, (P w) <=> (Q w)` |

### Namespaces / Qualified Imports

We use namespaces as much as possible to make dependencies clear to the reader without requiring "Go to Definition" and Lean to be installed.

| Description        | Original Agda | Translated Lean   |
| :---               | :---:         | :---:             |
| `List α -> Type u` | `◇.Lang`      | `Language.Lang`   |
| `List α -> β`      | `◇.ν`         | `Calculus.null`   |
| `(List α -> β) -> (a: α) -> (List α -> β)` | `◇.δ`     | `Calculus.derive` |
|                    | `Dec`         | `Decidability.Dec`     |
|                    | `Decidable`   | `Decidability.DecPred` |

### Syntax

We dropped most of the syntax, in favour of `([a-z]|[A-Z]|'|?|\.)*` names.

| Description  | Original Agda | Translated Lean |
| :---         | :---:         | :---:           |
| nullable     | `ν`           | `null`          |
| derivative of a string  | `𝒟` | `derives`      |
| derivative of a character    | `δ`  | `derive` |
|              | `∅`           | `emptyset`      |
|              | `𝒰`           | `universal`     |
| empty string | `𝟏`           | `emptystr`      |
| character    | ` c           | `char c`        |
|              | `∪`           | `or`            |
|              | `∩`           | `and`           |
| scalar       | `s · P`       | `scalar s P`    |
|              | `P ⋆ Q`       | `concat P Q`    |
| zero or more | `P ☆`        | `star P`        |
| decidable bottom  | `⊥?`     | `Decidability.empty?` |
| decidable top     | `⊤‽`     | `Decidability.unit?`  |
| decidable sum     | `_⊎‽_`   | `Decidability.sum?`   |
| decidable prod    | `_×‽_`   | `Decidability.prod?`   |
| `Dec α -> Dec (List α)` | `_✶‽` | `Decidability.list?` |
| `(β <=> α) -> Dec α -> Dec β` | `◃` | `Decidability.apply'` |
| decidable equality   | `_≟_`  | `Decidability.decEq` |
| decidable denotation | `⟦_⟧‽` | `denote? |
| denotation           | `⟦_⟧`  | `denote` |

All language operators defined in `Language.lagda` are referenced in other modules as `◇.∅`, while in Lean they are references as qualified and non notational names `Language.emptyset`. The exception is `Calculus.lean`, where `Language.lean` is opened, so they are not qualified.

### Explicit parameters.

We use explicit parameters and almost no module level parameters, for example `Lang` in Agda is defined as `Lang α` in Lean. In Agda the `A` parameter for `Lang` is lifted to the module level, but in this translation we make it explicit.

## Thank you

Thank you to the [Conal Elliot](http://conal.net/) for the idea of comparing LeanProver to Agda using the paper [Symbolic and Automatic Differentiation of Languages - Conal Elliott](http://conal.net/papers/language-derivatives).

Thank you to the Authors and Advisors:

  * [Paul Cadman](https://www.linkedin.com/in/paul-cadman/)
  * [Jan Mas Rovira](https://janmasrovira.gitlab.io/ascetic-slug/)
  * [Gregor Feierabend](https://www.linkedin.com/in/gregorfeierabend/)
  * [Keegan Perry](https://github.com/keeganperry7)
  * [Brink van der Merwe](https://abvdm.pages.cs.sun.ac.za/)
