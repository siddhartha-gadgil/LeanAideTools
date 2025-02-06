# LeanAideTools

The goal of this repository is to facilitate the use of [LeanAide](https://github.com/siddhartha-gadgil/LeanAide) in developing Lean Projects:

* This is a **zero-dependency**, small project to minimize issues of toolchain and dependency compatibilities.
* This provides the Syntax and other integrations to serve as a *client* for LeanAide in its server-client mode.
* Some tools are directly provided in this project.

## Use in your project

To add LeanAideTools as a dependency, add the following line to your `lakefile.toml` file:

```toml
[[require]]
name = "LeanAideTools"
git = "https://github.com/siddhartha-gadgil/LeanAideTools.git"
rev = "main"
```

If you use a `lakefile.lean` file, you can add the following line to the file:

```lean
require LeanAideTools from git "https://github.com/siddhartha-gadgil/LeanAideTools"@"main"
```

Then run `lake update LeanAideTools` to use LeanAideTools/LeanAide in your project.

## Client for LeanAide Syntax

Please see the README of the [LeanAide](https://github.com/siddhartha-gadgil/LeanAide) repository for instructions on setting up the LeanAide server. 

Once the server has started (and you have LeanAide as a dependency) you can use LeanAide. The most convenient way to use LeanAide is with syntax we provide that gives code-actions. We have syntax for translating theorems and definitions from natural language to Lean, and for adding documentation strings to theorems and definitions. For example, the following code in a Lean file (with correct dependencies) will give code actions:

```lean
import LeanAideTools
import Mathlib

#theorem "There are infinitely many odd numbers"

#def "A number is defined to be cube-free if it is not divisible by the cube of a prime number"

#doc
theorem InfiniteOddNumbers : {n  ∣  Odd n}.Infinite := by sorry
```

We also provide syntax for generating/completing proofs. For now this is slow and not of good quality. Experiments and feedback are welcome. The first of the examples below uses a command and the second uses a tactic. 

```lean
#prove "The product of two successive natural numbers is even"

theorem eg₁ (n: Nat) : 2 ∣ n * (n + 1) := by
  #prove
```

## Running tactics automatically

While proving results in tactic mode in Lean, proofs can often be completed by tactics like `simp`, `exact?`, `aesop` etc., but it is a nuisance to try this at each step. We provide a tactic mode where a list of tactics is run automatically **in the background** after each step. 

If a proof can be completed, then:

* A hyperlink in the infoview and a code action is offered to replace the code by a valid proof.
* The `sorry` tactic is run to complete the proof, so the user sees a warning (this is to avoid showing an error, following a suggestion by Bolton Bailey).

To work with this mode, follow the below installation instructions, including adding `import LeanAideTools` to your file. You can enter the auto-tactic mode by:

* Beginning a tactic block with `byy` instead of `by`.
* At any stage, starting a sequence of tactics with `doo`.

The `doo` syntax is provided as, at present, the mode does not see within `case`, `match`, bullet points etc., so one has to use it to re-enter the auto-tactic mode in these cases.

The tactics that run by default are `rfl`, `simp?`, `omega`, `aesop?`, `exact?`. More tactics can be added as long as they are in scope. For example, in a Mathlib dependent project (or a branch of Mathlib) one may
want to add `linarith` and `ring`. One can add either a single tactic or multiple tactics as in the following.

```lean
#auto ring
#autos [ring, linarith]
```

## Examples in action

Here are some examples illustrating the tactic mode.

### Simple Example

In the following simple example, the result can be proved straight away. The syntax `byy` by itself is valid and tries to prove the goal.

![Simple Example](https://github.com/siddhartha-gadgil/LeanAideTools/blob/v4.7.0/assets/lat1.gif)

### Checks after each tactic

In the following (rather contrived) example, the result cannot be proved automatically. However, once the tactic `rw [silly]` is entered the proof is completed and results are suggested.

![Checks after each tactic](https://github.com/siddhartha-gadgil/LeanAideTools/blob/v4.7.0/assets/lat2.gif)

### Background Running

The following shows that the tactics are running in the background. After the tactics to run are spawned, there is a configurable delay, 50 milliseconds by default, before control is returned to the user. The tactics continue running in the background till they finish after this delay.

Here the delay is set to `0`. Hence after `rw [silly]` the proof is not automatically completed. Every time the interpreter is triggered we check whether the proof was found by the background processes. In this case, hitting enter triggered the interpreter which found that the proof was found in the background.

![Background Running](https://github.com/siddhartha-gadgil/LeanAideTools/blob/v4.7.0/assets/lat3.gif)

### Configuration: Adding tactics

The following illustrates adding tactics. Here `simp [silly]` is added. In the presence of this tactic the example can be proved straight away.

![Adding Tactics](https://github.com/siddhartha-gadgil/LeanAideTools/blob/v4.7.0/assets/lat1.gif)


## Installation

Add the following or equivalent to your `lakefile.lean` to use the auto-tactic mode. The branch/tag `v4.7.0` works with the corresponding version of Lean's toolchain. Replace it with the toolchain you use in your project. I will try to have a branch/tag for each toolchain starting with `v4.7.0-rc2`.

```lean
require LeanAideTools from git
  "https://github.com/siddhartha-gadgil/LeanAideTools.git" @ "v4.7.0"
```

For use with a `Mathlib` branch, add the dependency in the lakefile while working on the branch and remove it before the PR is merged.

To use the mode in a file, add `import LeanAideTools` along with your other imports.

## Missing features?

There are two features that I hope to work on eventually:

* When a tactic like `exact?` finds a proof, the user gets a hyperlink and code-action to complete the proof with this tactic. But this tactic in turn gives a suggested proof with which it can be replaced. The two steps should ideally be replaced by just one.

* The tactic mode does not see within `case`, `match`, bullet points etc. This is a limitation of the current implementation. The `doo` syntax is provided to re-enter the auto-tactic mode in these cases, but ideally one should not have to do this.

Any comments, suggestions, or bug reports are welcome. Also contributions are welcome.
