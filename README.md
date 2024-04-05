# LeanAideTools

This repository is intended to contain useful tools while minimizing dependencies to allow use with/**without** mathlib and also while developing (a branch of) mathlib. I hope to also have a branch/tag for each lean toolchain version.

At present, there is a single tool, for running tactics automatically in the background to try to complete proofs.

## Running tactics automatically

### Simple Example

![Simple Example](https://github.com/siddhartha-gadgil/LeanAideTools/blob/v4.7.0/assets/lat1.gif)

### Checks after each tactic

![Checks after each tactic](https://github.com/siddhartha-gadgil/LeanAideTools/blob/v4.7.0/assets/lat2.gif)

### Background Running

![Background Running](https://github.com/siddhartha-gadgil/LeanAideTools/blob/v4.7.0/assets/lat3.gif)

### Configuration: Adding tactics

![Adding Tactics](https://github.com/siddhartha-gadgil/LeanAideTools/blob/v4.7.0/assets/lat1.gif)


## Installation

Add the following or equivalent to your `lakefile.lean` to use the auto-tactic mode. The branch/tag `v4.7.0` works with the corresponding version of Lean's toolchain. Replace it with the toolchain you use in your project. I will try to have a branch/tag for each toolchain starting with `v4.7.0-rc2`.

```lean
require LeanAideTools from git
  "https://github.com/siddhartha-gadgil/LeanAideTools.git" @ "v4.7.0"
```

For use with a `Mathlib` branch, add the dependency in the lakefile while working on the branch and remove it before the PR is merged.

To use the mode in a file, add `import LeanAideTools` along with your other imports.

