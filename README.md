Something is slowly growing here. It is still fragile so better not disturb it, but you may take a look if you'd like.

<img src="logo.svg" alt="logo" width="650"/>


**What is this?** Agda Core is, as its name suggests, intended to be a core language for Agda.

**Why make a core language for Agda?** Because people whose opinion I value were asking for it. Also, implementing a new language from scratch is fun, so there's that.

**How is it implemented?** Agda Core is implemented in Agda, naturally. It consists of a well-scoped syntax, an environment-based evaluator, a formal definition of the typing and conversion rules, and a derivation-producing type checker.

**What can I use it for?** First of all, you can appreciate the beauty of the typing rules. Secondly, we plan to link Agda Core to the main Agda system as a backend, so you can double-check its results. Finally, this project is also intended to serve as a demonstration of how to implement a correct-by-construction type checker for dependent types.


## Build instructions

### 1. Determine your Agda application directory

Run the following command and note the output location:

```bash
AGDA_DIR=$(agda --print-agda-app-dir)
```


### 2. Install and register required libraries
#### Install agda2hs

agda2hs is available on Hackage:
```bash
cabal install agda2hs
agda2hs locate >> "$AGDA_DIR/libraries"
```

This registers the agda2hs library with Agda.

#### Install scope

Choose any directory where you want to clone repositories, then run:

```bash
git clone https://github.com/jespercockx/scope.git
cd scope
realpath scope.agda-lib >> "$AGDA_DIR/libraries"
```

This registers the scope library with Agda.

#### 3. Build agda-core

Clone this repository (if you haven’t already), then in the repository root run:

```bash
make
cabal build
```

#### 4. Typecheck Agda files using agda-core

Invoke the custom Agda frontend like this:
```bash
cabal run exe:agda-core -- FILE.agda
```
Replace `FILE.agda` with the file you want to typecheck.
