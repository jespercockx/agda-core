Something is slowly growing here. It is still fragile so better not disturb it, but you may take a look if you'd like.

**What is this?** Agda Core is, as its name suggests, intended to be a core language for Agda.

**Why make a core language for Agda?** Because people whose opinion I value were asking for it. Also, implementing a new language from scratch is fun, so there's that.

**How is it implemented?** Agda Core is implemented in Agda, naturally. It consists of a well-scoped syntax, an environment-based evaluator, a formal definition of the typing and conversion rules, and a derivation-producing type checker.

**What can I use it for?** First of all, you can appreciate the beauty of the typing rules. Secondly, we plan to link Agda Core to the main Agda system as a backend, so you can double-check its results. Finally, this project is also intended to serve as a demonstration of how to implement a correct-by-construction type checker for dependent types.
