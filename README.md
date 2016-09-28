Formalization of Nominal Adapton's Lambda Calculus in Agda
----------------------------------------------------------

### What is this
This will be a formalization of Nominal Adapton's lambda calculus (as depicted in section 4 of the OOPSLA'15 paper *Incremental Computation with Names* by Hammer et al.) in Agda. The end goal will be to formalize the proof of from-scratch consistency, as given in the paper's appendix.

### What's done
1. The original Adapton's lambda calculus is mostly encoded.
2. Part of the common big-step operational semantics is encoded.
3. Started on type checking procedure.

### To do
1. All of the nominal stuff (and its new type system)
2. Finish encoding big-step operational semantics (try both relational and functional).
3. Finish type checking.
4. Prove type soundness.
5. Work on from-scratch consistency proof.

### Module contents
1. AdaptonExamples
 - Examples of Adapton programs.
2. Type
 - Defines Adapton's types and operations on them.
3. Term
 - Defines untyped terms, terminal values, and operations on them.
4. TypedTerm
 - Defines well-typed terms in Curry style and Church style (in submodule Church).
5. Evaluation
 - Encoding of big-step operational semantics.

### Sources used
1. Sandro Stucki. *system-f-agda*. https://github.com/sstucki/system-f-agda
2. Ulf Norell and James Chapman. *Dependently Typed Programming in Agda*. http://www.cse.chalmers.se/~ulfn/papers/afp08/tutorial.pdf
3. Hammer et al. *Adapton*. http://arxiv.org/pdf/1503.07792v5.pdf
4. Hammer et al. *Nominal Adapton*. http://www.cs.umd.edu/~hammer/adapton/adapton-pldi2014.pdf
5. Paul Levy. *A tutorial on call-by-push-value*. http://cs.ioc.ee/efftt/levy-slides.pdf
6. Fransesco Mazzoli. *Agda by Example: lambda-calculus*. http://mazzo.li/posts/Lambda.html
7. Jan Malakhovski. *Brutal [Meta]Introduction to Dependent Types in Agda*. http://oxij.org/note/BrutalDepTypes/
