# free-proving-code

A library to model effectful programs and prove properties about these programs in Coq.

# Setup

We run the code using Coq version 8.9 (but it should also work with 8.8). Use the respective `_CoqProject` in order to compile all the files.

```
> pwd
/home/free-proving-code
> coq_makefile -f _CoqProject -o Makefile
> make
```

# "Verifying Effectful Haskell Programs in Coq"

The Coq sources `src/Seq.v`, `src/StrictFields`, and `src/State.v` are the case studies associated with the most recent publication [Verifying Effectful Haskell Programs in Coq](https://www-ps.informatik.uni-kiel.de/~sad/haskell2019-preprint.pdf).

# "A Monad to Prove Them All"

The accompanying code for the publication [One Monad to Prove Them All](https://arxiv.org/abs/1805.08059) can be found on the [corresponding branch](https://github.com/ichistmeinname/free-proving-code/tree/oneMonadToProveThemAll). The described case study about queues is located in `src/Queue.v`.
