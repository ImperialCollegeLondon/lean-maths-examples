# Undergraduate mathematics questions, in Lean

A lot of people say to me "I've done the natural number game,
what next?". One answer to that question is "if you want
to explore further, install Lean 3 and the community tools
by following the instructions on [the community website](https://leanprover-community.github.io/get_started.html).
But then what?

In some sense, what happens next depends on your interests.
There are other browser games available, such as [list lean
games here], written by various people. There are also Lean
projects which, once you have Lean instaled, you can download
onto your computer by typing things like

```
leanproject get tutorials
```

if you want to get the official community tutorials project
(which will teach you how to do some analysis in Lean),
or

```
leanproject get ImperialCollegeLondon/complex-number-game
```

which will get you the complex number game repo, or

```
leanproject get ImperialCollegeLondon/lean-maths-examples 
```

which will get you this repository.

## This repository.

This repository is a collection of short one-file projects
the goal of each of which is to prove one or more results in
undergraduate-level mathematics, for example that the limit
of the product of two real-valued sequences is the product
of the limits.

Each project is in its own directory in `src`, for example
a short project playing with the basic axioms of group theory
will eventually appear at `src/group-axioms`. Each of these directories
contains three files. There's a `questions.lean` file contains
a basic introduction, approximate difficulty level, and all
the questions with `sorry`d proofs. There's a `HINTS.md` file with
hints on which tactics and theorems will be useful to solve
the questions, and finally there's a `solutions.lean` file with
full solutions. 

The projects are completely independent of each other, and
range in difficulty from quite easy to quite hard. Some of these
projects have been developed by Kevin Buzzard and tested on his
undergraduate students. I am quite open to PRs which add other
projects; please make sure they follow the same pattern of
a questions file, a solutions file, and a hints file.
