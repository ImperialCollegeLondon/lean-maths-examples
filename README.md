# Undergraduate mathematics questions, in Lean

A lot of people say to me "I've done the natural number game,
what next?". One answer to that question is "if you want
to explore further, install Lean 3 and the community tools
by following the instructions on [the community website](...)"
*put URL here*. But then what?

In some sense, what happens next depends on your interests.
There are other browser games available, such as [list lean
games here], written by various people. There are also Lean
projects which, once you have Lean instaled, you can download
onto your computer by typing

```
leanproject get <full-name-of-project>
```

For example you can download the official community tutorial,
suitable for beginners, by typing `...` *put command*. This
will teach you how to do some basic analysis in Lean. Alternatively
you can download the complex number game repo [here](...) *put URL*
by typing `...` *put command* and learn about how one can use
structures to make new mathematical objects such as \C in Lean.

## This repository.

This repository is not one coherent product like the projects
mentioned above. It is
a collection of short one-file projects, the goal of each of which
is to prove some results in undergraduate-level mathematics.
Each project is in its own directory in `src`, for example
a project playing with the basic axioms of group theory
is at `src/group-axioms-project`. Each of these directories
contains four files. There's a `questions.lean` file contains
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
