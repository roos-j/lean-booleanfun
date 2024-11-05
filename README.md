Analysis of Boolean functions in Lean
================

This is a project formalizing some basic definitions and results in the analysis of Boolean functions using [Lean 4](https://leanprover-community.github.io/), largely following the book [Analysis of Boolean functions](https://arxiv.org/abs/2105.10386) by Ryan O'Donnell.

Main results formalized so far:

* Plancherel's theorem for the Walsh-Fourier transform
* L² Poincaré inequality
* Blum-Luby-Rubinfeld linearity testing
* a version of Arrow's theorem

Installation
-------------

1. Install Lean 4 and dependencies as explained [here](https://leanprover-community.github.io/get_started.html).

2. Clone this repository using

        git clone https://github.com/roos-j/lean-booleanfun.git

and open it in VS Code (more instructions [here](https://leanprover-community.github.io/install/project.html)).

Future goals
-------------
* hypercontractivity, Bonami lemma
* KKL theorem
* Bobkov's two-point inequality
* Talagrand's isoperimetric theorem
* FKN theorem

Note: the central limit theorem will be needed eventually; currently not in Mathlib

Todo
-------------
* add doc-gen4
* streamline proofs

Previous formalizations of Arrow's theorem
-------------

Arrow's theorem has been formalized before (and in more general formulations):

* in Mizar [by Freek Wiedijk](https://link.springer.com/article/10.1007/s12046-009-0005-1)
* in Isabelle/HOL [by Tobias Nipkow](https://link.springer.com/article/10.1007/s10817-009-9147-4)
* in Lean [by Andrew Souther, Benjamin Davidson](https://github.com/asouther4/lean-social-choice)

These formalizations use direct [combinatorial arguments of John Geanakoplos](https://link.springer.com/article/10.1007/s00199-004-0556-7).

The formalization in this project uses [Gil Kalai's Fourier-analytic approach](https://www.sciencedirect.com/science/article/pii/S0196885802000234) as in Sec. 2.5 of [Ryan O'Donnell's book](https://arxiv.org/abs/2105.10386). 
