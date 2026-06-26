## Formalization of type IV superorthogonality

This repository contains a formalization of the main result (Theorem 1) in the paper

P. T. Gressman, L. B. Pierce, J. Roos, and P.-L. Yung. [A new type of superorthogonality.](https://arxiv.org/abs/2212.08956) *Proc. Amer. Math. Soc.* 152, 665-675, 2024. 

### Statement of the main theorem

We restate the theorem below, formulated as closely as practical to the Lean implementation in [Defs.lean](https://github.com/roos-j/lean-superorthogonality/blob/c8c070fc1a2f0bf52246817c0c2e663f29a0c760/LeanSuperorthogonality/Defs.lean) and [MainTheorem.lean](https://github.com/roos-j/lean-superorthogonality/blob/c8c070fc1a2f0bf52246817c0c2e663f29a0c760/LeanSuperorthogonality/MainTheorem.lean).

Let $\iota$ be a set, $\alpha$ a measurable space and $\mu$ a measure on $\alpha$.

**Definition.** Let $r\in\mathbb{N}$. A $2r$-tuple $j=(j_i)_{0\le i<2r}$ is called [*all distinct*](https://github.com/roos-j/lean-superorthogonality/blob/c8c070fc1a2f0bf52246817c0c2e663f29a0c760/LeanSuperorthogonality/Defs.lean#L31-L32) if for every $i,i'$ with $i\not=i'$ we have $j_i\not= j_{i'}$.

**Definition.** Let $f=\{f_i\}_{i\in \iota}$ be a family of complex-valued functions and $r\in\mathbb{N}$. Then $(\mu, f, r)$ is called [*type IV superorthogonal*](https://github.com/roos-j/lean-superorthogonality/blob/c8c070fc1a2f0bf52246817c0c2e663f29a0c760/LeanSuperorthogonality/Defs.lean#L38-L42) if for every $i\in\iota$, $f_i$ is measurable and for every all distinct $2r$-tuple $j=(j_i)_{0\le i<2r}$, the function $x\mapsto f_0(x) \cdots f_{r-1}(x) \overline{f_r(x) \cdots f_{2r-1}(x)}$ is integrable, and
```math
\int f_0 \cdots f_{r-1} \overline{f_r \cdots f_{2r-1}}\,d\mu = 0.
```

[**Theorem 1.**](https://github.com/roos-j/lean-superorthogonality/blob/c8c070fc1a2f0bf52246817c0c2e663f29a0c760/LeanSuperorthogonality/MainTheorem.lean#L35-L41) Let $\iota$ be countable and $r\ge 1$ a natural number. Let $\{f_i\}_{i\in\iota}$ be a family of equivalence classes wrt. $\mu$ a.e.-equality of complex-valued functions with $f_i\in L^{2r}(d\mu)$. Let $(\mu,f,r)$ be type IV superorthgonal. Assume that for $\mu$-a.e. $x$, the sum $\sum_{i\in\iota} |f_i(x)|^2$ converges and that the square-function $x\mapsto \Big(\sum_{i\in\iota} |f_i(x)|^2\Big)^{1/2}$ is in $L^{2r}(d\mu)$.
Then the series $\sum_{i\in\iota} f_i$ converges unconditionally in $L^{2r}(d\mu)$ and we have
```math
\Big\|\sum_{i\in\iota} f_i\Big\|_{2r} \le C_r \Big\| \Big(\sum_{i\in\iota} |f_i|^2\Big)^{1/2} \Big\|_{2r},
```
where $C_1=1$ and $C_r = 2^{1/2} ((2r)! - 1)^{1/2}$ for $r\ge 2$.

### Implementation notes

There are some limitations on the extent to which the mathematically conventional formulation can match the actual Lean implementation, which must follow the rules of Lean's type theory.

* Mathematically, elements $f$ of $L^{2r}(d\mu)$ are equivalence classes of functions with respect to $\mu$-a.e. equality. Since the notions of type IV superorthogonality and square-functions are defined for functions rather than equivalence classes, one must pass to a representative of $f$. In Lean this is achieved by a type coercion, which is often implicit, similarly to mathematical convention.

* The two occurrences of $L^{2r}$ norms on both sides of the inequality use two different (mathematically equivalent) implementations of $L^p$ norms in Lean. On the left-hand side we use the norm on the normed space $L^{2r}(d\mu)$ which takes equivalence classes, and on the right-hand side we use the $L^{2r}$ norm of the square-function interpreted as a function. These choices are to some extent arbitrary and other formulations are possible.

* The Lean formulation of the theorem has the "additional" hypothesis that the `Fact` $1\le 2r$ holds as an inequality in $\mathbb{R}_{\ge 0\infty}$ (extended nonnegative reals). This redundancy is there to allow Lean to infer the topology of $L^{2r}(d\mu)$ by typeclass inference.
The typeclass inference system is powerful, but it does not automatically discover that this fact is a consequence of the hypothesis $r\ge 1$ in $\mathbb{N}$.

### Verification

To build and verify the formalization locally follow these steps:

* Install Lean 4 following instructions [here](https://lean-lang.org/install/).

* Clone this repository using

`git clone https://github.com/roos-j/lean-superorthogonal`

* Open the repository folder in VSCode, open a terminal and run
  
  `lake exe cache get!`

This is not strictly necessary, but will significantly speed up the build process by fetching pre-built dependencies such as Mathlib.

* Open the file `LeanSuperorthogonality.lean` in VSCode and move the cursor to the line
  
`#print axioms sqfct_estimate_of_type_iv_superorthogonal`

After some time, the Lean InfoView window should then display the message

```'Superorthogonal.sqfct_estimate_of_type_iv_superorthogonal' depends on axioms: [propext, Classical.choice, Quot.sound]```

This means that Lean has successfully certified correctness of the theorem.

Alternatively, run 
`lake build`
from the terminal in VSCode.

### Autoformalization

The bulk of the ~3k lines of code in this project was generated using Codex/gpt-5.5-xhigh. Specifically, the files in the [Codex folder](https://github.com/roos-j/lean-superorthogonality/tree/c8c070fc1a2f0bf52246817c0c2e663f29a0c760/LeanSuperorthogonality/Codex) contain the autoformalized proofs while the remaining files contain the basic definitions and main theorem statements, which were entirely human-generated.
