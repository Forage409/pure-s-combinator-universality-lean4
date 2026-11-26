# Computational Universality, Finite Tree Algebras, and Asymptotic Phase Transitions of the Pure $S$ Combinator

**Wolfram $S$ Combinator Challenge Submission**

## Abstract

Schönfinkel's combinator $S$, defined by $S x y z \to_S (x z)(y z)$, generates an orthogonal, non-erasing subsystem $\mathrm{CL}(S)$ of combinatory logic in which weak and strong normalization coincide and form a regular tree language (Waldmann, 2000). Because normal-form reachability is decidable in linear time, universal computation in $\mathrm{CL}(S)$ requires sub-universal encoding, halting detection, and output decoding along non-terminating reductions (Wolfram, 2021).

We show that universality in $\mathrm{CL}(S)$ depends sharply on evaluation-order control. Under a stateless, root-restarted finite-state tree-walking selector, closed $S$-terms simulate arbitrary Turing machines via Neary and Woods's $U_{3,11}$ with initial tree size $O((|Q|^2 + |w|)^2)$, a minimal $11$-state bottom-up halting tree automaton, and linear-time output recovery; a program-free selector starting from a $10$-leaf seed simulates cyclic tag systems without an embedded universal table. Conversely, root-restarted selection is already universal over $\mathsf{Leaf} \to \mathsf{Node}(\mathsf{Leaf},\mathsf{Leaf})$, whereas unrestricted reduction admits constant-step halting shortcuts and forbids asymmetric branch gating.

For unguided rewriting, we construct conversion-invariant finite $S$-algebras of $35$ states for head normalization, $39$ states each for strong normalization and Böhm-tree productivity, and $36$ states separating unsolvable convertibility classes, resolving Questions 5, 7, 10, 30 (on normalizing terms), and 31 of Barendregt, Endrullis, Klop, and Waldmann (2017). Singularity analysis yields an exact rational density $4429673/7077888 \approx 0.62585$ of head-normalizing $S$-terms, whereas normalizing and productive $S$-terms decay exponentially. All results are constructively formalized in Lean 4 and cross-checked in Wolfram Language.

*2020 Mathematics Subject Classification:* Primary 03B40, 68Q05; Secondary 68Q42, 05A16, 68V20  
*Keywords:* combinatory logic, $S$ combinator, universal Turing machine, cyclic tag system, tree-walking automaton, tree automaton, Böhm tree, productivity, analytic combinatorics, constructive formalization

---

## 1. Introduction

### 1.1. Historical Context and the Pure $S$ Problem

In a lecture delivered to the Göttingen Mathematical Society on December 7, 1920 and published in 1924, Moses Schönfinkel showed that bound variables can be eliminated from mathematical logic by reducing all operations to binary application and two primitive combinators: the cancellation operator $K$ (written $C$ by Schönfinkel), satisfying $K x y \to x$, and the fusion operator $S$, satisfying $S x y z \to (x z)(y z)$ [53]. Together with Haskell Curry's axiomatization [18, 19], the system $\mathrm{CL}(S,K)$ became one of the standard foundations of computability theory, matching the expressive power of Church's untyped $\lambda$-calculus and Turing machines [60, 1, 35].

In $\mathrm{CL}(S,K)$, computational universality relies simultaneously on duplication by $S$ and erasure by $K$. Restricting the basis to $S$ alone yields the subsystem $\mathrm{CL}(S)$, whose closed (or ground) terms $\mathcal{T}_S$ are finite full binary application trees with every leaf labeled $S$, rewritten under the contextual closure of

$$
S X Y Z \;\to_S\; (X Z)(Y Z). \tag{1.1}
$$

Because every argument $X, Y, Z$ reappears on the right-hand side of (1.1), the leaf count $|M|$ never decreases under reduction: $|(X Z)(Y Z)| - |S X Y Z| = |Z| - 1 \ge 0$. By Church's conservation principle for orthogonal non-erasing rewrite systems, weak normalization ($\mathrm{WN}$) and strong normalization ($\mathrm{SN}$) coincide on $\mathrm{CL}(S)$ [75, 4]. For five decades after Schönfinkel's lecture, it was not even clear whether every closed $S$-term normalizes. That question was settled in the negative in the mid-1970s through Barendregt's $9$-leaf term $A A A$ (where $A \equiv S S S$), Duboué's two minimal $7$-leaf non-normalizing terms $X_1 \equiv S(S S)S S S S$ and $X_2 \equiv S S S(S S)S S$ [2, 1], and Zachos's $10$-leaf single-redex term $Z_{\mathrm{Zac}} \equiv S T T(S T T)$ (where $T \equiv S S$) [75].

Two decades later, Johannes Waldmann proved through an algebraic analysis of pure-$S$ rewriting that the set $\mathcal{T}_S \cap \mathrm{SN}$ of normalizing closed $S$-terms is a regular tree language, recognizable in linear time $O(|M|)$ by a finite tree automaton [62, 63, 64, 65] whose minimal deterministic bottom-up realization has $39$ states ($38$ accepting states and one absorbing sink) [24, 4]; see also Cheilaris, Ramirez, and Zachos [15] for a manual grammar derivation, and Barendregt, Dekkers, and Statman [3] for broader typed and combinatory decision boundaries. Waldmann's theorem immediately rules out direct normal-form universality in the classical sense of Davis [22]: if halting of a universal machine $U$ on input $w$ were encoded as normal-form reachability $\mathcal{E}(w) \in \mathrm{WN}$, any computable encoder $\mathcal{E}$ would compose with the $39$-state tree automaton to decide the halting problem.

Yet normalizing reductions represent an exponentially vanishing fraction of $\mathrm{CL}(S)$ dynamics [7], and non-normalizing $S$-terms display intricate growth and tree-unfolding behavior [71]. On June 8, 2021, commemorating the centenary of Schönfinkel's lecture [69, 71], Stephen Wolfram posed *The Wolfram $S$ Combinator Challenge*, asking whether $\mathrm{CL}(S)$ can support universal computation along non-terminating evolutions [70]. Following the ongoing-computation framework established by Priese [50] and employed in the universality proofs for elementary cellular automaton Rule 110 by Cook [17] and for the $(2,3)$ Turing machine prize by Smith [55, 68], Wolfram formulated ongoing pure-$S$ computation via an encoder $\mathcal{E}$, a halting detector $\mathcal{H}$, and an output decoder $\mathcal{D}$, each required to operate within strict sub-universal resource bounds so that no universal simulation occurs outside $\mathrm{CL}(S)$ itself [70, 61]. Wolfram also emphasized that once reductions do not terminate in a unique normal form, confluence no longer collapses distinct evaluation orders: the answer may depend on whether one considers fixed canonical strategies (such as normal-order reduction $\to_{\mathrm{lo}}$), unrestricted multiway conversion $=_S$, or a specified single-step selection discipline.

### 1.2. Computation Regimes and Summary of Main Results

The central thesis of this monograph is that the computational power of $\mathrm{CL}(S)$ admits an exact classification governed by the locus of evaluation-order control. Rather than treating “universality of $S$” as an undifferentiated yes-or-no predicate, we analyze all five candidate operational regimes posed in [70, 4] within a single mathematical and mechanized framework. Table 1 summarizes the resulting taxonomy.

**Table 1.** Taxonomy of computational regimes and decidability boundaries in $\mathrm{CL}(S)$.

| Regime | Step relation | Halting / event problem | Expressive / algebraic law | Reference |
| :— | :— | :— | :— | :— |
| Normal-form halting | $M \to_S^* N \in \mathrm{NF}$ | Regular ($39$-state $\mathcal{A}_{\mathrm{SN}}$) | Subcritical ($\gamma_{\mathrm{SN}} \approx 3.36992$) | Thms. 6.2, 8.4 |
| Canonical fixed order | $\to_h, \to_{\mathrm{lo}}, \to_{\mathrm{li}}$ | $\mathrm{HN}$ ($35$), $\mathrm{Prod}$ ($39$) regular | Super-pushdown; monotone clones | Thms. 6.6, 6.12, 7.3 |
| Unrestricted multiway | $M \to_S^* N$, $M =_S N$ | $\to_S^*$ decidable; $=_S$ on $\mathrm{SN}$ | $7$/$5$-step shortcuts; no branch gate | Prop. 5.4, Thm. 5.5 |
| Root-restarted walker | $T_{k+1} = \sigma_{\mathrm{TM}}(T_k)$ | $\Sigma_1^0$-complete ($11$-state $\mathcal{H}_{11}$) | $O((\vert Q\vert ^2+\vert w\vert )^2)$ size; sep. by $\to_{\mathrm{sp}}$ | Thms. 3.9, 5.2 |
| Program-free walker | $T_{k+1} = \sigma_{\mathrm{CTS}}(T_k)$ | $\Sigma_1^0$-complete ($11$-state $\mathcal{H}_{11}$) | No UTM table; genesis from $D_{\mathrm{seed}}$ | Prop. 4.4, Thm. 4.5 |

Our contributions span four interconnected directions.

Sections 3 and 4 establish compact, polynomial-size universal simulations in $\mathrm{CL}(S)$ under stateless root-restarted finite-state selection. In an instructive recent development, Filin [26] demonstrated selected-path universality of $\mathrm{CL}(S)$ under a root-restarted finite controller by compiling Boolean-tape Turing machines through three-counter and $2$-tag systems [16, 42] to Rogozhin's $(4,6)$ universal Turing machine [51] and Cook's $912$-phase cyclic tag system [17]; because unary counter encoding incurs iterated exponential blowup, every source instance in that padded pipeline produces at least $8^{19069} = 2^{57207}$ seed bits before $114$-fold tag expansion, and source output recovery requires an $O(|T|^4)$ parser consulting the retained seed. In Section 3, we bypass tag systems altogether by compiling boundary-safe normalized binary Turing machines directly to Neary and Woods's quadratic-time $3$-state, $11$-symbol universal machine $U_{3,11}$ [44, 43] and its $132$-state, $262$-rule binary specialization $U_{\mathrm{bin}}$. Theorem 3.9 establishes that the resulting pure-$S$ compiler $\mathcal{E}_{\mathrm{TM}}(M,w)$ produces a closed $S$-term of quartic leaf size $|T_0| \le 125{,}000\,N(M,w)^2$ with $N(M,w) = 225|Q|^2 + 390|Q| + 4|w| + 173$, reducing the compiled size of a $1$-state machine from at least $2^{57207}$ seed bits to $1{,}996{,}921$ leaves; moreover, every macro-step of the zipper tree-walking selector $\sigma_{\mathrm{TM}}$ terminates in at most $3500(2|t|-1)$ cursor micro-ticks with no state retained between contractions, halting is recognized by a provably minimal $11$-state deterministic bottom-up tree automaton $\mathcal{H}_{11}$ (Proposition 3.8), and the bare halted term decodes to the exact output word $\operatorname{out}_M(w)$ in linear time $O(|T_k|)$. In Section 4, we remove the embedded universal transition table from the selector itself: Theorem 4.5 constructs a program-free selector $\sigma_{\mathrm{CTS}}$ over self-describing pure-$S$ cyclic-tag encodings $\mathcal{E}_{\mathrm{CTS}}(P,w)$ of quadratic leaf size at most $2500(\|(P,w)\|+1)^2$, recognized at halting by the identical $11$-state automaton $\mathcal{H}_{11}$, and Proposition 4.4 proves that every instance $\mathcal{E}_{\mathrm{CTS}}(P,w)$ is reachable via pure-$S$ reduction from a single fixed $10$-leaf combinator $D_{\mathrm{seed}} \equiv S(S(S S))(S(S S))(S S)S$.

Section 5 characterizes why external redex selection is indispensable to Theorems 3.9 and 4.5, sharpening the automata-theoretic perspective of Bojańczyk and Colcombet [12] and Kutrib and Meyer's deterministic tree-walking-storage automata [39, 40]. Theorem 5.2 proves a controller-complexity separation: a fixed root-restarted finite-state tree-walking selector coupled with a $3$-state bottom-up halting tree automaton is already Turing-complete over unlabeled binary trees governed solely by the unary leaf-splitting rule $\mathsf{Leaf} \to_{\mathrm{sp}} \mathsf{Node}(\mathsf{Leaf},\mathsf{Leaf})$, which performs neither subtree duplication nor arity-$3$ interaction. Within controlled rewriting, the distinctive contribution of $S$ is therefore in-tree subtree duplication, which powers the program-free self-description and $10$-leaf seed genesis of Section 4. Conversely, once the external selector is removed in favor of unrestricted pure-$S$ reduction $\to_S^*$, Proposition 5.4 exhibits explicit $7$-step and $5$-step multiway reductions that trigger spurious halting on arbitrary non-terminating payloads in both protected-frame counter hubs and tag-dispatcher encodings, while Theorem 5.5 proves unconditionally that no closed $S$-term can realize asymmetric Church-boolean branch gating.

Sections 6 and 7 develop the intrinsic decidability and expressiveness theory of unguided $\mathrm{CL}(S)$ rewriting, resolving five open questions from Chapter 5 (*“Dance of the Starlings”*) of Barendregt, Endrullis, Klop, and Waldmann [4]. Constructing explicit integer head-step potentials $(A,B)$ that eliminate König's lemma, we prove completeness of the $35$-state head-normalization $S$-algebra $\mathcal{A}_{\mathrm{HN}}$ and linear-time decidability of root normal forms, resolving Question 10 and Footnote 4 of [4] (Theorem 6.6), alongside a constructive global potential proof of Waldmann's top-termination theorem and the absence of Berarducci mute $S$-terms [9, 8] (Theorem 6.7). Building on left and right $\bot$-propagation laws and universal right-application $\bot$-absorption for the Zachos family $G_m G_n$, we synthesize a minimal $39$-state conversion-invariant $S$-algebra $\mathcal{A}_P$ deciding Böhm-tree productivity in linear time, resolving Question 5 of [4] in the affirmative (Theorem 6.12). We further construct an explicit infinite refinement alternation sequence $F_0 \sqsubseteq F_1 \sqsubseteq \cdots$ resolving Question 7, separate $A A A \neq_S A A A S$ via a $36$-state refinement $\mathcal{A}_{36}$ of $\mathcal{A}_{\mathrm{HN}}$ despite identical clocked Böhm trees $\bot$ to resolve Question 31 in the negative, and establish decidability of $=_S$ on closed normalizing terms toward Dana Scott's Question 30 [54]. For fixed deterministic strategies, we prove coincidence of six canonical strategies on single-redex terms, non-semilinear quadratic trace languages on $Z_{\mathrm{Zac}}$, a sharp ceiling of $5$ consecutive innermost right-branch contractions, and a Post-lattice dichotomy showing that $\mathcal{A}_{\mathrm{HN}}, \mathcal{A}_{\mathrm{SN}}, \mathcal{A}_P$ are confined to monotone clones [48] whereas a $4$-state conversion-invariant $S$-algebra $\mathcal{D}_4$ realizes an $11$-leaf normal-form combinator computing cellular automaton Rule 110 (Theorem 7.3).

Finally, Section 8 classifies all $14$ empirical pure-$S$ benchmarks highlighted in Wolfram's challenge announcement [70], establishes sharp Catalan small-term minimality thresholds across leaf sizes $1 \le |M| \le 11$, and applies Flajolet–Sedgewick singularity analysis [28] to the polynomial generating-function systems of $\mathcal{A}_{\mathrm{HN}}$, $\mathcal{A}_{\mathrm{SN}}$, and $\mathcal{A}_P$, advancing the quantitative combinatory logic program of Bendkowski, Grygiel, and Zaionc [7]. Because the unsolvable sink $\infty_{\mathrm{HN}}$ is a left ideal ($q \odot \infty_{\mathrm{HN}}$ need not equal $\infty_{\mathrm{HN}}$, as witnessed by $S(A A A) \in \mathrm{HNF}$), Puiseux expansion at the Catalan singularity $z = 1/4$ yields the exact dyadic-ternary rational limiting density

$$
\lim_{n \to \infty} \frac{\#\mathrm{HN}(n)}{C_{n-1}} \;=\; \frac{4\,429\,673}{7\,077\,888} \;=\; \frac{4\,429\,673}{2^{18}\cdot 3^3} \;\approx\; 0.6258467215,
$$

whereas the two-sided context sinks of $\mathcal{A}_{\mathrm{SN}}$ and $\mathcal{A}_P$ push their dominant singularities strictly past $1/4$ to distinct degree-$35$ algebraic branch points $\rho_{\mathrm{SN}} > \rho_P > 1/4$, forcing exponential rarity of both normalizing and productive closed $S$-terms with certified all-$n$ upper bounds proportional to $(250/259)^n$.

### 1.3. Technical Overview and Proof Architecture

Five structural mechanisms underlie the proofs across Sections 2–8.

Protected spine-$2$ storage frames $F(a,b,j) \equiv S a(S b j)$, building on local opening identities of Filin [26], isolate reductions inside their left slot $a$ and right slot $b$ while sequestering historical junk $j$ without erasure: because $\operatorname{ls}(F(a,b,j)) = 2$, the term $F(a,b,j)$ has no root redex. Unopened leaves of the addressable memory layout are represented by phase-indexed counter generators $G(m,n) \equiv \nu_m \nu_n S$, which open deterministically in $6$ or $7$ contractions into $F(G(m',n'), G(m',n'), j')$ with non-frame intermediate stages and non-$\mathrm{S}_2$ junk $j'$. Wrapping an append-only chain of $11$-bit cell records along the right spine of $F$-frames allows the stateless zipper selector $\sigma_{\mathrm{TM}}$ to execute $U_{\mathrm{bin}}$ via a two-pass priority scan (completing any pending neighbor move before initiating a new active transition) while reading only $6$ local cursor observations and resetting all control state at each contraction.

In-tree self-description stands in sharp contrast to unguided multiway collapse. By encoding cyclic-tag appendant templates with $3$-bit versioned handshakes ($\mathsf{idle} \to \mathsf{armed} \to \mathsf{appending} \to \mathsf{idle}$) paired with staged queue allocation, the program-free selector $\sigma_{\mathrm{CTS}}$ copies arbitrarily long appendants onto the queue tail using pure-$S$ duplication alone, and every initial tree $\mathcal{E}_{\mathrm{CTS}}(P,w)$ unfolds directly from $D_{\mathrm{seed}}$ via a $5$-step bootstrap to $(\nu_1 S)\,G(2,2)$ followed by selective slot openings. Removing the selector destroys this discipline immediately: under unrestricted $\to_S^*$, any unopened halt-flag generator inside a protected hub opens in $7$ steps regardless of payload divergence, and any $D \cdot Q$ queue dispatcher contracts its live $1$-cell prematurely to a tombstone in $1$ step and executes the $0$-branch in $4$ further steps. More fundamentally, an inductive spine-grammar invariant ($\mathcal{W}_0$ and $\mathcal{O}$ in Section 5.3) shows that in any reduction of $M x_0 x_1 U_1 \cdots U_m$, every head $S$-redex capable of bringing $x_1$ into active function position must carry $x_0$ as one of its first two arguments, activating $x_0$ first.

Explicit algebraic potentials replace non-constructive appeals to König's lemma in finite $S$-algebra completeness proofs. For the $35$-state head-normalization algebra $\mathcal{A}_{\mathrm{HN}}$, we exhibit integer tables $A \colon Q_{\mathrm{HN}}^2 \to \{0,\dots,30\}$ and $B \colon Q_{\mathrm{HN}}^2 \to \{0,\dots,68\}$ whose spine sum decreases by at least $2$ across all $8{,}329$ active head-redex state triples outside $\infty_{\mathrm{HN}}$, constructively bounding head-reduction lengths on every solvable closed $S$-term.

Canonical productive values and critical-pair stratification resolve Question 5 on Böhm-tree productivity. On closed $S$-terms, left application preserves $\bot$ at the same Böhm depth while right application increases depth by at most $1$ because $\operatorname{ord}(M) \le 3$ prevents an argument from escaping a head spine without root consumption. Jointly analyzing $\mathcal{A}_P \times \mathcal{A}_{\mathrm{SN}}$ reveals that $34$ of the $38$ accepting states of $\mathcal{A}_P$ consist exclusively of strongly normalizing terms, three further states reduce to $\mathrm{HNF}$ without root contractions, and $(q_{29}, \infty_{\mathrm{SN}})$ is the unique non-normalizing productive root-redex fiber, populated by the Zachos family $G_m G_n$ whose right applications $(G_m G_n) U$ always collapse to $\bot$. A finite rank-$17$ stratification on $\mathcal{A}_P \times \mathcal{A}_{\mathrm{HN}}$ then constructively witnesses $\bot_d(M)$ whenever $\llbracket M \rrbracket_P = \infty_P$.

Strongly connected component (SCC) decomposition of tree-automaton dependency graphs combines with algebraic singularity analysis to govern the asymptotic densities of $\mathrm{CL}(S)$. Evaluating the $35$-variable quadratic system of $\mathcal{A}_{\mathrm{HN}}$ at $z = 1/4$ yields exact rational values $L_q(1/4) \in \mathbb{Q}$, reducing the square-root Puiseux coefficients $b_q$ to a nonsingular rational linear system, whereas eliminating non-sink states of $\mathcal{A}_{\mathrm{SN}}$ and $\mathcal{A}_P$ isolates recurrent cores analytic strictly past $z = 1/4$, certified both by degree-$35$ resultant polynomials and by elementary positive-vector evaluations at $z = 37/125$ formalized directly over $\mathbb{N}$.

### 1.4. Constructive Mechanization and Organization

Every definition, construction, finite table check, and theorem in this monograph has been constructively formalized and kernel-verified in the Lean 4 theorem prover (version 4.33.1). Throughout the entire development, all proofs rely exclusively on Lean's standard propositional extensionality and quotient soundness principles, avoiding classical choice, excluded middle on undecidable predicates, and external reflection or native-code evaluation oracles. In addition, all compilers, tree-walking selectors, finite $S$-algebras, halting detectors, and output decoders are implemented in a standalone Wolfram Language package cross-checked on concrete Turing machine, Busy Beaver, cyclic tag, and small-term census benchmarks.

The remainder of the monograph is organized as follows. Section 2 establishes the rewriting syntax, confluence, conservation, acyclicity, order-$3$, Böhm-tree, finite $S$-algebra, and ongoing-simulation preliminaries. Section 3 presents the $U_{3,11}$ compiler, protected spine-$2$ encoding, stateless zipper tree-walking selector, minimal $11$-state halting automaton, and linear-time bare-term output decoder. Section 4 develops the program-free cyclic tag simulator and its genesis from the $10$-leaf seed $D_{\mathrm{seed}}$. Section 5 proves the leaf-splitting controller-separation theorem, the $7$-step and $5$-step multiway halting shortcuts, and the impossibility of asymmetric branch gating. Section 6 constructs the finite $S$-algebras $\mathcal{A}_{\mathrm{SN}}, \mathcal{A}_{\mathrm{HN}}, \mathcal{A}_P, \mathcal{A}_{36}$ and resolves Questions 5, 7, 10, 30 (on $\mathrm{SN}$), and 31 of [4] together with constructive top-termination. Section 7 analyzes deterministic strategy coincidence, quadratic trace languages, innermost right-step bounds, and Post-clone barriers versus minimal normal-form Rule 110. Section 8 classifies Wolfram's $14$ benchmark terms, establishes small-term minimality thresholds up to $11$ leaves, and proves the Catalan asymptotic phase-transition theorems. Section 9 discusses the constructive formalization architecture, and Appendix A provides a complete concordance mapping every numbered result to its machine-checked declaration.

## 2. Preliminaries: Rewriting Semantics, Infinitary Trees, and Finite $S$-Algebras

### 2.1. Syntax, Spine Geometry, and Conservation Laws

We begin by fixing the syntax, size measures, and reduction relations of $\mathrm{CL}(S)$, following the conventions of Barendregt [1], Waldmann [65], and Barendregt, Endrullis, Klop, and Waldmann [4].

**Definition 2.1 (Syntax, spine measures, and reduction in $\mathrm{CL}(S)$).** 
Let $\mathcal{V} = \{x_0, x_1, x_2, \dots\}$ be a countably infinite set of variables. The set $\mathcal{T}_S(\mathcal{V})$ of *open $S$-terms* is generated inductively by the grammar

$$
M, N \;::=\; S \;\mid\; x \;\mid\; (M\,N) \qquad (x \in \mathcal{V}),
$$

and the subset $\mathcal{T}_S \subset \mathcal{T}_S(\mathcal{V})$ of *closed* (or *ground*) *$S$-terms*—also called *pure-$S$ combinators*—consists of all variable-free terms generated by $M, N ::= S \mid (M\,N)$. Binary application associates to the left, so $M N P \equiv ((M N) P)$, and $M \equiv N$ denotes literal syntactic identity of finite binary trees. Throughout the paper we write the standard closed abbreviations

$$
T \;\equiv\; S S, \qquad B \;\equiv\; S(S S) \;\equiv\; S T, \qquad A \;\equiv\; S S S \;\equiv\; T S.
$$

For every $M \in \mathcal{T}_S(\mathcal{V})$, the *leaf size* $|M| \ge 1$, total binary-tree *node count* $\operatorname{nodes}(M)$, *left-spine length* $\operatorname{ls}(M)$, and *right-spine length* $\operatorname{rs}(M)$ are defined recursively by

$$
\begin{aligned}
|S| &= |x| = 1, & |M N| &= |M| + |N|, & \operatorname{nodes}(M) &= 2|M| - 1, \\
  \operatorname{ls}(S) &= \operatorname{ls}(x) = 0, & \operatorname{ls}(M N) &= 1 + \operatorname{ls}(M), & \operatorname{rs}(S) = \operatorname{rs}(x) &= 0,\quad \operatorname{rs}(M N) = 1 + \operatorname{rs}(N).
\end{aligned}
$$

A *one-hole context* is generated by $C[\,] ::= \square \mid (C[\,]\,N) \mid (M\,C[\,])$, with $C[M]$ denoting substitution of $M$ into the unique hole $\square$. An *$S$-redex* is any term of the form $S X Y Z$, with *contractum* $(X Z)(Y Z)$. *One-step reduction* $\to_S$ is the contextual closure of root contraction: $C[S X Y Z] \to_S C[(X Z)(Y Z)]$. We write $\to_r$ for contraction at the root position ($C[\,] \equiv \square$), $\to_S^+$ for the transitive closure of $\to_S$, $\to_S^*$ for its reflexive-transitive closure, $\to_S^k$ for $k$-fold composition, and $=_S$ for the equivalence relation (convertibility) generated by $\to_S$.

A term $M \in \mathcal{T}_S(\mathcal{V})$ is in *normal form* ($M \in \mathrm{NF}$) if there is no $N$ with $M \to_S N$; *weakly normalizing* ($M \in \mathrm{WN}$) if $M \to_S^* N$ for some $N \in \mathrm{NF}$; and *strongly normalizing* ($M \in \mathrm{SN}$) if $M$ is constructively well-founded (accessible) with respect to $\to_S$, meaning every reduction sequence starting from $M$ terminates.

Note that the number of closed $S$-terms of leaf size $n \ge 1$ is the Catalan number $C_{n-1} = \frac{1}{n}\binom{2n-2}{n-1}$, since closed $S$-terms of leaf size $n$ are in bijection with full binary trees having $n$ leaves and $n-1$ internal application nodes.

**Proposition 2.2 (Confluence, monotonicity, and $\mathrm{WN} = \mathrm{SN}$).** 
The rewrite system $(\mathcal{T}_S(\mathcal{V}), \to_S)$ satisfies the following properties:

- (i) *Confluence (Church–Rosser):* If $M \to_S^* N_1$ and $M \to_S^* N_2$, there exists $P \in \mathcal{T}_S(\mathcal{V})$ such that $N_1 \to_S^* P$ and $N_2 \to_S^* P$. Consequently, $M =_S N$ holds if and only if $M$ and $N$ share a common reduct, and normal forms are unique up to $\equiv$.
- (ii) *Leaf and right-spine monotonicity:* Whenever $M \to_S N$, one has $|M| \le |N|$ and $\operatorname{rs}(M) \le \operatorname{rs}(N)$. Specifically, $|S X Y Z| = |(X Z)(Y Z)|$ holds if and only if $|Z| = 1$ (that is, $Z \equiv S$ or $Z \in \mathcal{V}$).
- (iii) *Conservation ($\mathrm{WN} = \mathrm{SN}$):* If $M \to_S N$ and $N \in \mathrm{SN}$, then $M \in \mathrm{SN}$. In particular, $\mathrm{WN} = \mathrm{SN}$ on $\mathcal{T}_S(\mathcal{V})$.

*Proof.* 
For (i), $\mathrm{CL}(S)$ is an orthogonal left-linear combinatory rewrite system [59]. Explicitly, adapting Takahashi's parallel reduction method [58], define $M \Rightarrow N$ inductively by the clauses $S \Rightarrow S$, $x \Rightarrow x$, and $M_1 M_2 \Rightarrow N_1 N_2$ whenever $M_i \Rightarrow N_i$, together with $S X Y Z \Rightarrow (X' Z')(Y' Z')$ whenever $X \Rightarrow X'$, $Y \Rightarrow Y'$, and $Z \Rightarrow Z'$. Define the complete development map $\Delta \colon \mathcal{T}_S(\mathcal{V}) \to \mathcal{T}_S(\mathcal{V})$ by $\Delta(S X Y Z) \equiv (\Delta(X)\,\Delta(Z))(\Delta(Y)\,\Delta(Z))$ on root redexes, $\Delta(M_1 M_2) \equiv \Delta(M_1)\,\Delta(M_2)$ on non-redex applications, and $\Delta(a) \equiv a$ on atoms $a \in \{S\} \cup \mathcal{V}$. Structural induction on $M \Rightarrow N$ shows the triangle property $N \Rightarrow \Delta(M)$: in the sole overlap-free critical check where $M \equiv (S X Y) Z$ steps via $M_1 M_2 \Rightarrow N_1 N_2$, inversion on $S X Y \Rightarrow N_1$ forces $N_1 \equiv S X' Y'$ with $X' \Rightarrow \Delta(X)$ and $Y' \Rightarrow \Delta(Y)$, whence $N_1 N_2 \equiv S X' Y' Z' \Rightarrow (\Delta(X)\,\Delta(Z))(\Delta(Y)\,\Delta(Z)) \equiv \Delta(M)$. The diamond property for $\Rightarrow$ follows immediately, and since $\to_S \;\subseteq\; \Rightarrow \;\subseteq\; \to_S^*$, diagram chasing yields Church–Rosser confluence.

For (ii), at a root redex $S X Y Z \to_r (X Z)(Y Z)$ we have

$$
|(X Z)(Y Z)| - |S X Y Z| \;=\; (|X| + |Z| + |Y| + |Z|) - (1 + |X| + |Y| + |Z|) \;=\; |Z| - 1 \;\ge\; 0,
$$

with equality if and only if $|Z| = 1$, while $\operatorname{rs}((X Z)(Y Z)) = 1 + \operatorname{rs}(Y Z) = 2 + \operatorname{rs}(Z) > 1 + \operatorname{rs}(Z) = \operatorname{rs}(S X Y Z)$. Induction over contexts $C[\,]$ preserves $|M| \le |N|$ everywhere and preserves $\operatorname{rs}(M) \le \operatorname{rs}(N)$ because left-child steps leave $\operatorname{rs}(L R) = 1 + \operatorname{rs}(R)$ unchanged and right-child steps increase $\operatorname{rs}(R)$ monotonically.

For (iii), enrich parallel reduction with an explicit contraction weight $M \Rightarrow_w N$ ($w \in \mathbb{N}$): atoms have weight $0$, application satisfies $M_1 M_2 \Rightarrow_{w_1 + w_2} N_1 N_2$, and redex contraction satisfies $S X Y Z \Rightarrow_{1 + w_X + w_Y + 2 w_Z} (X' Z')(Y' Z')$. Note that $M \to_S N$ implies $M \Rightarrow_1 N$. A routine structural induction on $M \Rightarrow_w N$ establishes the projection alternative: for every step $M \to_S M_1$, either there exists $w_1 < w$ with $M_1 \Rightarrow_{w_1} N$ (when $M \to_S M_1$ contracts a redex already contracted in $M \Rightarrow_w N$, using $(w_X + w_Z) + (w_Y + w_Z) < 1 + w_X + w_Y + 2 w_Z$), or there exist $N_1$ and $w_1 \in \mathbb{N}$ such that $N \to_S^+ N_1$ and $M_1 \Rightarrow_{w_1} N_1$ (in particular, when $M \to_S M_1$ contracts inside $Z \to_S Z_1$ of a redex $S X Y Z$, both copies of $Z'$ in $(X' Z')(Y' Z')$ step to $Z_1'$, guaranteeing at least two positive steps $N \to_S^+ N_1$ because $Z$ is never erased). Well-founded induction on $N \in \mathrm{SN}$ (lifted to $\to_S^+$) with an inner induction on $w$ then proves $M \in \mathrm{SN}$. Induction along $M \to_S^* N \in \mathrm{NF} \subseteq \mathrm{SN}$ yields $\mathrm{WN} \subseteq \mathrm{SN}$, and $\mathrm{SN} \subseteq \mathrm{WN}$ holds constructively by picking the leftmost redex until none remains.
 $\square$

### 2.2. Acyclicity, Non-Spiralling, and Functional Order

Although $\mathrm{CL}(S)$ admits infinite reductions, its non-erasing binary geometry forbids both cyclic reductions and self-embedding spirals, and bounds the functional arity of every pure-$S$ term by $3$.

**Proposition 2.3 (Acyclicity, non-spiralling, and functional order at most $3$).** 
Let $M, N \in \mathcal{T}_S(\mathcal{V})$.

- (i) *Bergstra acyclicity and decidability of $\to_S^*$ [37, 4]:* Define $\|S\|_{\mathrm{B}} = \|x\|_{\mathrm{B}} = 1$ and $\|P Q\|_{\mathrm{B}} = 2\|P\|_{\mathrm{B}} + \|Q\|_{\mathrm{B}}$. Whenever $M \to_S N$ with $|M| = |N|$, one has $\|N\|_{\mathrm{B}} < \|M\|_{\mathrm{B}}$. Consequently, no $M \in \mathcal{T}_S(\mathcal{V})$ satisfies $M \to_S^+ M$, and pointwise reachability $M \to_S^* N$ is constructively decidable for all $M, N \in \mathcal{T}_S(\mathcal{V})$.
- (ii) *Waldmann's no-spiral theorem [65, 4]:* For every one-hole context $C[\,]$ and every $M \in \mathcal{T}_S(\mathcal{V})$, it is impossible that $M \to_S^+ C[M]$; if $C[\,] \not\equiv \square$, then $M \to_S^* C[M]$ does not hold.
- (iii) *Visser–van Oostrom order-$3$ theorem [4]:* For all $M \in \mathcal{T}_S(\mathcal{V})$ and variables $x_0, x_1, x_2, x_3 \in \mathcal{V}$, there do not exist $P, Q \in \mathcal{T}_S(\mathcal{V})$ such that $M x_0 x_1 x_2 \to_S^* S P Q$. Consequently, every $M \in \mathcal{T}_S(\mathcal{V})$ has functional order $\operatorname{ord}(M) \le 3$: whenever $M x_0 x_1 x_2 x_3 \to_S^* N$, there exists $N' \in \mathcal{T}_S(\mathcal{V})$ such that $N \equiv N' x_3$ and $M x_0 x_1 x_2 \to_S^* N'$.

*Proof.* 
For (i), if $S X Y Z \to_r (X Z)(Y Z)$ preserves leaf count, Proposition 2.2(ii) gives $|Z| = 1$, so $Z$ is an atom and $\|Z\|_{\mathrm{B}} = 1$. Direct expansion yields

$$
\begin{aligned}
\|S X Y Z\|_{\mathrm{B}} &\;=\; 2\bigl(2(2\cdot 1 + \|X\|_{\mathrm{B}}) + \|Y\|_{\mathrm{B}}\bigr) + 1 \;=\; 4\|X\|_{\mathrm{B}} + 2\|Y\|_{\mathrm{B}} + 9, \\
  \|(X Z)(Y Z)\|_{\mathrm{B}} &\;=\; 2(2\|X\|_{\mathrm{B}} + 1) + (2\|Y\|_{\mathrm{B}} + 1) \;=\; 4\|X\|_{\mathrm{B}} + 2\|Y\|_{\mathrm{B}} + 3,
\end{aligned}
$$

which drops strictly by $6$; contextual induction preserves strict decrease since $u \mapsto 2u + v$ and $v \mapsto 2u + v$ are strictly monotone. Thus every step $M \to_S M'$ strictly decreases the lexicographic pair $(|N| - |M|,\, \|M\|_{\mathrm{B}})$ along any candidate path $M \to_S^* N$ (which requires $|M'| \le |N|$ by Proposition 2.2(ii)), ruling out $M \to_S^+ M$ and bounding the finite search tree for $M \to_S^* N$.

For (ii), label every binary application node $P \cdot Q$ of a term with $\rho(Q) := 1 + \operatorname{rs}(Q)$. Under a root step $S \cdot_a X \cdot_b Y \cdot_c Z \to_r (X \cdot_c Z) \cdot_{1+c} (Y \cdot_c Z)$ where $c = \rho(Z)$, the top label increases strictly from $c$ to $1 + c$ while the two child applications receive the smaller label $c$; under a right-child step $P \cdot_c Q \to P \cdot_{c'} Q'$, Proposition 2.2(ii) gives $c \le c'$. Suppose toward a contradiction that $M \to_S^+ C[M]$. Because this reduction is finite, all labels occurring along it are bounded by some $B \in \mathbb{N}$. Replacing each label $k$ by the inverted rank $d = B - k \in \{0,\dots,B\}$ converts every step of $M \to_S^+ C[M]$ into a positive step in the recursive path ordering (RPO) over ranked binary operators $\{\cdot_d\}_{0 \le d \le B}$, in which $\cdot_d$ dominates $\cdot_{d'}$ for $d' < d$ and subterm extraction $C[M] \triangleright^* M$ is included. Nested well-founded induction on $d$ and structural accessibility proves that this finite-rank RPO is irreflexive on $\to_S^+$, contradicting $M \to_S^+ C[M] \triangleright^* M$. If $C[\,] \not\equiv \square$, then $|M| < |C[M]|$ excludes $M \equiv C[M]$ as well.

For (iii), let $\mathcal{W}_1 \subset \mathcal{T}_S(\mathcal{V})$ be the set of terms whose rightmost leaf is a variable ($x \in \mathcal{W}_1$, $S \notin \mathcal{W}_1$, and $P Q \in \mathcal{W}_1$ if and only if $Q \in \mathcal{W}_1$), and define $\mathcal{W}_2 = \{P Q : P, Q \in \mathcal{W}_1\}$ and $\mathcal{W}_3 = \{(P Q) R : P, Q, R \in \mathcal{W}_1\} = \{L R : L \in \mathcal{W}_2,\, R \in \mathcal{W}_1\}$. At a root redex $S X Y Z \to_r (X Z)(Y Z)$, the rightmost leaf of $(X Z)(Y Z)$ equals that of $Z$, and contextual steps likewise preserve membership in $\mathcal{W}_1$; hence $\mathcal{W}_1$ is closed under $\to_S$. Closure of $\mathcal{W}_2$ under $\to_S$ follows immediately: if $S X Y Z \equiv (S X Y) Z \in \mathcal{W}_2$, then $S X Y \in \mathcal{W}_1$ (so $Y \in \mathcal{W}_1$) and $Z \in \mathcal{W}_1$, whence $X Z, Y Z \in \mathcal{W}_1$ and $(X Z)(Y Z) \in \mathcal{W}_2$. Similarly, $\mathcal{W}_3$ is closed under $\to_S$: at a root step $S X Y Z \equiv ((S X) Y) Z \in \mathcal{W}_3$, we have $(S X) Y \in \mathcal{W}_2$ and $Z \in \mathcal{W}_1$, so $S X \in \mathcal{W}_1$ (giving $X \in \mathcal{W}_1$); thus $X Z \in \mathcal{W}_2$ and $Y Z \in \mathcal{W}_1$, placing $(X Z)(Y Z) \in \mathcal{W}_3$, while left steps $(P Q) R \to_S L' R$ preserve $L' \in \mathcal{W}_2$ (which remains an application) and right steps preserve $R' \in \mathcal{W}_1$. Now $M x_0 x_1 x_2 \equiv ((M x_0) x_1) x_2 \in \mathcal{W}_3$ because $M x_0, x_1, x_2 \in \mathcal{W}_1$, whereas $S P Q \equiv (S P) Q \notin \mathcal{W}_3$ because $S \notin \mathcal{W}_1$ implies $S P \notin \mathcal{W}_2$. By $\to_S^*$-closure of $\mathcal{W}_3$, the term $M x_0 x_1 x_2$ never reduces to $S P Q$. Consequently, in any reduction of $(M x_0 x_1 x_2)\,x_3$, no root contraction can ever fire and $x_3$ has no internal redexes, so every reduct has the form $N' x_3$ with $M x_0 x_1 x_2 \to_S^* N'$.
 $\square$

### 2.3. Head Reduction, Root Normal Forms, and Böhm Trees

Every closed $S$-term $M \in \mathcal{T}_S$ decomposes uniquely along its left spine as $M \equiv S M_1 M_2 \cdots M_k$ where $k = \operatorname{ls}(M) \ge 0$. If $k \le 2$ (that is, $M \equiv S$, $M \equiv S M_1$, or $M \equiv S M_1 M_2$), no contraction can occur at or along the left spine of $M$; if $k \ge 3$, the unique redex $S M_1 M_2 M_3$ at the top of the left spine is the *head redex* of $M$.

**Definition 2.4 (Head normal forms, root normal forms, Böhm trees, and productivity).** 
On closed $S$-terms $M, N \in \mathcal{T}_S$:

- (i) *Head reduction* $\to_h$ contracts the unique head redex along the left spine: $S X Y Z \to_h (X Z)(Y Z)$, and $P Q \to_h P' Q$ whenever $P \to_h P'$. A term $M \in \mathcal{T}_S$ is in *head normal form* ($M \in \mathrm{HNF}$) if $\operatorname{ls}(M) \le 2$, and is *solvable* or *head-normalizing* ($M \in \mathrm{HN}$) if $M \to_S^* H$ for some $H \in \mathrm{HNF}$; otherwise $M$ is *unsolvable* ($M \in \mathcal{T}_S \setminus \mathrm{HN}$).
- (ii) A term $M \in \mathcal{T}_S$ is a *root normal form* ($M \in \mathrm{RNF}$) if there do not exist $X, Y, Z \in \mathcal{T}_S$ such that $M \to_S^* S X Y Z$. Following Berarducci [9, 8], $M$ is *mute* (or root-active) if $M$ cannot reduce to any root normal form.
- (iii) Following Böhm [13] and Barendregt [1], the *Böhm tree* $\operatorname{BT}(M)$ is the potentially infinite labeled tree over signature $\{S, \cdot, \bot\}$ defined coinductively by $\operatorname{BT}(M) = \bot$ if $M \notin \mathrm{HN}$, and 
$$
\operatorname{BT}(M) \;=\; S \qquad (M \to_S^* S), \qquad
    \operatorname{BT}(M) \;=\; S\,\operatorname{BT}(M_1) \qquad (M \to_S^* S M_1), \qquad
    \operatorname{BT}(M) \;=\; S\,\operatorname{BT}(M_1)\,\operatorname{BT}(M_2) \qquad (M \to_S^* S M_1 M_2).
$$
 Similarly, the *Berarducci tree* $\operatorname{BeT}(M)$ unfolds $M$ at every node having a root normal form ($S$ if $M \to_S^* S$, or $\operatorname{BeT}(P) \cdot \operatorname{BeT}(Q)$ if $M \to_S^* P Q \in \mathrm{RNF}$) and places $\bot$ at mute subterms.
- (iv) To reason constructively about $\bot$-occurrence without coinductive choice, define the inductive finite-depth predicate $\bot_d(M)$ ($d \in \mathbb{N}$, read “$\operatorname{BT}(M)$ contains $\bot$ at tree depth at most $d$”) by four rules: (a) if $M \notin \mathrm{HN}$, then $\bot_d(M)$ holds for all $d$; (b) if $M \to_S^* S X$ and $\bot_d(X)$, then $\bot_{d+1}(M)$; (c) if $M \to_S^* S X Y$ and $\bot_d(X)$, then $\bot_{d+1}(M)$; and (d) if $M \to_S^* S X Y$ and $\bot_d(Y)$, then $\bot_{d+1}(M)$. A closed $S$-term $M \in \mathcal{T}_S$ is *productive* ($M \in \mathrm{Prod}$) if $\neg\bot_d(M)$ holds for all $d \in \mathbb{N}$ [25, 4].

Observe that $\mathrm{HNF}$ is closed under arbitrary reductions $\to_S^*$: if $\operatorname{ls}(H) \le 2$ and $H \to_S H'$, then either $H \equiv S X \to_S S X'$ or $H \equiv S X Y \to_S S X' Y$ or $S X Y'$, preserving $\operatorname{ls}(H') = \operatorname{ls}(H) \le 2$.

**Lemma 2.5 (Conversion invariance of $\mathrm{HN}$ and $\mathrm{Prod}$).** 
For all $M, N \in \mathcal{T}_S$ satisfying $M =_S N$, one has $M \in \mathrm{HN}$ if and only if $N \in \mathrm{HN}$, $\bot_d(M)$ if and only if $\bot_d(N)$ for every $d \in \mathbb{N}$, and hence $M \in \mathrm{Prod}$ if and only if $N \in \mathrm{Prod}$.

*Proof.* 
By Proposition 2.2(i), it suffices to show that $M \to_S^* N$ implies the equivalences $M \in \mathrm{HN}$ if and only if $N \in \mathrm{HN}$, and $\bot_d(M)$ if and only if $\bot_d(N)$. First, if $N \to_S^* H$ with $\operatorname{ls}(H) \le 2$, transitivity gives $M \to_S^* H$, so $N \in \mathrm{HN}$ implies $M \in \mathrm{HN}$. Conversely, if $M \to_S^* H$ with $\operatorname{ls}(H) \le 2$, Church–Rosser yields $U$ with $N \to_S^* U$ and $H \to_S^* U$; since $\operatorname{ls} \le 2$ is preserved under $\to_S^*$, we have $\operatorname{ls}(U) \le 2$ and $N \in \mathrm{HN}$.

Next we prove by induction on $d$ that $M \to_S^* N$ implies $\bot_d(M)$ if and only if $\bot_d(N)$. At depth $d = 0$, the predicate $\bot_0(P)$ holds if and only if $P \notin \mathrm{HN}$, which is already invariant. Assume equivalence holds at depth $d$. If $\bot_{d+1}(N)$ holds via $N \to_S^* S X$ with $\bot_d(X)$ (or $N \to_S^* S X Y$ with $\bot_d(X)$ or $\bot_d(Y)$), then $M \to_S^* N \to_S^* S X$ (or $S X Y$) immediately derives $\bot_{d+1}(M)$. Conversely, suppose $\bot_{d+1}(M)$ holds. If $M \notin \mathrm{HN}$, then $N \notin \mathrm{HN}$ and $\bot_{d+1}(N)$ holds by rule (a). If $M \to_S^* S X$ with $\bot_d(X)$, Church–Rosser on $M \to_S^* N$ and $M \to_S^* S X$ yields $U$ with $N \to_S^* U$ and $S X \to_S^* U$; inversion on $S X \to_S^* U$ forces $U \equiv S X'$ with $X \to_S^* X'$, so the induction hypothesis gives $\bot_d(X')$ and hence $\bot_{d+1}(N)$. The remaining two cases where $M \to_S^* S X Y$ follow identically because $S X Y \to_S^* U$ forces $U \equiv S X' Y'$ with $X \to_S^* X'$ and $Y \to_S^* Y'$. Negating the existence of $d \in \mathbb{N}$ satisfying $\bot_d(-)$ yields $M \in \mathrm{Prod}$ if and only if $N \in \mathrm{Prod}$.
 $\square$

### 2.4. Bottom-Up Tree Automata, Finite $S$-Algebras, and Ongoing Simulation

Because $\mathcal{T}_S$ is the set of ground terms over a signature consisting of one nullary constant $S$ and one binary operator $\cdot$, deterministic bottom-up tree automata on $\mathcal{T}_S$ coincide with finite pointed magmas equipped with an accepting subset [24, 4].

**Definition 2.6 (Bottom-up tree automata and finite $S$-algebras).** 
A *deterministic bottom-up tree automaton* (DTA) over $\mathcal{T}_S$ is a quadruple $\mathcal{A} = (Q, q_0, \odot, F)$, where $Q$ is a finite nonempty set of states, $q_0 \in Q$ is the leaf constant ($q_0 = \llbracket S \rrbracket_{\mathcal{A}}$), $\odot \colon Q \times Q \to Q$ is the binary transition operation, and $F \subseteq Q$ is the accepting subset. The evaluation morphism $\llbracket - \rrbracket_{\mathcal{A}} \colon \mathcal{T}_S \to Q$ is defined recursively by

$$
\llbracket S \rrbracket_{\mathcal{A}} \;=\; q_0, \qquad \llbracket M N \rrbracket_{\mathcal{A}} \;=\; \llbracket M \rrbracket_{\mathcal{A}} \odot \llbracket N \rrbracket_{\mathcal{A}},
$$

and the recognized regular tree language is $L(\mathcal{A}) = \{M \in \mathcal{T}_S : \llbracket M \rrbracket_{\mathcal{A}} \in F\}$. Clearly $\llbracket M \rrbracket_{\mathcal{A}}$ is computable in a single bottom-up pass of $2|M| - 1$ table lookups ($O(|M|)$ time). We call $\mathcal{A}$ a *finite $S$-algebra* if $\odot$ satisfies the combinatory identity

$$
((q_0 \odot x) \odot y) \odot z \;=\; (x \odot z) \odot (y \odot z) \qquad (\text{for all } x, y, z \in Q). \tag{2.1}
$$

Because $\llbracket - \rrbracket_{\mathcal{A}}$ is compositional on application contexts, (2.1) implies $\llbracket M \rrbracket_{\mathcal{A}} = \llbracket N \rrbracket_{\mathcal{A}}$ whenever $M =_S N$, making $L(\mathcal{A})$ invariant under unrestricted pure-$S$ conversion.

Finally, building on classical criteria for non-trivial simulation and encoding complexity [21, 27, 34] together with Priese [50], van Emde Boas [61], Neary and Woods [44], and Wolfram [70], we formalize ongoing simulation of a deterministic computation system in $\mathrm{CL}(S)$ with explicit sub-universal guards on all boundary maps.

**Definition 2.7 (Ongoing pure-$S$ simulation with sub-universal boundary maps).** 
Let $\mathcal{S}$ be a deterministic computational model with instance set $\mathcal{I}$, step relation $\vdash_{\mathcal{S}}$, halting predicate $\mathrm{Halts}_{\mathcal{S}}(I)$, and partial output map $\operatorname{out}_{\mathcal{S}} \colon \mathcal{I} \rightharpoonup \Sigma^*$. An *ongoing selected-path simulation* of $\mathcal{S}$ in $\mathrm{CL}(S)$ is a quadruple $(\mathcal{E}, \sigma, \mathcal{H}, \mathcal{D})$ consisting of:

- (i) a total polynomial-time (or logspace) *encoder* $\mathcal{E} \colon \mathcal{I} \to \mathcal{T}_S$ mapping each instance $I \in \mathcal{I}$ to a finite closed $S$-term $T_0 = \mathcal{E}(I)$ of size $|T_0| \le \mathrm{poly}(\|I\|)$;
- (ii) a fixed stateless *single-step selector* $\sigma \colon \mathcal{T}_S \to \mathcal{T}_S \cup \{\mathsf{normal}\}$ realized by a finite-state tree-walking automaton that resets to a unique initial control state at the root of $T$ before each step, halts on every $T \in \mathcal{T}_S$ in $O(|T|)$ cursor transitions, and satisfies $T \to_S \sigma(T)$ whenever $\sigma(T) \in \mathcal{T}_S$;
- (iii) a *halting detector* $\mathcal{H} = (Q_{\mathrm{halt}}, q_0, \odot_{\mathrm{halt}}, F_{\mathrm{halt}})$ given by a fixed deterministic bottom-up finite tree automaton ($L(\mathcal{H}) \in \mathrm{REG}$); and
- (iv) a total polynomial-time (in $|T|$) read-only *output decoder* $\mathcal{D} \colon \mathcal{T}_S \to \Sigma^* \cup \{\bot\}$,

such that along the iterated reduction trajectory $T_0 = \mathcal{E}(I)$ and $T_{k+1} = \sigma(T_k)$ (defined while $\sigma(T_k) \in \mathcal{T}_S$), one has $\mathrm{Halts}_{\mathcal{S}}(I)$ if and only if there exists $k \ge 0$ with $T_k \in L(\mathcal{H})$, and every such step $k$ satisfies $\mathcal{D}(T_k) = \operatorname{out}_{\mathcal{S}}(I)$. Because $\mathcal{E}$ is total polynomial-time (indeed logspace-constructible up to tree output), $\mathcal{H}$ has $O(1)$ finite memory, and $\mathcal{D}$ terminates in bounded polynomial time on every bare tree $T \in \mathcal{T}_S$, none of the boundary maps $(\mathcal{E}, \mathcal{H}, \mathcal{D})$ can decide any $\Sigma_1^0$-complete problem on its own.

## 3. Polynomial-Size Turing Machine Simulation Under Root-Restarted Selection

Arbitrary deterministic binary Turing machines admit an explicit ongoing pure-$S$ simulation $(\mathcal{E}_{\mathrm{TM}}, \sigma_{\mathrm{TM}}, \mathcal{H}_{11}, \mathcal{D}_{\mathrm{TM}})$ with quartic initial tree size $O((|Q|^2 + |w|)^2)$, node-linear stateless tree-walking step selection, a minimal $11$-state bottom-up halting automaton, and linear-time bare-term output recovery. Following the modular simulation methodology of Cook [17], Neary and Woods [44, 43], and Smith [55], we factor the compiler into four layers: boundary-safe marked normalization, compilation to $U_{3,11}$, $4$-bit binary specialization to $U_{\mathrm{bin}}$, and protected spine-$2$ pure-$S$ encoding.

### 3.1. Source Normalization and Compilation to Neary–Woods $U_{3,11}$

In Neary and Woods's universal Turing machine $U_{3,11}$ [44, 43], the simulated binary machine operates on a one-way infinite tape indexed by $\mathbb{N}$, never steps left from cell $0$ during active computation, and signals halting by entering a designated final state that sweeps left until exiting cell $0$. Our first definition compiles any partial clamping-left binary Turing machine into this exact normal form without corrupting output bits.

**Definition 3.1 (Source Turing machines and boundary-safe marked normalization).** 
A *clamping-left binary Turing machine* is a pair $M = (Q, \delta_M)$ where $Q = \{0, \dots, |Q|-1\}$ ($|Q| \ge 1$) is a finite state set with start state $0$, and

$$
\delta_M \colon Q \times \{0, 1\} \;\rightharpoonup\; \{0, 1\} \times \{\mathsf{L}, \mathsf{S}, \mathsf{R}\} \times Q
$$

is a partial transition function. A configuration $(q, h, \tau) \in Q \times \mathbb{N} \times \{0,1\}^*$ (with blank-padded cell lookup $\tau[i] \in \{0,1\}$, defaulting to $0$ for $i \ge |\tau|$) halts if $(q, \tau[h]) \notin \operatorname{dom}(\delta_M)$, and otherwise steps to $(q', h', \tau[h := b'])$ where $\delta_M(q, \tau[h]) = (b', d, q')$ and $h' = \max(h-1, 0)$ for $d = \mathsf{L}$, $h' = h$ for $d = \mathsf{S}$, and $h' = h + 1$ for $d = \mathsf{R}$. On input $w \in \{0,1\}^*$, the machine $M$ starts at $(0, 0, w)$; if $M$ reaches a halted configuration $(q_{\mathrm{fin}}, h_{\mathrm{fin}}, \tau_{\mathrm{fin}})$, its *canonical output* $\operatorname{out}_M(w) \in \{0,1\}^*$ is $\tau_{\mathrm{fin}}$ stripped of trailing $0$-blanks.

Given $M = (Q, \delta_M)$ and $w \in \{0,1\}^*$, the *boundary-safe normalized instance* $(M_{\mathrm{norm}}, w_{\mathrm{mark}})$ is constructed as follows:

- (i) *Sentinel-interleaved tape:* For $w = b_0 b_1 \cdots b_{m-1}$ ($m \ge 1$), set $w_{\mathrm{mark}} = 1\,b_0\,0\,b_1\,0\cdots 0\,b_{m-1}$, and for $w = \varepsilon$ set $w_{\mathrm{mark}} = 1\,0$. Thus $|w_{\mathrm{mark}}| \le 2|w| + 2$, cell $0$ holds the left-boundary sentinel $1$, every positive even cell $2i$ ($i \ge 1$) holds marker $0$, and every odd cell $2i + 1$ ($i \ge 0$) holds data bit $w[i]$.
- (ii) *Total $\{\mathsf{L},\mathsf{R}\}$ rule table:* Let $r = |\operatorname{dom}(\delta_M)| \le 2|Q|$ be the number of defined transitions of $M$, ordered lexicographically by $(q, b) \in Q \times \{0,1\}$. Then $M_{\mathrm{norm}}$ has state set $Q_{\mathrm{norm}} = \{0, \dots, S_{\mathrm{norm}}-1\}$ of cardinality 
$$
S_{\mathrm{norm}} \;=\; |Q| + 2 + r \;\le\; 3|Q| + 2,
$$
 consisting of an entry state $0$ (which leaves cell $0$ unchanged and moves $\mathsf{R}$ to odd cell $1$ in state $1$), shifted source states $q + 1$ ($q \in Q$), dedicated auxiliary states $|Q| + 1 + \mathrm{idx}(q,b)$ executing each defined source step in two moves across the adjacent marker cell (clamping at cell $0$ whenever the marker reads $1$ so active steps never exit cell $0$), and a unique halt-sweep state $S_{\mathrm{norm}} - 1$ entered on $(q,b) \notin \operatorname{dom}(\delta_M)$, which obeys $(S_{\mathrm{norm}}-1, b) \mapsto (b, \mathsf{L}, S_{\mathrm{norm}}-1)$ for all $b \in \{0,1\}$, preserving every cell until attempting a left move from cell $0$.

By construction, after one initialization step $(0, 0, w_{\mathrm{mark}}) \vdash (1, 1, w_{\mathrm{mark}})$, $t$ active steps of $M$ correspond bijectively to $2t$ steps of $M_{\mathrm{norm}}$ maintaining head position $2h + 1$, sentinel $\tau_{\mathrm{norm}}[0] = 1$, even markers $\tau_{\mathrm{norm}}[2i] = 0$ ($i \ge 1$), and odd data $\tau_{\mathrm{norm}}[2i+1] = \tau[i]$, while halting at $(q, h, \tau)$ triggers an exact $(1 + 2h)$-step non-destructive left sweep to $(S_{\mathrm{norm}}-1, 0, \tau_{\mathrm{norm}})$, which exits cell $0$ to the left.

Within the small universal Turing machine program initiated by Watanabe [66] and advanced through the tag-based machines of Rogozhin and Kudlek [51, 52, 38] (surveyed in [74]), Neary and Woods's $3$-state, $11$-symbol machine $U_{3,11}$ [44, 43] achieves direct quadratic-time Turing simulation without intermediate tag-system exponential blowup.

**Definition 3.2 (The universal Turing machine $U_{3,11}$ and encoder $\mathcal{E}_U$).** 
The machine $U_{3,11}$ has state set $Q_U = \{u_1, u_2, u_3\}$ (with start state $u_1$) and $11$-symbol tape alphabet

$$
\Sigma_{11} \;=\; \bigl\{\,\overleftarrow{a},\, \overleftarrow{b},\, e,\, h,\, \overrightarrow{e},\, \overrightarrow{h},\, \overleftarrow{e},\, \overleftarrow{h},\, \lambda,\, \delta,\, \gamma\,\bigr\},
$$

indexed $0, 1, \dots, 10$ in that order, with blank symbol $\overleftarrow{a}$ ($0$) and $32$ defined transitions displayed in Table 2; the unique undefined halting pair is $(u_3, \delta)$.

**Table 2.** Complete transition table of Neary and Woods's $3$-state, $11$-symbol universal Turing machine $U_{3,11}$ [44, 43], where $\overleftarrow{a}$ is the blank symbol and $(u_3, \delta)$ is the unique halting configuration.

| Index | Symbol | State $u_1$ | State $u_2$ | State $u_3$ |
| —: | :—: | :—: | :—: | :—: |
| $0$ | $\overleftarrow{a}$ | $(\overleftarrow{e},\, \mathsf{R},\, u_1)$ | $(\gamma,\, \mathsf{L},\, u_2)$ | $(\overleftarrow{a},\, \mathsf{L},\, u_3)$ |
| $1$ | $\overleftarrow{b}$ | $(\overleftarrow{e},\, \mathsf{R},\, u_2)$ | $(\overleftarrow{b},\, \mathsf{L},\, u_1)$ | $(e,\, \mathsf{R},\, u_1)$ |
| $2$ | $e$ | $(\overrightarrow{e},\, \mathsf{L},\, u_1)$ | $(\overleftarrow{e},\, \mathsf{R},\, u_1)$ | $(e,\, \mathsf{R},\, u_1)$ |
| $3$ | $h$ | $(\overrightarrow{h},\, \mathsf{L},\, u_1)$ | $(\overleftarrow{h},\, \mathsf{R},\, u_3)$ | $(\overleftarrow{a},\, \mathsf{L},\, u_1)$ |
| $4$ | $\overrightarrow{e}$ | $(\overleftarrow{e},\, \mathsf{R},\, u_1)$ | $(e,\, \mathsf{R},\, u_2)$ | $(\overleftarrow{e},\, \mathsf{R},\, u_3)$ |
| $5$ | $\overrightarrow{h}$ | $(\overleftarrow{h},\, \mathsf{R},\, u_1)$ | $(h,\, \mathsf{R},\, u_2)$ | $(\overleftarrow{h},\, \mathsf{R},\, u_3)$ |
| $6$ | $\overleftarrow{e}$ | $(\overrightarrow{e},\, \mathsf{L},\, u_1)$ | $(\overrightarrow{e},\, \mathsf{L},\, u_2)$ | $(\gamma,\, \mathsf{L},\, u_2)$ |
| $7$ | $\overleftarrow{h}$ | $(\overrightarrow{h},\, \mathsf{L},\, u_1)$ | $(\overrightarrow{h},\, \mathsf{L},\, u_2)$ | $(\overleftarrow{a},\, \mathsf{L},\, u_3)$ |
| $8$ | $\lambda$ | $(\delta,\, \mathsf{R},\, u_1)$ | $(\lambda,\, \mathsf{R},\, u_2)$ | $(\delta,\, \mathsf{R},\, u_3)$ |
| $9$ | $\delta$ | $(\lambda,\, \mathsf{L},\, u_1)$ | $(\lambda,\, \mathsf{L},\, u_2)$ | HALT |
| $10$ | $\gamma$ | $(\overleftarrow{a},\, \mathsf{L},\, u_3)$ | $(\overleftarrow{h},\, \mathsf{R},\, u_3)$ | $(\overleftarrow{b},\, \mathsf{L},\, u_3)$ |

Given a normalized machine $M_{\mathrm{norm}}$ with $s = S_{\mathrm{norm}} \ge 3$ states and marked word $w_{\mathrm{mark}} \in \{0,1\}^*$, each transition $\theta = (b', d, q') = \delta_{\mathrm{norm}}(q, b)$ ($q, q' \in \{0,\dots,s-1\}$) is encoded as an *encoded transition rule* (ETR) word over $\{e, h\}^*$: setting $\beta(\theta) = 2 + 5q' + 3\cdot\mathbf{1}_{d = \mathsf{L}}$ and $\alpha(\theta) = 5s + 2 - \beta(\theta)$, define

$$
E(\theta) \;=\; \begin{cases}
    h^{\mathbf{1}_{b'=1}}\, e^{\alpha(\theta)}\, h^{\beta(\theta)}, & \textrm{if } d = \mathsf{R}, \\
    e^{\alpha(\theta)-1}\, h^{\beta(\theta)}\, e\, h^{\mathbf{1}_{b'=1}}\, e, & \textrm{if } d = \mathsf{L}.
  \end{cases}
$$

For each state $q \in \{0,\dots,s-1\}$, let $E'(q) = e^{5(s-q)-3}\,h^{4+5q}$ if $q = 0$ or $q$ has an incoming $\mathsf{R}$-transition in $M_{\mathrm{norm}}$, and $E'(q) = \varepsilon$ otherwise. State $q$ is represented by the $5$-block tuple (ordered from left to right on the program prefix)

$$
\mathcal{P}(q) \;=\; \lambda\,E(\delta_{\mathrm{norm}}(q,1))\,\lambda\,E(\delta_{\mathrm{norm}}(q,0))\,\lambda\,E(\delta_{\mathrm{norm}}(q,0))\,\lambda\,E(\delta_{\mathrm{norm}}(q,1))\,\lambda\,E'(q).
$$

Encoding each right-side tape bit $b \in \{0,1\}$ via the $2$-symbol block $\langle 0 \rangle_R = \overleftarrow{a}\overleftarrow{a}$ and $\langle 1 \rangle_R = \overleftarrow{b}\overleftarrow{a}$, the compiled initial $U_{3,11}$ configuration $u_0 = \mathcal{E}_U(M, w)$ places $\mathcal{P}(s-1)\cdots\mathcal{P}(1)\mathcal{P}(0)\lambda e$ to the left of the head, scans $\overleftarrow{a}$ in start state $u_1$, and places $\overleftarrow{a}^{5s-1}\,\overleftarrow{b}\overleftarrow{b}\,\langle w_{\mathrm{mark}} \rangle_R$ to the right of the head.

**Proposition 3.3 (Polynomial $U_{3,11}$ simulation and initial tape bound).** 
For every clamping-left binary Turing machine $M = (Q, \delta_M)$ and input $w \in \{0,1\}^*$, let $u_0 = \mathcal{E}_U(M, w)$ and set

$$
N(M, w) \;:=\; 225|Q|^2 + 390|Q| + 4|w| + 173. \tag{3.1}
$$

Then:

- (i) *Quadratic tape size:* The total non-blank length $|u_0|$ of $u_0$ satisfies $|u_0| + 1 \le N(M,w)$.
- (ii) *Constructive halting equivalence and output recovery:* The machine $M$ halts on $w$ if and only if $U_{3,11}$ starting from $u_0$ reaches an undefined transition (necessarily at $(u_3, \delta)$). Moreover, from the halted $U_{3,11}$ tape, a single left-to-right linear scan strips the $\overleftarrow{a}^*\overleftarrow{b}^{\ge 2}\overleftarrow{a}$ state header, decodes $\langle - \rangle_R$ pairs, verifies the sentinel $1$, and extracts odd-indexed data bits to recover $\operatorname{out}_M(w)$ identically.

*Proof.* 
For (i), let $s = S_{\mathrm{norm}}$. Every block in $\mathcal{P}(q)$ has length at most $5s + 4$, so prepending $\lambda$ gives $5s$ blocks of length at most $5s + 5$, plus the $2$-symbol suffix $\lambda e$, one scanned symbol $\overleftarrow{a}$, $(5s - 1) + 2 = 5s + 1$ state-token symbols, and $2|w_{\mathrm{mark}}|$ encoded tape symbols:

$$
|u_0| \;\le\; 5s(5s + 5) + 2 + 1 + (5s + 1) + 2|w_{\mathrm{mark}}| \;=\; 25s^2 + 30s + 2|w_{\mathrm{mark}}| + 4.
$$

Substituting $s \le 3|Q| + 2$ and $|w_{\mathrm{mark}}| \le 2|w| + 2$ from Definition 3.1 yields

$$
|u_0| \;\le\; 25(9|Q|^2 + 12|Q| + 4) + 30(3|Q| + 2) + 2(2|w| + 2) + 4 \;=\; 225|Q|^2 + 390|Q| + 4|w| + 168,
$$

whence $|u_0| + 1 \le 225|Q|^2 + 390|Q| + 4|w| + 169 < N(M,w)$.

For (ii), each simulated step of $M_{\mathrm{norm}}$ factors into the four sub-table cycles of [44, 43]: *Cycle 1 (Index)* shuttles between the unary $\overleftarrow{b}^{k+2}$ state counter on the simulated head and $\lambda$-delimiters in the table, neutralizing $k$ delimiters $\lambda \mapsto \delta$ from right to left until selecting the $k$-th ETR block ($0 \le k < 5s$); *Cycle 2 (Print)* copies the selected ETR block character by character ($e \mapsto \overleftarrow{a}, h \mapsto \overleftarrow{b}$) across the overlined region onto the head; *Cycle 3 (Restore)* sweeps left to right in $u_2$, restoring every neutralized $\delta \mapsto \lambda$ and arrowed symbol $\overleftarrow{e}, \overleftarrow{h} \mapsto e, h$; and *Cycle 4 (Choose Read/Write)* aligns the head over the adjacent simulated cell. Cutting the inductive simulation invariant *immediately after Cycle 1* (the *post-index invariant*) unifies all four transition geometries: at configuration $(q, h, \tau_{\mathrm{norm}})$, $U_{3,11}$ stands in state $u_2$ reading $\gamma$, with untouched blocks $k+1, \dots, 5s-1$ on the far left, the active block $\lambda\,E(\delta_{\mathrm{norm}}(q, \tau_{\mathrm{norm}}[h]))$, $k$ neutralized blocks, $\delta\,\overleftarrow{e}\,\langle \tau_{\mathrm{norm}}[0\mathinner{\ldotp\ldotp}h-1] \rangle_L\,\overleftarrow{e}^{5s+3}$ immediately to the left of $\gamma$, and $\langle \tau_{\mathrm{norm}}[h+1\mathinner{\ldotp\ldotp}] \rangle_R$ to the right of $\gamma$ (modulo trailing $\overleftarrow{a}$-blanks).

From $u_0$, if $w_{\mathrm{mark}}[0] = 1$ (which always holds by sentinel initialization, and even for arbitrary $w$ via the $E'(0)$ two-pass case when $w[0]=0$), one pass of Cycle 1 establishes the post-index invariant for $(0, 0, w_{\mathrm{mark}})$. Given the post-index invariant at $(q, h, \tau_{\mathrm{norm}})$:

- If $M_{\mathrm{norm}}$ steps right to $(q', h+1, \tau')$ writing $b' \in \{0,1\}$, Cycles 2–4 print $b'$ into the left-tape encoding and place $\overleftarrow{a}^{5(s-q')}\overleftarrow{b}^{2+5q'}$ before $\langle \tau'[h+1] \rangle_R$. When $\tau'[h+1] = 1$ ($\overleftarrow{b}\overleftarrow{a}$), the extra $\overleftarrow{b}$ merges directly into $\overleftarrow{b}^{3+5q'}$, indexing block $5q'+1 = E(\delta_{\mathrm{norm}}(q',1))$ in one Cycle 1 pass; when $\tau'[h+1] = 0$ ($\overleftarrow{a}\overleftarrow{a}$, Neary's Case D), $\overleftarrow{b}^{2+5q'}$ first indexes the auxiliary block $5q' = E'(q')$ (nonempty because $q'$ has an incoming $\mathsf{R}$-edge), whose Cycle 2–4 execution shifts two $\overleftarrow{a}$ blanks to yield $\overleftarrow{b}^{4+5q'}$, indexing block $5q'+2 = E(\delta_{\mathrm{norm}}(q',0))$ on the second Cycle 1 pass.
- If $M_{\mathrm{norm}}$ steps left ($h \ge 1$) to $(q', h-1, \tau')$, the block $E(\theta)$ has length $5s + 4$, so Cycle 2 consumes one extra $\overleftarrow{e}$ from the left-side cell $\langle \tau_{\mathrm{norm}}[h-1] \rangle_L \in \{\overleftarrow{e}\overleftarrow{e}, \overleftarrow{h}\overleftarrow{e}\}$; Cycle 4 then branches on $e$ vs. $h$ to append $0$ or $2$ extra $\overleftarrow{b}$ tokens to $\overleftarrow{b}^{5+5q'}$, indexing block $5q'+3 = E(\delta_{\mathrm{norm}}(q',0))$ or $5q'+4 = E(\delta_{\mathrm{norm}}(q',1))$ respectively.
- If $h = 0$ and $\delta_{\mathrm{norm}}(q, \tau_{\mathrm{norm}}[0])$ moves $\mathsf{L}$ (which occurs uniquely when $q = s - 1$ finishes its halt sweep), the extra consumption in Cycle 2 reaches the table delimiter $\delta$ directly, placing $U_{3,11}$ on $(u_3, \delta)$ with the restored table on the left and $\overleftarrow{a}^{5(s-q')-3}\,\overleftarrow{b}^{5+5q'}\,\overleftarrow{a}\,\langle 1 \rangle_R\,\langle \tau_{\mathrm{norm}}[1\mathinner{\ldotp\ldotp}] \rangle_R$ on the right, from which the linear scan reads back $\operatorname{out}_M(w)$.

Because every simulated step executes $m \ge 1$ defined $U_{3,11}$ transitions, constructive bounded-fuel evaluation of $M$ for $T$ steps (returning either a halting run of length at most $T$ or a live $T$-step run) combines with determinism of $U_{3,11}$ to establish bidirectional halting equivalence without invoking classical choice.
 $\square$

### 3.2. Binary Specialization $U_{\mathrm{bin}}$ and Protected Spine-2 Pure-$S$ Encoding

To embed $U_{3,11}$ into $\mathrm{CL}(S)$ with uniform bit-level storage frames, we first specialize $U_{3,11}$ to a fixed binary Turing machine $U_{\mathrm{bin}}$ and then represent $U_{\mathrm{bin}}$ configurations as addressable spines of protected pure-$S$ frames.

**Construction 3.4 (Binary specialization $U_{\mathrm{bin}}$ and pure-$S$ compiler $\mathcal{E}_{\mathrm{TM}}$).** 
Encode each symbol $s \in \Sigma_{11} = \{0,\dots,10\}$ as its $4$-bit big-endian binary block $\mathrm{bin}_4(s) \in \{0,1\}^4$ ($0 \mapsto 0000$, $1 \mapsto 0001$, …, $10 \mapsto 1010$; note $\mathrm{bin}_4(\overleftarrow{a}) = 0000$ matches the binary blank). Compiling the $32$ defined rules of $U_{3,11}$ over $4$-bit blocks yields a fixed deterministic binary Turing machine $U_{\mathrm{bin}}$ with $132$ states ($\{0,\dots,131\}$, with block-entry states $u_1 \mapsto 0$, $u_2 \mapsto 54$, $u_3 \mapsto 55$) and $262$ defined transition rules: every defined transition of $U_{3,11}$ is refined in exactly $10$ binary steps ($3$ right moves to read the $4$-bit symbol, $3$ left moves writing the new $4$-bit symbol, and $4$ moves shifting one block left or right, clamping at the left tape boundary), while the halting pair $(u_3, \delta) = (55, 1001_2)$ executes $6$ binary steps rewinding to the block start in state $41$ scanning bit $1$, where $(41, 1)$ is undefined.

In $\mathrm{CL}(S)$, define for any $a, b, j \in \mathcal{T}_S$ the *protected spine-$2$ frame*

$$
F(a, b, j) \;\equiv\; (S\,a)\,(S\,b\,j), \tag{3.2}
$$

and define counter numerals $\nu_n \in \mathcal{T}_S$ and unopened phase generators $G(m, n) \in \mathcal{T}_S$ ($m, n \in \mathbb{N}$) by

$$
\nu_0 \;\equiv\; S T T \;\equiv\; B T, \qquad \nu_{n+1} \;\equiv\; T\,\nu_n, \qquad G(m, n) \;\equiv\; \nu_m\,\nu_n\,S. \tag{3.3}
$$

Define the depth-indexed phase sequence $p_0 = (2,2)$ and $p_{d+1} = (n, n+1)$ if $p_d = (0, n)$, else $(m-1, n)$ if $p_d = (m, n)$ with $m \ge 1$; every $p_d = (m_d, n_d)$ satisfies $2 \le n_d$ and $m_d \le n_d$. Set the depth-$d$ unopened base $\beta_d \equiv G(m_d, n_d)$ and junk term $\iota_d \equiv (\nu_{n_d - 1} S)\,G(n_d, n_d + 1)$ if $m_d = 0$, else $(\nu_{n_d - 2} S)\,G(m_d - 1, n_d)$.

- (i) *Bit lists and append-only version chains:* At tree depth $d$, a Boolean bit $b \in \{0,1\}$ is encoded as $\beta_d$ if $b = 0$ and $F(\beta_{d+1}, \beta_{d+1}, \iota_d)$ if $b = 1$. A fixed-width bit tuple $v = (b_1,\dots,b_w) \in \{0,1\}^w$ is encoded as a nested frame list ending in sentinel $F(\beta, \beta, \iota)$, and a history of committed $w$-bit records $[v_1, \dots, v_r]$ is encoded along the left spine of $F$-frames so that scanning left children from the root returns the newest complete $w$-bit record $v_r$ while ignoring any partially opened trailing record.
- (ii) *$11$-bit universal tape cells and root hub:* Each binary cell of $U_{\mathrm{bin}}$ is represented by a width-$11$ version chain encoding $(b, \mathrm{st}, q) \in \{0,1\} \times \{\mathsf{off}, \mathsf{active}, \mathsf{movingL}, \mathsf{movingR}\} \times \{0,\dots,255\}$ ($1$ data bit, $2$ status bits, $8$ state bits). Given $(M,w)$ with $u_0 = \mathcal{E}_U(M,w)$, the $4|u_0|$ binary cells of $u_0$ are initialized with one $\mathsf{active}$ record at bit $4 h(u_0)$ in start state $0$ and $\mathsf{off}$ records elsewhere, chained along the right spine of $F$-frames to form $\mathrm{Tape}_0$, and wrapped in the root hub 
$$
\mathcal{E}_{\mathrm{TM}}(M, w) \;\equiv\; (\nu_1\,S)\,F\bigl(\beta_1,\, \mathrm{Tape}_0,\, \iota_0\bigr).
$$

**Lemma 3.5 (Protected-frame opening laws and initial quartic leaf bound).** 
The encoding of Construction 3.4 satisfies:

- (i) *Root inertness and controlled opening:* Every frame $F(a,b,j)$ has $\operatorname{ls}(F(a,b,j)) = 2$ (hence no root redex); if applied externally to an argument $x$, it opens in two steps via $F(a,b,j)\,x \to_S^2 (a x)((b x)(j x))$. Internally without an external argument, for all $m, n \in \mathbb{N}$, the unopened generator $G(m+1, n+2)$ reduces in $6$ steps to 
$$
G(m+1, n+2) \;\to_S^6\; F\bigl(G(m, n+2),\, G(m, n+2),\, (\nu_n S)\,G(m, n+2)\bigr),
$$
 and $G(0, n+2)$ reduces in $7$ steps to $F(G(n+2, n+3), G(n+2, n+3), (\nu_{n+1} S)\,G(n+2, n+3))$, with every intermediate reduct not of $F$-shape and every generated junk term satisfying $\operatorname{ls}(j) \ne 2$ with head $S$ (that is, $j$ never has the shape $S u v$).
- (ii) *Quartic initial leaf bound:* For every clamping-left binary Turing machine $M = (Q, \delta_M)$ and input $w \in \{0,1\}^*$, the closed $S$-term $T_0 = \mathcal{E}_{\mathrm{TM}}(M, w)$ satisfies 
$$
|\mathcal{E}_{\mathrm{TM}}(M, w)| \;\le\; 125{,}000\,N(M, w)^2, \tag{3.4}
$$
 where $N(M,w) = 225|Q|^2 + 390|Q| + 4|w| + 173$.

*Proof.* 
For (i), $\operatorname{ls}(S a (S b j)) = 1 + \operatorname{ls}(S a) = 2$, preventing any root contraction; applying $x$ yields $S a (S b j) x \to_r (a x)(S b j x) \to_S (a x)((b x)(j x))$. For internal generator opening, let $N_1 \equiv T \nu_n$, $N_2 \equiv T N_1 \equiv \nu_{n+2}$, $Q_0 \equiv \nu_m N_2$, and $g \equiv \nu_m N_2 S \equiv G(m, n+2)$. Then $G(m+1, n+2) \equiv (T \nu_m) N_2 S$ reduces in $6$ deterministic steps:

$$
\begin{aligned}
(S S \nu_m)\,N_2\,S &\;\to_S\; (S N_2 Q_0)\,S \;\to_r\; (N_2 S)\,g \;\equiv\; (S S N_1 S)\,g \;\to_S\; \bigl(T(N_1 S)\bigr)\,g \\
  &\;\to_r\; (S g)\bigl((N_1 S) g\bigr) \;\equiv\; (S g)\bigl((S S \nu_n S) g\bigr) \;\to_S\; (S g)\bigl((T(\nu_n S)) g\bigr) \;\to_S\; F\bigl(g, g, (\nu_n S) g\bigr).
\end{aligned}
$$

When $m = 0$, the single preliminary step $G(0, n+2) \equiv (S T T)\,\nu_{n+2}\,S \to_S (T \nu_{n+2})(T \nu_{n+2}) S \equiv G(n+3, n+3)$ reduces to the positive case $(m', n') = (n+2, n+1)$, giving $1 + 6 = 7$ steps. Direct inspection of the $6$ (respectively, $7$) pre-final terms confirms none matches $(S u)(S v w)$, and $(\nu_k S) g$ has left child $\nu_k S$ where $\nu_k \not\equiv S$, so $(\nu_k S) g$ never has the shape $S u v$.

For (ii), induction on $n$ gives $|\nu_n| = 5 + 2n$, $|G(m,n)| = 11 + 2m + 2n$, and $|(\nu_k S)\,G(m,n)| = 17 + 2k + 2m + 2n$. Let $K$ be the number of opened $F$-frames in the layout tree of $\mathrm{Tape}_0$, and let $H$ bound $n_d + h$, where $h$ is the remaining height of the layout tree; since $p_1 = (1,2)$ and each depth step increases $n_d$ by at most $1$, we have $H \le 2 + K$, and structural induction on the layout tree proves $|\mathrm{Tape}_0| \le (2K + 1)(19 + 6H) \le (2K + 1)(31 + 6K)$. Adding $|\nu_1 S| = 8$, $|\beta_1| = 17$, $|\iota_0| = 23$, and the two $S$-leaves of the outer hub frame gives $|T_0| \le 50 + (2K + 1)(31 + 6K)$. In $\mathrm{Tape}_0$, there are $4|u_0|$ binary cells, each containing one initial $11$-bit record, and each $11$-bit record opens at most $2 \cdot 11 + 2 = 24$ frames plus $1$ spine frame per cell, so $K \le (1 + 24) \cdot 4|u_0| = 100|u_0|$. Since $2(100|u_0|) + 1 \le 200(|u_0| + 1)$ and $31 + 600|u_0| \le 600(|u_0| + 1)$, we obtain

$$
|T_0| \;\le\; 50 + 120{,}000(|u_0| + 1)^2 \;\le\; 125{,}000(|u_0| + 1)^2 \;\le\; 125{,}000\,N(M, w)^2,
$$

using Proposition 3.3(i).
 $\square$

### 3.3. Stateless Root-Restarted Zipper Tree-Walking Selector

To ensure that evaluation-order selection retains no hidden memory between pure-$S$ contractions and inspects only bounded local tree neighborhoods, we formalize the selector $\sigma_{\mathrm{TM}}$ as a deterministic root-restarted finite-state tree-walking automaton operating on a Huet zipper [36].

**Definition 3.6 (Zipper cursor and root-restarted finite-state selector $\sigma_{\mathrm{TM}}$).** 
A *zipper cursor* over $\mathcal{T}_S$ is a pair $(f, \gamma)$ consisting of the focused subterm $f \in \mathcal{T}_S$ and a breadcrumb stack $\gamma \in \{\mathsf{L}(R), \mathsf{R}(L) : L, R \in \mathcal{T}_S\}^*$ recording sibling subtrees along the path back to the root, with root cursor $\mathrm{root}(t) = (t, \varepsilon)$ and tree reconstruction $\mathrm{rebuild}(f, \varepsilon) = f$, $\mathrm{rebuild}(f, \mathsf{L}(R)\cdot\gamma) = \mathrm{rebuild}(f R, \gamma)$, and $\mathrm{rebuild}(f, \mathsf{R}(L)\cdot\gamma) = \mathrm{rebuild}(L f, \gamma)$. At each micro-tick, the automaton observes only the $6$-element local observation

$$
\mathrm{obs}(f, \gamma) \;\in\; \{\mathsf{S},\, \mathsf{App}\} \times \{\mathsf{root},\, \mathsf{left},\, \mathsf{right}\},
$$

indicating whether $f \equiv S$ or $f \equiv f_1 f_2$ and whether the top of $\gamma$ is empty, $\mathsf{L}(\_)$, or $\mathsf{R}(\_)$, and issues one of five primitive commands:

$$
\mathsf{moveL}(q'), \qquad \mathsf{moveR}(q'), \qquad \mathsf{moveU}(q'), \qquad \mathsf{contract}, \qquad \mathsf{normal}.
$$

Here $\mathsf{moveL}, \mathsf{moveR}, \mathsf{moveU}$ step one tree edge down-left, down-right, or up to the parent in state $q'$; $\mathsf{contract}$ contracts a root redex $f \equiv S X Y Z \mapsto (X Z)(Y Z)$ at the current focus, rebuilds the tree, and terminates the invocation; and $\mathsf{normal}$ terminates without modifying the tree.

The finite control state space $Q_{\mathrm{ctrl}}$ of $\sigma_{\mathrm{TM}}$ is a loop-free product of bounded finite registers:

- (i) a $23$-state local strict-frame lookahead register probing at most $16$ micro-ticks to verify that a candidate node has shape $F(a,b,j)$ with $\operatorname{ls}(j) \ne 2$ or $j$ not headed by $S$ (enforcing unambiguous frame parsing without false positives from junk subtrees);
- (ii) $11$-bit shift buffers ($\{0,1\}^{\le 11}$) and decoded cell registers $\{0,1\} \times \{\mathsf{off}, \mathsf{active}, \mathsf{movingL}, \mathsf{movingR}\} \times \{0,\dots,255\}$ implementing a two-pass tape scan: *Pass 1* scans the tape spine for any cell in status $\mathsf{movingL}$ or $\mathsf{movingR}$ and completes its neighbor arrival and source reset to $\mathsf{off}$; if none is pending, *Pass 2* locates the unique $\mathsf{active}$ cell $(b, \mathsf{active}, q)$ and consults the fixed $262$-rule table of $U_{\mathrm{bin}}$ (opening the hub halt flag if $(q, b)$ is undefined, or appending the next $11$-bit record, or extending the post-halt left-spine frontier if the halt flag is already open);
- (iii) a $28$-state local generator-opening probe inspecting depth at most $5$ to select the unique next redex of the $6$- or $7$-step sequence of Lemma 3.5(i); and
- (iv) a $10$-state root-ascent and leftmost-redex Euler-tour fallback invoked if any structural guard fails on a malformed input tree.

(Flattening these finite product registers into a single enumerated set yields $|Q_{\mathrm{ctrl}}| = 4{,}376{,}490{,}905$ states.) Every macro-step of $\sigma_{\mathrm{TM}}$ starts fresh at $(q_0, \mathrm{root}(t))$, retaining no state across contractions.

**Lemma 3.7 (Universal node-linear micro-tick termination and soundness).** 
For every closed $S$-term $t \in \mathcal{T}_S$, executing the tree-walking controller of Definition 3.6 from $(q_0, \mathrm{root}(t))$ terminates after $m$ elementary micro-ticks satisfying

$$
1 \;\le\; m \;\le\; 3500\,(2|t| - 1) \;=\; 3500\,\operatorname{nodes}(t), \tag{3.5}
$$

either returning $\sigma_{\mathrm{TM}}(t) = \mathsf{normal}$ (in which case $t \in \mathrm{NF}$) or returning $\sigma_{\mathrm{TM}}(t) = t' \in \mathcal{T}_S$ obtained by contracting a single redex ($t \to_S t'$).

*Proof.* 
If $t \equiv S$, then $|t| = 1$ and $(q_0, \mathrm{root}(S))$ halts in $m = 1 \le 3500(2\cdot 1 - 1)$ micro-tick returning $\mathsf{normal}$. For composite $t \equiv t_1 t_2$ ($|t| \ge 2$, so $|t| + 1 \le 2|t| - 1$), every subroutine of $Q_{\mathrm{ctrl}}$ traverses disjoint subtrees of the current focus without revisiting siblings inside the same pass: each strict-frame lookahead takes at most $16$ micro-ticks and restores the cursor to its entry node; reading or verifying an $11$-bit cell version chain descends along the left spine of committed records (at most $16 + 22\cdot 18$ micro-ticks per record, amortized against the disjoint leaf mass of the record's field subtrees) and ascends to the cell header; Pass 1 and Pass 2 each sweep down the right tape spine at most once, followed by at most one local neighbor step, one version-write descent, and one $5$-edge generator probe before contracting. If any structural invariant fails on an arbitrary non-canonical tree $t$, the controller ascends directly to the root (in at most $|t|$ moves, since breadcrumb length satisfies $|\gamma| < |t|$) and performs a standard depth-first Euler tour tracking left-spine arity in $\{0,1,2,3\}$: every edge of $t$ ($2|t| - 2$ edges) is traversed at most twice (once downward, once upward), halting with $\mathsf{normal}$ at the root if no node reaches left-spine arity $3$, or climbing $3$ edges to contract the first $S X Y Z$ redex encountered. Summing the explicit worst-case phase potentials across Pass 1, root rewind, Pass 2, destination/write traversal, root ascent, and Euler fallback bounds total micro-ticks by $3500(|t| + 1) \le 3500(2|t| - 1)$. Finally, $\mathsf{contract}$ fires only after verifying three consecutive left-child edges above an $S$-leaf, so rebuilding the zipper produces a valid single-step reduct $t \to_S t'$, whereas $\mathsf{normal}$ fires only after a complete redex-free Euler tour.
 $\square$

### 3.4. Minimal 11-State Halting Automaton, Bare-Term Output Readback, and Master Theorem

When $U_{\mathrm{bin}}$ reaches its undefined halting configuration $(41, 1)$ on a compiled term, Pass 2 of $\sigma_{\mathrm{TM}}$ opens the root hub's halt flag from $\beta_1$ to an opened frame $F(\beta_2, \beta_2, \iota_1)$, and all subsequent invocations extend a dedicated post-halt frontier inside the halt flag while leaving $\mathrm{Tape}$ untouched. Thus a bare term $t \in \mathcal{T}_S$ is in a root-halted state ($\mathsf{rootHalt}(t) = 1$) if and only if $t \equiv H_{\mathrm{hdr}} \cdot \mathrm{Hub}$ where $\mathrm{Hub} \equiv F(\mathrm{Flag}, \mathrm{Tape}, j)$ is an opened frame whose left slot $\mathrm{Flag} \equiv F(l, r, j')$ is also an opened frame.

**Proposition 3.8 (Minimal $11$-state halting automaton $\mathcal{H}_{11}$ and bare-term decoder $\mathcal{D}_{\mathrm{TM}}$).** 
Let $L_{\mathrm{halt}} = \{t \in \mathcal{T}_S : \mathsf{rootHalt}(t) = 1\}$.

- (i) *Exact recognition and $11$-state minimality:* The deterministic bottom-up tree automaton $\mathcal{H}_{11} = (\{0,\dots,10\}, 0, \odot_{\mathrm{halt}}, \{3, 6, 8, 10\})$ defined by the $7$-feature vector table in Table 3 satisfies $L(\mathcal{H}_{11}) = L_{\mathrm{halt}}$. Moreover, $\mathcal{H}_{11}$ is the unique minimal deterministic bottom-up tree automaton recognizing $L_{\mathrm{halt}}$ over $\mathcal{T}_S$: no DTA with $10$ or fewer states recognizes $L_{\mathrm{halt}}$.
- (ii) *Linear-time bare-term output decoder:* There exists a read-only structural parser $\mathcal{D}_{\mathrm{TM}} \colon \mathcal{T}_S \rightharpoonup \{0,1\}^*$ terminating in $O(|t|)$ primitive tree operations on every $t \in \mathcal{T}_S$ that inspects neither $M$ nor $w$ and extracts the halted output directly from $\mathrm{Tape}$.

**Table 3.** States, Boolean feature vectors $(\mathsf{s}_0, \mathsf{s}_1, \mathsf{s}_1\mathsf{F}, \mathsf{s}_2, \mathsf{frame}, \mathsf{haltHub}, \mathsf{rootHalt})$, and minimal closed representatives of the $11$-state halting tree automaton $\mathcal{H}_{11}$, where $T \equiv S S$, $A \equiv S S S$, $F_0 \equiv T A$, and $H_0 \equiv (S F_0) A$.

| State $q$ | Feature vector | Accepting | Representative $t_q \in \mathcal{T}_S$ | Syntactic role |
| —: | :—: | :—: | :—: | :— |
| $0$ | $(1,0,0,0,0,0,0)$ | no | $S$ | Atomic leaf $S$ |
| $1$ | $(0,1,0,0,0,0,0)$ | no | $T$ | $S X$ with $X$ not a frame |
| $2$ | $(0,1,1,0,0,0,0)$ | no | $S F_0$ | $S F$ with $F$ a frame, non-halting right child |
| $3$ | $(0,1,1,0,0,0,1)$ | yes | $S H_0$ | $S H$ where $H$ is a halted hub |
| $4$ | $(0,0,0,1,0,0,0)$ | no | $A$ | $(S X) Y$ not of frame shape |
| $5$ | $(0,0,0,1,1,0,0)$ | no | $F_0$ | Frame $F(a,b,j)$ with unopened flag $a$ |
| $6$ | $(0,0,0,1,1,0,1)$ | yes | $T H_0$ | Frame whose right child is a halted hub |
| $7$ | $(0,0,0,1,1,1,0)$ | no | $H_0$ | Halted hub $F(F', b, j)$, non-halting right child |
| $8$ | $(0,0,0,1,1,1,1)$ | yes | $(S F_0) H_0$ | Halted hub whose right child is a halted hub |
| $9$ | $(0,0,0,0,0,0,0)$ | no | $A S$ | Other composite term, non-halting |
| $10$ | $(0,0,0,0,0,0,1)$ | yes | $A H_0$ | Composite root $P H$ with halted hub $H$ |

*Proof.* 
For (i), associate to every $t \in \mathcal{T}_S$ the $7$-tuple $\mathbf{f}(t) = (\mathsf{s}_0, \mathsf{s}_1, \mathsf{s}_1\mathsf{F}, \mathsf{s}_2, \mathsf{frame}, \mathsf{haltHub}, \mathsf{rootHalt}) \in \{0,1\}^7$, where the seven Boolean coordinates hold as follows: $\mathsf{s}_0(t) = 1$ if and only if $t \equiv S$; $\mathsf{s}_1(t) = 1$ if and only if $t \equiv S x$ for some $x$; $\mathsf{s}_1\mathsf{F}(t) = 1$ if and only if $t \equiv S x$ for some $x$ with $\mathsf{frame}(x) = 1$; $\mathsf{s}_2(t) = 1$ if and only if $t \equiv S x y$ for some $x, y$; $\mathsf{frame}(t) = 1$ if and only if $t \equiv (S a)(S b j)$ for some $a, b, j$; $\mathsf{haltHub}(t) = 1$ if and only if $t \equiv (S a)(S b j)$ for some $a, b, j$ with $\mathsf{frame}(a) = 1$; and $\mathsf{rootHalt}(t) = 1$ if and only if $t \equiv p q$ for some $p, q$ with $\mathsf{haltHub}(q) = 1$. For any binary application $l r$, these seven coordinates satisfy the purely compositional law (writing $\land$ for multiplication on $\{0,1\}$)

$$
\mathbf{f}(l r) \;=\; \bigl(0,\; \mathsf{s}_0(l),\; \mathsf{s}_0(l)\land\mathsf{frame}(r),\; \mathsf{s}_1(l),\; \mathsf{s}_1(l)\land\mathsf{s}_2(r),\; \mathsf{s}_1\mathsf{F}(l)\land\mathsf{s}_2(r),\; \mathsf{haltHub}(r)\bigr). \tag{3.6}
$$

Direct inspection verifies that the $11$ vectors listed in Table 3 contain $\mathbf{f}(S) = (1,0,0,0,0,0,0)$, are closed under (3.6) across all $11 \times 11 = 121$ pairs (defining $q_l \odot_{\mathrm{halt}} q_r$), and accept via coordinate $7$ ($\{3,6,8,10\}$), so structural induction shows that $\llbracket t \rrbracket_{\mathcal{H}_{11}} = q$ holds if and only if $\mathbf{f}(t) = \mathbf{v}_q$, establishing $L(\mathcal{H}_{11}) = L_{\mathrm{halt}}$.

To prove $11$-state Myhill–Nerode minimality, first note that all $11$ states are inhabited on $\mathcal{T}_S$ by the explicit closed representatives $t_0, \dots, t_{10}$ in Table 3. Second, using (3.6) with $\mathsf{s}_2(A) = 1$, $\mathsf{frame}(F_0) = 1$, and $\mathsf{s}_1\mathsf{F}(S F_0) = 1$, each of the seven Boolean coordinates of $\mathbf{f}(t)$ is isolated as root acceptance $C_i[t] \in L_{\mathrm{halt}}$ by a fixed closed context $C_i[\square]$:

$$
\begin{aligned}
C_7[\square] &\equiv \square, &
  C_6[\square] &\equiv S\,\square, &
  C_4[\square] &\equiv S\bigl((S F_0)\,\square\bigr), &
  C_3[\square] &\equiv S(\square\,A), \\
  C_5[\square] &\equiv S\bigl((S\,\square)\,A\bigr), &
  C_2[\square] &\equiv S\bigl((S F_0)(\square\,S)\bigr), &
  C_1[\square] &\equiv S\bigl((\square\,F_0)\,A\bigr).
\end{aligned}
$$

Indeed, $C_6[t] \in L_{\mathrm{halt}}$ holds if and only if $\mathsf{haltHub}(t) = 1$; $C_4[t] \in L_{\mathrm{halt}}$ holds if and only if $\mathsf{s}_1\mathsf{F}(S F_0) \land \mathsf{s}_2(t) = 1$, which simplifies to $\mathsf{s}_2(t) = 1$; $C_3[t] \in L_{\mathrm{halt}}$ holds if and only if $\mathsf{s}_1\mathsf{F}(t) \land \mathsf{s}_2(A) = 1$, which simplifies to $\mathsf{s}_1\mathsf{F}(t) = 1$; and $C_5, C_2, C_1$ compose $C_3$ and $C_4$ with $S\,\square$, $\square\,S$, and $\square\,F_0$ to test $\mathsf{frame}(t) = 1$, $\mathsf{s}_1(t) = 1$, and $\mathsf{s}_0(t) = 1$, respectively. Since the $11$ rows of Table 3 are pairwise distinct in $\{0,1\}^7$, any two distinct states $p \ne q$ differ at some coordinate $i \in \{1,\dots,7\}$, so exactly one of $C_i[t_p]$ and $C_i[t_q]$ belongs to $L_{\mathrm{halt}}$. By the Myhill–Nerode theorem for tree languages, every deterministic bottom-up tree automaton recognizing $L_{\mathrm{halt}}$ has at least $11$ states.

For (ii), given $t \in \mathcal{T}_S$, the decoder $\mathcal{D}_{\mathrm{TM}}(t)$ parses $t \equiv H_{\mathrm{hdr}} \cdot F(\mathrm{Flag}, \mathrm{Tape}, j)$, checks $\mathsf{frame}(\mathrm{Flag}) = 1$, walks the right spine of $\mathrm{Tape}$ once to extract the newest committed $11$-bit record of each cell, verifies that no cell has status $\mathsf{movingL}$ or $\mathsf{movingR}$ and that the first $\mathsf{active}$ cell lies at bit index $4 u_{\mathrm{head}} \equiv 0 \pmod 4$, groups the cell data bits into $4$-bit blocks $\mathrm{bin}_4^{-1} \in \Sigma_{11}$ (verifying that cell $u_{\mathrm{head}}$ holds $\delta$ in $u_3$), and applies the single-pass $U_{3,11}$ output scan of Proposition 3.3(ii). Every subterm of $t$ is visited at most once, taking $O(|t|)$ time.
 $\square$

Combining Proposition 3.3, Construction 3.4, Lemmas 3.5 and 3.7, and Proposition 3.8 yields our first main universality theorem.

**Theorem 3.9 (Controlled polynomial-size Turing machine simulation in $\mathrm{CL}(S)$).** 
The quadruple $(\mathcal{E}_{\mathrm{TM}}, \sigma_{\mathrm{TM}}, \mathcal{H}_{11}, \mathcal{D}_{\mathrm{TM}})$ is an ongoing selected-path simulation of all clamping-left deterministic binary Turing machines in $\mathrm{CL}(S)$. Specifically, for every machine $M = (Q, \delta_M)$ and input $w \in \{0,1\}^*$, let $N(M,w) = 225|Q|^2 + 390|Q| + 4|w| + 173$ and $T_0 = \mathcal{E}_{\mathrm{TM}}(M, w) \in \mathcal{T}_S$. Then:

- (i) *Initial size and perpetual single-step trajectory:* $|T_0| \le 125{,}000\,N(M,w)^2$, and iterating $\sigma_{\mathrm{TM}}$ generates an infinite pure-$S$ reduction sequence $T_0 \to_S T_1 \to_S T_2 \to_S \cdots$ ($T_{k+1} = \sigma_{\mathrm{TM}}(T_k)$) in which each step is selected from $(q_0, \mathrm{root}(T_k))$ within $3500(2|T_k|-1)$ micro-ticks and every term satisfies the quadratic trajectory bound 
$$
|T_k| \;\le\; 600{,}000\,\bigl(N(M,w) + k\bigr)^2 \qquad (\text{for all } k \ge 0). \tag{3.7}
$$

- (ii) *Bidirectional halting equivalence and output recovery:* The machine $M$ halts on $w$ if and only if there exists $k \ge 0$ such that $T_k \in L(\mathcal{H}_{11})$; moreover, whenever $M$ halts on $w$, every $k \ge 0$ with $T_k \in L(\mathcal{H}_{11})$ satisfies $\mathcal{D}_{\mathrm{TM}}(T_k) = \operatorname{out}_M(w)$.

*Proof.* 
By Lemma 3.5(ii) and Lemma 3.7, $|T_0| \le 125{,}000\,N(M,w)^2$ and each invocation of $\sigma_{\mathrm{TM}}$ halts in at most $3500(2|T_k|-1)$ micro-ticks. On every reachable term from $T_0$, the strict-frame invariant holds throughout the hub, so the local $16$-tick frame checks of $\sigma_{\mathrm{TM}}$ agree identically with structural frame parsing. Each binary transition of $U_{\mathrm{bin}}$ adds at most $1$ new tape cell and at most $3$ committed $11$-bit cell records (for moving source, arrival destination, and source reset), so after $t$ binary transitions of $U_{\mathrm{bin}}$, the opened-frame count satisfies $K_t \le 100(|u_0| + t)$ and the checkpoint term size is at most $125{,}000(|u_0| + t + 1)^2$. Because every pure-$S$ contraction has non-decreasing leaf count by Proposition 2.2(ii), any intermediate term $T_k$ along a $6$- or $7$-step generator opening is bounded in leaf size by the next macro-boundary checkpoint: if $U_{\mathrm{bin}}$ runs for $k+1$ binary transitions without halting, we have $K \le 100(|u_0| + k + 1)$ and $(|u_0| + k + 2)^2 \le 4(|u_0| + k + 1)^2 \le 4(N(M,w) + k)^2$, giving $|T_k| \le 4 \cdot 125{,}000(N(M,w)+k)^2 = 500{,}000(N(M,w)+k)^2$; if $U_{\mathrm{bin}}$ halts at binary step $t_{\mathrm{halt}} \le k$, the tape freezes at size at most $500{,}000(N(M,w)+k)^2$ while at most $k+1$ post-halt frontier openings contribute at most $800(N(M,w)+k)^2 + 33$ leaves, yielding $|T_k| \le 600{,}000(N(M,w)+k)^2$ in all cases.

For (ii), while $U_{\mathrm{bin}}$ executes defined transitions, $\mathrm{Flag} \equiv \beta_1$ remains unopened, so $T_k \notin L(\mathcal{H}_{11})$. Constructive bounded evaluation of $U_{\mathrm{bin}}$ shows that $U_{\mathrm{bin}}$ halts on $\mathcal{E}_{\mathrm{bin}}(u_0)$ if and only if some $T_k$ opens $\mathrm{Flag}$ and enters $L(\mathcal{H}_{11})$. By the $10$-step defined / $6$-step halting refinement between $U_{3,11}$ and $U_{\mathrm{bin}}$ (Construction 3.4) and Proposition 3.3(ii), this holds if and only if $M$ halts on $w$. At the halting boundary $u_{\mathrm{fin}} = (u_3, \delta)$ of $U_{3,11}$, the $6$-step rewind of $U_{\mathrm{bin}}$ leaves the active head aligned at bit $4 h(u_{\mathrm{fin}})$ with no pending moves and all $4$-bit symbol blocks intact; since post-halt steps modify only $\mathrm{Flag}$, every $T_k \in L(\mathcal{H}_{11})$ decodes under $\mathcal{D}_{\mathrm{TM}}$ to $u_{\mathrm{fin}}$ modulo trailing blanks and hence to $\operatorname{out}_M(w)$.
 $\square$

*Remark 3.10 (Sub-universal complexity and concrete compiled sizes).* 
Formatting $\mathcal{E}_U(M,w)$ requires only $O(\log(|Q| + |w|))$ workspace [44], and expanding $u_0$ into the unshared syntax tree $T_0 = \mathcal{E}_{\mathrm{TM}}(M,w)$ is a deterministic uniform block substitution running in time linear in $|T_0|$, while $\mathcal{H}_{11}$ is an $11$-state finite tree automaton and $\mathcal{D}_{\mathrm{TM}}$ runs in read-only time $O(|T_k|)$. In concrete evaluations, compiling the $1$-state halting Turing machine on the empty input ($|Q|=1, |w|=0$, where $|u_0| = 540$ versus the upper bound $N = 788$) produces an explicit pure-$S$ tree of $1{,}996{,}921$ leaves; compiling a $2$-state write-$1$ machine produces $7{,}477{,}337$ leaves; and simulating the $2$-state Busy Beaver executes $912$ pure-$S$ contractions to enter $L(\mathcal{H}_{11})$ and output $1111$, contrasting with the unmaterializable seeds of at least $2^{57207}$ bits required by unary counter/tag pipelines [26].

## 4. Program-Free Cyclic Tag Simulation and Genesis from the Ten-Leaf Seed

In Section 3, the root-restarted selector $\sigma_{\mathrm{TM}}$ incorporates the fixed $262$-rule binary transition table of $U_{\mathrm{bin}}$ inside its finite control. One naturally asks whether this embedded universal transition table can be eliminated altogether, so that both the simulated program and its data reside inside the closed $S$-term while a single program-free selector executes arbitrary computations purely by structural manipulation of $\mathcal{T}_S$. Here we answer this question affirmatively via cyclic tag systems [17] and prove that every encoded instance unfolds by pure-$S$ reduction from a single $10$-leaf combinator $D_{\mathrm{seed}}$.

### 4.1. Cyclic Tag Systems and Self-Describing Pure-$S$ Queue Encoding

Introduced by Cook [17] as a binary refinement of Post's canonical and tag systems [47, 49] and Minsky and Cocke's universal $2$-tag machines [41, 16], and later shown by Woods and Neary [73] to simulate Turing machines with polynomial time overhead, cyclic tag systems dispense with explicit control states in favor of a cyclically rotating ring of binary appendants.

**Definition 4.1 (Cyclic tag systems).** 
A *cyclic tag system* (CTS) is a nonempty finite tuple $P = (A_0, A_1, \dots, A_{m-1})$ of $m \ge 1$ binary words $A_i \in \{0,1\}^*$, called *appendants*. A configuration of $P$ is a pair $(i, u) \in \{0, \dots, m-1\} \times \{0,1\}^*$ consisting of the active phase index $i$ and the FIFO data queue $u$. On initial word $w \in \{0,1\}^*$, execution begins at $(0, w)$ and evolves deterministically according to

$$
(i,\, \varepsilon) \;\text{halts}, \qquad
  (i,\, 0\cdot u') \;\vdash_P\; \bigl((i + 1) \bmod m,\, u'\bigr), \qquad
  (i,\, 1\cdot u') \;\vdash_P\; \bigl((i + 1) \bmod m,\, u'\cdot A_i\bigr).
$$

We write $\|(P, w)\| := m + \sum_{j=0}^{m-1} |A_j| + |w|$ for the total bit-and-phase description length of $(P, w)$.

Because pure-$S$ reduction cannot erase consumed queue cells or reset template bits destructively, our self-describing encoding equips every phase header, appendant template bit, and queue bit with an append-only version chain inside protected $F$-frames.

**Construction 4.2 (Self-describing pure-$S$ CTS encoding $\mathcal{E}_{\mathrm{CTS}}$).** 
Retaining the protected frame $F(a,b,j) \equiv S a(S b j)$, counter generators $\beta_d \equiv G(m_d, n_d)$, junk terms $\iota_d$, and width-$r$ version chains of Construction 3.4, define the following status codes:

- (i) *$2$-bit phase status codes:* $\mathtt{00}$ ($\mathsf{inactive}$), $\mathtt{10}$ ($\mathsf{active}$), and $\mathtt{11}$ ($\mathsf{handoff}$).
- (ii) *$3$-bit appendant template codes, for template bit $s \in \{0,1\}$:* $\mathtt{00}s$ ($\mathsf{idle}$), $\mathtt{10}s$ ($\mathsf{armed}$), and $\mathtt{11}s$ ($\mathsf{appending}$).
- (iii) *$3$-bit queue cell codes, for data bit $b \in \{0,1\}$:* $\mathtt{01}b$ ($\mathsf{staging}$), $\mathtt{00}b$ ($\mathsf{unconsumed}$), $\mathtt{10}b$ ($\mathsf{consuming}$), and $\mathtt{11}b$ ($\mathsf{consumed}$).

Given $P = (A_0, \dots, A_{m-1})$ and $w \in \{0,1\}^*$:

- Each appendant $A_j = s_{j,1}\cdots s_{j,\ell_j}$ is encoded as a right-spine $F$-list of $\ell_j$ width-$3$ version chains initialized to $[\mathtt{00}s_{j,r}]$ ($\mathsf{idle}$) and terminated by $\beta_{4+j+\ell_j}$; each phase $j \in \{0,\dots,m-1\}$ pairs a width-$2$ status chain (initialized to $[\mathtt{10}]$ for $j = 0$ and $[\mathtt{00}]$ for $j > 0$) with its template list inside $F(-,-,\iota_{3+j})$, chained along the right spine (terminated by $\beta_{2+m}$) to form $\mathrm{Ring}_0$ at base depth $d = 2$.
- The initial queue $w = b_1\cdots b_{|w|}$ is encoded at base depth $d = 2$ as a right-spine $F$-list $\mathrm{Queue}_0$ of $|w|$ width-$3$ version chains initialized to $[\mathtt{00}b_r]$ ($\mathsf{unconsumed}$), terminated by $\beta_{2+|w|}$.
- Combining the unopened halt flag $\beta_1$ at path $[1,0,1]$ with the payload pair $F(\mathrm{Ring}_0, \mathrm{Queue}_0, \iota_1)$ yields the closed $S$-term 
$$
\mathcal{E}_{\mathrm{CTS}}(P, w) \;\equiv\; (\nu_1\,S)\,F\Bigl(\beta_1,\; F\bigl(\mathrm{Ring}_0,\, \mathrm{Queue}_0,\, \iota_1\bigr),\; \iota_0\Bigr), \tag{4.1}
$$
 whose total leaf count satisfies $|\mathcal{E}_{\mathrm{CTS}}(P,w)| \le 2500\,\bigl(\|(P,w)\| + 1\bigr)^2$.

Indeed, each initial width-$2$ record opens at most $6$ frames ($+2$ phase-spine frames per phase), and each initial width-$3$ template or queue record opens at most $8$ frames ($+1$ list frame), plus $2$ outer hub frames, giving $K_0 \le 2 + 8m + 9\sum |A_j| + 9|w| \le 2 + 9\|(P,w)\|$ opened frames and height $H_0 \le 4 + 9\|(P,w)\|$. By the layout leaf bound of Lemma 3.5(ii),

$$
|\mathcal{E}_{\mathrm{CTS}}(P,w)| \;\le\; 8 + (2K_0 + 1)(19 + 6H_0) \;\le\; 8 + 23(\|(P,w)\|+1)\cdot 97(\|(P,w)\|+1) \;\le\; 2500\bigl(\|(P,w)\|+1\bigr)^2.
$$

### 4.2. Program-Free Bare-Term Selector and Ten-Leaf Seed Genesis

Because both $\mathrm{Ring}_0$ and $\mathrm{Queue}_0$ are embedded inside $\mathcal{E}_{\mathrm{CTS}}(P,w)$, a single fixed selector $\sigma_{\mathrm{CTS}}$ can execute arbitrary cyclic tag systems without holding any CTS or UTM parameters in its own definition.

**Definition 4.3 (Program-free selector $\sigma_{\mathrm{CTS}}$ and bare-term decoder $\mathcal{D}_{\mathrm{CTS}}$).** 
The *program-free selector* $\sigma_{\mathrm{CTS}} \colon \mathcal{T}_S \to \mathcal{T}_S \cup \{\mathsf{halt}, \mathsf{stuck}\}$ inspects only a bare term $t \in \mathcal{T}_S$:

- (i) If $t \in L_{\mathrm{halt}}$ (recognized by the $11$-state automaton $\mathcal{H}_{11}$ of Proposition 3.8), return $\mathsf{halt}$.
- (ii) Otherwise, parse $t \equiv H_{\mathrm{hdr}} \cdot F(\mathrm{Flag}, F(\mathrm{Ring}, \mathrm{Queue}, j_1), j_0)$, scan the newest committed $2$-bit status of each phase in $\mathrm{Ring}$ and its $3$-bit template statuses, and scan $\mathrm{Queue}$ to locate the first $\mathsf{consuming}$ cell ($\mathtt{10}b$), first $\mathsf{unconsumed}$ cell ($\mathtt{00}b$), first $\mathsf{staging}$ cell ($\mathtt{01}s$), or any freshly opened uninitialized tail slot: - *Handoff completion:* If some phase $j$ has status $\mathsf{handoff}$ ($\mathtt{11}$), then if a queue cell is $\mathsf{consuming}$ ($\mathtt{10}b$), append record $\mathtt{11}b$ ($\mathsf{consumed}$) to it; else if $m = 1$, append $\mathtt{10}$ ($\mathsf{active}$) to phase $0$; else if phase $j' = (j+1) \bmod m$ is not yet $\mathtt{10}$, append $\mathtt{10}$ to phase $j'$, and once phase $j'$ is $\mathtt{10}$, append $\mathtt{00}$ ($\mathsf{inactive}$) to phase $j$.
- *Active phase dispatch:* If no phase is in $\mathsf{handoff}$ and phase $j$ is $\mathsf{active}$ ($\mathtt{10}$): - (a) When no queue cell is $\mathsf{consuming}$: if no $\mathsf{unconsumed}$ cell exists, open the halt flag $\mathrm{Flag}$ at path $[1,0,1]$; else if the front $\mathsf{unconsumed}$ cell holds bit $b = 0$, append $\mathtt{100}$ ($\mathsf{consuming}$); else ($b = 1$) if phase $j$ still has an $\mathsf{idle}$ template ($\mathtt{00}s$), append $\mathtt{10}s$ ($\mathsf{armed}$) to the first $\mathsf{idle}$ template, and once all templates of phase $j$ are $\mathsf{armed}$, append $\mathtt{101}$ ($\mathsf{consuming}$) to the front queue cell.
- (b) When a queue cell is $\mathsf{consuming}$ ($\mathtt{10}b$): if a template is $\mathsf{appending}$ ($\mathtt{11}s$), first open the queue tail if needed, then write $\mathtt{01}s$ ($\mathsf{staging}$) into the new tail cell, and once $\mathtt{01}s$ is committed, reset the $\mathsf{appending}$ template to $\mathtt{00}s$ ($\mathsf{idle}$); if no template is $\mathsf{appending}$ and a queue cell is $\mathsf{staging}$ ($\mathtt{01}s$), commit it to $\mathtt{00}s$ ($\mathsf{unconsumed}$); else if an $\mathsf{armed}$ template ($\mathtt{10}s$) remains, advance the first $\mathsf{armed}$ template to $\mathtt{11}s$ ($\mathsf{appending}$); else, with all templates $\mathsf{idle}$ and the queue clean, advance phase $j$ to $\mathtt{11}$ ($\mathsf{handoff}$).
- (iii) Having chosen either a target generator slot to open or a target version chain to extend by one bit, apply the $5$-edge local opening probe of Lemma 3.5(i) to contract the unique next redex $t \to_S t'$.

The companion *bare-term CTS decoder* $\mathcal{D}_{\mathrm{CTS}} \colon \mathcal{T}_S \rightharpoonup \mathbb{N} \times \{0,1\}^*$ checks that neither $\mathrm{Flag}$ nor any phase or queue version chain is mid-opening, verifies that a unique phase $i$ has status $\mathtt{10}$ with all others $\mathtt{00}$, skips $\mathsf{consumed}$ ($\mathtt{11}b$) queue cells, and collects $\mathsf{unconsumed}$ ($\mathtt{00}b$) cells to return $(i, u)$.

Before proving universal simulation, we establish a structural property unique to duplicative combinatory rewriting: every encoded CTS instance $\mathcal{E}_{\mathrm{CTS}}(P,w)$ (and indeed every finite protected-frame layout, including $\mathcal{E}_{\mathrm{TM}}(M,w)$) is generated via pure-$S$ reduction from a single fixed $10$-leaf combinator.

**Proposition 4.4 (Universal genesis from the ten-leaf seed).** 
Define the $10$-leaf closed $S$-term

$$
D_{\mathrm{seed}} \;\equiv\; S\bigl(S(S S)\bigr)\bigl(S(S S)\bigr)(S S)\,S \;\equiv\; S B B T S. \tag{4.2}
$$

For every cyclic tag system $P$ and every input word $w \in \{0,1\}^*$, there is an explicit pure-$S$ reduction sequence $D_{\mathrm{seed}} \to_S^* \mathcal{E}_{\mathrm{CTS}}(P, w)$.

*Proof.* 
First, $|D_{\mathrm{seed}}| = 1 + 3 + 3 + 2 + 1 = 10$, and $D_{\mathrm{seed}}$ bootstraps in $5$ pure-$S$ contractions to the universal root generator $(\nu_1 S)\,G(2,2)$ (recall $\nu_0 \equiv B T \equiv S T T$, $\nu_1 \equiv T \nu_0$, $\nu_2 \equiv T \nu_1$):

$$
\begin{aligned}
D_{\mathrm{seed}} &\;\equiv\; (S B B T)\,S \;\to_S\; \bigl((B T)(B T)\bigr)\,S \;\equiv\; \nu_0\,\nu_0\,S \;\equiv\; G(0,0) \\
  &\;\equiv\; (S T T \nu_0)\,S \;\to_S\; \bigl((T \nu_0)(T \nu_0)\bigr)\,S \;\equiv\; \nu_1\,\nu_1\,S \;\equiv\; G(1,1) \\
  &\;\equiv\; (S S \nu_0 \nu_1)\,S \;\to_S\; \bigl(S \nu_1 (\nu_0 \nu_1)\bigr)\,S \;\to_r\; (\nu_1 S)\,(\nu_0 \nu_1 S) \\
  &\;\equiv\; (\nu_1 S)\,\bigl((S T T \nu_1)\,S\bigr) \;\to_S\; (\nu_1 S)\,\bigl((T \nu_1)(T \nu_1)\,S\bigr) \;\equiv\; (\nu_1 S)\,G(2, 2).
\end{aligned}
$$

Second, let $\Lambda$ range over finite binary layout skeletons generated by $\Lambda ::= \mathsf{unopened} \mid \mathsf{opened}(\Lambda_1, \Lambda_2)$, where $\mathrm{Term}(\mathsf{unopened}, m, n) \equiv G(m,n)$ and $\mathrm{Term}(\mathsf{opened}(\Lambda_1,\Lambda_2), m, n)$ recursively places $\mathrm{Term}(\Lambda_1, m', n')$ and $\mathrm{Term}(\Lambda_2, m', n')$ into the left and right slots of $F(-,-,j)$ using the phase transition $(m,n) \mapsto (m',n')$ of Construction 3.4. We prove by structural induction on $\Lambda$ that $G(m,n) \to_S^* \mathrm{Term}(\Lambda, m, n)$ for all $m, n \in \mathbb{N}$ with $2 \le n$ and $m \le n$. The base case $\Lambda = \mathsf{unopened}$ is reflexive. For $\Lambda = \mathsf{opened}(\Lambda_1, \Lambda_2)$, Lemma 3.5(i) gives $G(m,n) \to_S^6 F(G(m',n'), G(m',n'), j)$ (if $m \ge 1$) or $G(m,n) \to_S^7 F(G(m',n'), G(m',n'), j)$ (if $m = 0$), with $2 \le n'$ and $m' \le n'$. Because $\to_S^*$ is congruent inside both $a$ and $b$ of $F(a,b,j) \equiv (S a)(S b j)$, applying the induction hypotheses $G(m',n') \to_S^* \mathrm{Term}(\Lambda_1, m', n')$ on the left and $G(m',n') \to_S^* \mathrm{Term}(\Lambda_2, m', n')$ on the right yields $G(m,n) \to_S^* \mathrm{Term}(\mathsf{opened}(\Lambda_1,\Lambda_2), m, n)$. By Construction 4.2, $\mathcal{E}_{\mathrm{CTS}}(P,w) \equiv (\nu_1 S)\,\mathrm{Term}(\Lambda_{P,w}, 2, 2)$ for an explicit finite layout $\Lambda_{P,w}$, whence $D_{\mathrm{seed}} \to_S^5 (\nu_1 S)\,G(2,2) \to_S^* \mathcal{E}_{\mathrm{CTS}}(P,w)$.
 $\square$

**Theorem 4.5 (Program-free cyclic tag universality in $\mathrm{CL}(S)$).** 
For every cyclic tag system $P = (A_0, \dots, A_{m-1})$ and every input word $w \in \{0,1\}^*$, let $T_0 = \mathcal{E}_{\mathrm{CTS}}(P, w) \in \mathcal{T}_S$.

- (i) *Single-step soundness and all-step quadratic leaf bound:* Whenever $\sigma_{\mathrm{CTS}}(t) = t' \in \mathcal{T}_S$, one has $t \to_S t'$. Along any $k$-step trajectory $T_0 \to_S T_1 \to_S \cdots \to_S T_k$ generated by iterating $\sigma_{\mathrm{CTS}}$, every term $T_k$ satisfies 
$$
|T_k| \;\le\; 35{,}000\,\bigl(\|(P,w)\| + k + 1\bigr)^2. \tag{4.3}
$$

- (ii) *Bidirectional halting equivalence via $\mathcal{H}_{11}$ and terminal readback:* The cyclic tag system $P$ starting from $(0, w)$ eventually halts (empties its queue) if and only if there exists $k \ge 0$ such that $\sigma_{\mathrm{CTS}}^k(T_0) = T_k \in L(\mathcal{H}_{11})$, where $\mathcal{H}_{11}$ is the identical $11$-state bottom-up halting automaton of Proposition 3.8. Moreover, for that unique halting step $k$, $(0, w) \vdash_P^* (i_{\mathrm{fin}}, \varepsilon)$ holds and $\mathcal{D}_{\mathrm{CTS}}(T_k) = (i_{\mathrm{fin}}, \varepsilon)$.

*Proof.* 
Single-step soundness in (i) holds because every non-halting step of $\sigma_{\mathrm{CTS}}$ contracts a single verified redex $S X Y Z \to_r (X Z)(Y Z)$ located by Lemma 3.5(i). To verify step-for-step CTS simulation, maintain the invariant $\mathrm{Rep}_P(i, u)$ stating that $\mathrm{Flag} \equiv \beta_1$, phase $i$ has newest status $\mathtt{10}$ with all $|A_i|$ templates $\mathtt{00}s$ ($\mathsf{idle}$), all other phases $j \ne i$ have newest status $\mathtt{00}$ with all templates $\mathtt{00}s$, and $\mathrm{Queue}$ consists of a prefix of $\mathsf{consumed}$ ($\mathtt{11}b$) cells followed by $|u|$ queue cells with status $\mathsf{unconsumed}$ ($\mathtt{00}b$) matching $u$. Clearly $T_0$ satisfies $\mathrm{Rep}_P(0, w)$ and $\mathcal{D}_{\mathrm{CTS}}(T_0) = (0, w)$.

Suppose $T$ satisfies $\mathrm{Rep}_P(i, u)$. Because appending a width-$r$ version record opens between $1$ and $2r + 2$ layout slots (each taking $6$ or $7$ contractions while leaving the scanned committed value unchanged until the final sentinel slot opens), appending a $2$-bit phase record takes between $6$ and $42$ contractions (at most $6$ opened slots) and appending a $3$-bit cell or template record takes between $6$ and $56$ contractions (at most $8$ opened slots):

- If $u = \varepsilon$, rule (ii)(a) opens $\mathrm{Flag}$ at $[1,0,1]$ in $6$ or $7$ steps to $T_{\mathrm{halt}} \in L(\mathcal{H}_{11})$, after which $\sigma_{\mathrm{CTS}}(T_{\mathrm{halt}}) = \mathsf{halt}$ and $\mathcal{D}_{\mathrm{CTS}}(T_{\mathrm{halt}}) = (i, \varepsilon)$.
- If $u = 0\cdot u'$, rule (ii)(a) marks the front cell $\mathtt{100}$ ($\mathsf{consuming}$), advances phase $i$ to $\mathtt{11}$ ($\mathsf{handoff}$), marks the consuming cell $\mathtt{110}$ ($\mathsf{consumed}$), and activates $(i+1) \bmod m$ to $\mathtt{10}$ (deactivating $i$ to $\mathtt{00}$ if $m \ge 2$), reaching $\mathrm{Rep}_P((i+1) \bmod m, u')$ in $k_{\mathrm{step}} \ge 24$ contractions while adding at most $8 + 26 = 34$ opened slots.
- If $u = 1\cdot u'$, rule (ii)(a) first arms all $|A_i|$ templates ($\mathtt{10}s$, adding $8|A_i|$ slots), then marks the front cell $\mathtt{101}$ ($\mathsf{consuming}$, adding $8$ slots); rule (ii)(b) then copies each bit $s$ of $A_i$ in order via the $5$-part handshake ($\mathtt{11}s \to \text{open queue tail} \to \mathtt{01}s \to \mathtt{00}s\text{ template} \to \mathtt{00}s\text{ queue}$, taking at least $30$ contractions and $33$ slots per bit), and executes the same handoff ($26$ slots) to reach $\mathrm{Rep}_P((i+1)\bmod m, u'\cdot A_i)$ in $k_{\mathrm{step}} \ge 24 + 36|A_i|$ contractions while adding $34 + 41|A_i| \le 34 + 41\|(P,w)\|$ slots (and at most $2 k_{\mathrm{step}}$ slots).

Because no intermediate term inside a macro-step has an opened $\mathrm{Flag}$, $T_k \notin L(\mathcal{H}_{11})$ prior to queue exhaustion; constructive bounded evaluation of $P$ for $k + 1$ steps combines with determinism of $\sigma_{\mathrm{CTS}}$ to show that $(0, w) \vdash_P^* (i_{\mathrm{fin}}, \varepsilon)$ holds if and only if $T_k \in L(\mathcal{H}_{11})$ for some $k \ge 0$. Moreover, every $T_k$ is a prefix of a checkpoint term with at most $K \le (2 + 9\|(P,w)\|) + 2k + 34 + 41\|(P,w)\| \le 50(\|(P,w)\| + k + 1)$ opened slots and height $H \le 2 + 50(\|(P,w)\| + k + 1)$; monotone leaf growth gives

$$
|T_k| \;\le\; 8 + 101(\|(P,w)\|+k+1)\cdot 331(\|(P,w)\|+k+1) \;=\; 8 + 33{,}431\bigl(\|(P,w)\|+k+1\bigr)^2 \;\le\; 35{,}000\bigl(\|(P,w)\|+k+1\bigr)^2.
$$

$\square$

## 5. The Locus of Control: Leaf-Splitting Separation and Multiway Impossibility Theorems

Theorems 3.9 and 4.5 establish universal computation along pure-$S$ trajectories selected by root-restarted walkers. To isolate the respective contributions of external step selection and combinatory duplication, we prove three complementary separation and impossibility theorems.

### 5.1. Leaf-Splitting Universality Under Root-Restarted Selection

We first isolate the computational power of the root-restarted finite-state tree-walking control discipline itself by replacing $\mathrm{CL}(S)$ with a minimal non-erasing binary-tree rewrite system: unary leaf splitting, which performs neither subtree duplication nor higher-arity interaction.

**Definition 5.1 (Unary leaf-splitting system and $3$-state halting automaton).** 
Let $\mathcal{T}_{\mathrm{bin}}$ be the set of unlabeled finite full binary trees generated by $t ::= \mathsf{Leaf} \mid \mathsf{Node}(t_1, t_2)$, with leaf count $|\mathsf{Leaf}|_{\mathrm{leaf}} = 1$ and $|\mathsf{Node}(t_1,t_2)|_{\mathrm{leaf}} = |t_1|_{\mathrm{leaf}} + |t_2|_{\mathrm{leaf}}$. Define single-step *leaf-splitting reduction* $\to_{\mathrm{sp}}$ as the contextual closure of the sole local rule

$$
\mathsf{Leaf} \;\to_{\mathrm{sp}}\; \mathsf{Node}(\mathsf{Leaf},\, \mathsf{Leaf}). \tag{5.1}
$$

Every step $t \to_{\mathrm{sp}} t'$ satisfies $|t'|_{\mathrm{leaf}} = |t|_{\mathrm{leaf}} + 1$. A *root-restarted finite-state tree-walking selector* over $(\mathcal{T}_{\mathrm{bin}}, \to_{\mathrm{sp}})$ is a finite control set $Q_{\mathrm{walk}}$ with start state $q_{\mathrm{init}}$ and transition function

$$
\delta_{\mathrm{walk}} \colon Q_{\mathrm{walk}} \times \{\mathsf{true}, \mathsf{false}\} \times \{\mathsf{root}, \mathsf{leftChild}, \mathsf{rightChild}\} \;\longrightarrow\; \mathsf{downL}(Q_{\mathrm{walk}}) \cup \mathsf{downR}(Q_{\mathrm{walk}}) \cup \mathsf{up}(Q_{\mathrm{walk}}) \cup \{\mathsf{split},\, \mathsf{halt}\},
$$

which starts at $(q_{\mathrm{init}}, t, \varepsilon)$, moves a Huet zipper one edge at a time based solely on whether the focused subtree is $\mathsf{Leaf}$ and which child edge leads to its parent, and upon executing $\mathsf{split}$ at a focused $\mathsf{Leaf}$ replaces that leaf by $\mathsf{Node}(\mathsf{Leaf},\mathsf{Leaf})$ and resets its control state to $(q_{\mathrm{init}}, t', \varepsilon)$.

Define the $3$-state deterministic bottom-up tree automaton $\mathcal{H}_3 = (\{s_{\mathrm{L}}, s_{\mathrm{N}}, s_{\mathrm{acc}}\}, s_{\mathrm{L}}, \odot_3, \{s_{\mathrm{acc}}\})$ on $\mathcal{T}_{\mathrm{bin}}$ by $s_{\mathrm{L}} \odot_3 y = s_{\mathrm{N}}$ and $x \odot_3 y = s_{\mathrm{acc}}$ for $x \in \{s_{\mathrm{N}}, s_{\mathrm{acc}}\}$, so that $L(\mathcal{H}_3) = \{\mathsf{Node}(\mathsf{Node}(a,b), r) : a, b, r \in \mathcal{T}_{\mathrm{bin}}\}$.

**Theorem 5.2 (Controller-complexity separation via leaf splitting).** 
There exist a linear-size initial tree encoder $\mathcal{E}_{\mathrm{sp}}$ and a fixed root-restarted finite-state tree-walking selector $\sigma_{\mathrm{sp}}$ over $(\mathcal{T}_{\mathrm{bin}}, \to_{\mathrm{sp}})$ simulating the $132$-state universal binary Turing machine $U_{\mathrm{bin}}$ (and hence every deterministic Turing machine) with exact bidirectional halting equivalence: for every initial configuration $c_0$ of $U_{\mathrm{bin}}$, $U_{\mathrm{bin}}$ halts from $c_0$ if and only if the root-restarted leaf-splitting trajectory $B_0 = \mathcal{E}_{\mathrm{sp}}(c_0)$, $B_{k+1} = \sigma_{\mathrm{sp}}(B_k)$ with $B_k \to_{\mathrm{sp}} B_{k+1}$ reaches some $B_k \in L(\mathcal{H}_3)$.

*Proof.* 
Encode the $4$-status cell alphabet of $U_{\mathrm{bin}}$—consisting of $\mathsf{off}(b)$, $\mathsf{active}(b, q)$, $\mathsf{movingR}(b, q)$, and $\mathsf{movingL}(b, q)$ for $b \in \{0,1\}$ and $q \in \{0,\dots,131\}$—into the $1056$-element integer range $c \in \{0,\dots,1055\}$ via $\mathsf{off}(0) \mapsto 0$, $\mathsf{off}(1) \mapsto 1$, and $\mathsf{tag}(b,q) \mapsto \mathrm{tag} + 8q$ for $\mathrm{tag} \in \{2,\dots,7\}$. Represent any natural number $m \in \mathbb{N}$ by the right-leaning unary spine $U_0 = \mathsf{Leaf}$, $U_{m+1} = \mathsf{Node}(\mathsf{Leaf}, U_m)$. A *committed cell record* with code $c$ followed by version tail $\mathrm{rest} \in \mathcal{T}_{\mathrm{bin}}$ is the tree

$$
\mathrm{Rec}(c, \mathrm{rest}) \;:=\; \mathsf{Node}\Bigl(\mathsf{Node}\bigl(\mathsf{Node}(\mathsf{Leaf},\mathsf{Leaf}),\, U_c\bigr),\; \mathrm{rest}\Bigr),
$$

whose commit flag (the left child of the inner payload pair) is the composite node $\mathsf{Node}(\mathsf{Leaf},\mathsf{Leaf})$. A cell with history $[c_1, \dots, c_r]$ and uncommitted tail $\tau$ is $\mathrm{Cell}([c_1,\dots,c_r], \tau) = \mathrm{Rec}(c_1, \dots \mathrm{Rec}(c_r, \tau)\dots)$, chained along a right-leaning tape spine $\mathrm{Tape} = \mathsf{Node}(\mathrm{Cell}_0, \mathsf{Node}(\mathrm{Cell}_1, \dots \mathsf{Leaf}))$, under a global root $\mathsf{Node}(\mathrm{Flag}, \mathrm{Tape})$ with $\mathrm{Flag} = \mathsf{Leaf}$ while active (so $\mathsf{Node}(\mathsf{Leaf}, \mathrm{Tape}) \notin L(\mathcal{H}_3)$).

Appending a new committed code $c \in \{0,\dots,1055\}$ to a clean cell tail $\tau = \mathsf{Leaf}$ involves no subtree duplication and executes atomically across $c + 3$ root-restarted leaf splits while preserving the previously committed value on all $c + 2$ intermediate steps:

- (i) *Record-box allocation (split $1$):* $\tau = \mathsf{Leaf} \to_{\mathrm{sp}} \mathsf{Node}(\mathsf{Leaf}, \mathsf{Leaf})$ (uncommitted: inner left child is $\mathsf{Leaf}$).
- (ii) *Staging-pair allocation (split $2$):* split the left child to obtain $\mathsf{Node}(\mathsf{Node}(\mathsf{Leaf}, U_0), \mathsf{Leaf})$ (staging count $m = 0$; commit flag is still $\mathsf{Leaf}$).
- (iii) *Unary payload countdown (splits $3$ through $c+2$, empty when $c = 0$):* on each invocation, $\sigma_{\mathrm{sp}}$ walks down the uncommitted staging spine $U_m$ incrementing a bounded counter in $\{0,\dots,1055\}$; while $m < c$, it splits the terminal $\mathsf{Leaf}$ of $U_m$ to produce $U_{m+1}$ and resets to the root. Because the commit flag remains $\mathsf{Leaf}$, every read pass skips the uncommitted tail and still reads $c_r$.
- (iv) *Atomic commit (split $c+3$):* when the walk reaches the end of $U_m$ with $m = c$, $\sigma_{\mathrm{sp}}$ ascends to the staging pair and splits its left-child commit flag $\mathsf{Leaf} \to_{\mathrm{sp}} \mathsf{Node}(\mathsf{Leaf},\mathsf{Leaf})$, turning the tail into $\mathrm{Rec}(c, \mathsf{Leaf})$ in a single step.

Equipped with this $(c+3)$-split atomic write primitive (plus a $1$-split right-tape extension when $\mathsf{movingR}$ reaches the tape sentinel $\mathsf{Leaf}$), $\sigma_{\mathrm{sp}}$ executes the same two-pass priority simulation of $U_{\mathrm{bin}}$ as $\sigma_{\mathrm{TM}}$: Pass 1 completes any $\mathsf{movingR}$ or $\mathsf{movingL}$ handshake, and Pass 2 steps the unique $\mathsf{active}$ cell—or, when $\delta_{U_{\mathrm{bin}}}(q, b)$ is undefined, ascends to the global root and splits its left child $\mathrm{Flag}$ from $\mathsf{Leaf}$ to $\mathsf{Node}(\mathsf{Leaf},\mathsf{Leaf})$, placing the root tree into $L(\mathcal{H}_3)$. Constructive bounded evaluation of $U_{\mathrm{bin}}$ together with determinism of $\sigma_{\mathrm{sp}}$ yields exact bidirectional halting equivalence.
 $\square$

*Remark 5.3 (Division of computational labor between controller and rewrite rule).* 
Theorem 5.2 clarifies the relationship between controlled pure-$S$ universality and tree-walking automata theory. Read-only finite-state tree-walking automata cannot recognize all regular tree languages [12], whereas Kutrib and Meyer showed that equipping a finite control with a dynamically growing tree-walking storage already recognizes non-semilinear unary languages strictly beyond regular languages even under real-time non-erasing operation [39, 40]. Theorem 5.2 establishes that when multi-pass stateless root-restarted navigation is allowed to mutate an unlabeled tree solely via $\mathsf{Leaf} \to_{\mathrm{sp}} \mathsf{Node}(\mathsf{Leaf},\mathsf{Leaf})$, the resulting system is Turing-complete. Thus, when a universal machine table is permitted inside the finite controller (as in [26] and Theorem 3.9), universality stems from addressable growing tree storage rather than from combinatory dynamics. What $\mathrm{CL}(S)$ genuinely contributes beyond $\to_{\mathrm{sp}}$ is in-tree duplicative computation $S X Y Z \to_S (X Z)(Y Z)$, which enables both the program-free selector $\sigma_{\mathrm{CTS}}$ and universal seed genesis from $D_{\mathrm{seed}}$ in Section 4.

### 5.2. Constant-Step Multiway Halting Shortcuts

We next show that removing external evaluation-order selection in favor of unrestricted multiway rewriting $\to_S^*$ causes immediate soundness collapse across both major pure-$S$ encoding architectures: unopened-generator halt flags (Sections 3–4) and live/tombstone $D \cdot Q$ tag dispatchers [26].

**Proposition 5.4 (Seven-step and five-step multiway halting shortcuts).** 
Under unrestricted pure-$S$ reduction $\to_S^*$, the following constant-step shortcuts hold for arbitrary (including non-terminating) program and queue subterms:

- (i) *Protected-trie halt-flag shortcut ($7$ contractions):* For every integer $k \ge 1$ and arbitrary terms $P_{\mathrm{ring}}, Q_{\mathrm{root}}, j_0, j_1 \in \mathcal{T}_S$, the hub term $F(F(G(0, k+1), P_{\mathrm{ring}}, j_1), Q_{\mathrm{root}}, j_0)$ reduces in $7$ contractions to $F(F(H_{\mathrm{open}}, P_{\mathrm{ring}}, j_1), Q_{\mathrm{root}}, j_0)$, where $H_{\mathrm{open}} \equiv F(g, g, (\nu_k S) g)$ with $g \equiv G(k+1, k+2)$ is an opened frame, without inspecting or contracting a single redex inside $P_{\mathrm{ring}}$ or $Q_{\mathrm{root}}$.
- (ii) *Tag-dispatcher queue-deletion shortcut ($5$ contractions):* Let $v_1 \equiv S(S(S T T))$, let $L_1(X) \equiv (T v_1) X$ be the live $1$-bit queue cell with empty-queue tombstone $Q_{\mathrm{empty}} \equiv S S (v_1 S)$, let $A_0 \equiv S(S K_{\mathrm{cont}}) S$ be the $0$-bit empty-append branch for any continuation $K_{\mathrm{cont}} \in \mathcal{T}_S$, and let $D(A_0, A_1) \equiv T(S A_0 A_1)$ be the binary queue dispatcher for any non-halting $1$-bit append action $A_1 \in \mathcal{T}_S$. Then $D(A_0, A_1)\,(L_1(S))$ reduces in exactly $5$ contractions to 
$$
(S Q_{\mathrm{empty}})\,\Bigl(\bigl((K_{\mathrm{cont}}\,(S Q_{\mathrm{empty}}))\,(Q_{\mathrm{empty}}\,(S Q_{\mathrm{empty}}))\bigr)\,(A_1 Q_{\mathrm{empty}})\Bigr),
$$
 converting the live $1$-bit queue into the empty tombstone $Q_{\mathrm{empty}}$ and firing the $0$-branch $K_{\mathrm{cont}}\,(S Q_{\mathrm{empty}})$ regardless of $A_1$.

*Proof.* 
For (i), let $c_1 \equiv \nu_{k+1} \equiv T \nu_k$, $n_2 \equiv T c_1 \equiv \nu_{k+2}$, $q \equiv c_1 n_2$, and $g \equiv c_1 n_2 S$. Inside the context $C[\square] \equiv F(F(\square, P_{\mathrm{ring}}, j_1), Q_{\mathrm{root}}, j_0)$, the unopened generator $G(0, k+1) \equiv (S T T)\,c_1\,S$ admits the $7$-step pure-$S$ derivation

$$
\begin{aligned}
(S T T)\,c_1\,S
  &\;\to_S\; \bigl((T c_1)(T c_1)\bigr)\,S \;\equiv\; (T c_1)\,n_2\,S
   \;\to_S\; (S n_2 q)\,S
   \;\to_S\; (n_2 S)\,g \\
  &\;\to_S\; \bigl(T(c_1 S)\bigr)\,g
   \;\to_S\; (S g)\,\bigl((c_1 S)\,g\bigr)
   \;\to_S\; (S g)\,\bigl((T(\nu_k S))\,g\bigr) \\
  &\;\to_S\; (S g)\,\bigl(S g\,((\nu_k S)\,g)\bigr) \;\equiv\; H_{\mathrm{open}},
\end{aligned}
$$

lifting by contextual closure to $C[G(0,k+1)] \to_S^7 C[H_{\mathrm{open}}]$ without touching $P_{\mathrm{ring}}$ or $Q_{\mathrm{root}}$.

For (ii), instead of contracting the outer dispatcher redex first (which would inspect the live tag $v_1$ and select $A_1$), an unguided reduction contracts the argument redex $L_1(S) \equiv S S v_1 S \to_r (S S)(v_1 S) \equiv Q_{\mathrm{empty}}$ at step $1$, and then dispatches on $Q_{\mathrm{empty}}$ across steps $2$–$5$:

$$
\begin{aligned}
D(A_0, A_1)\,\bigl(L_1(S)\bigr)
  &\;\to_S\; \bigl(S S (S A_0 A_1)\bigr)\,Q_{\mathrm{empty}} \\
  &\;\to_r\; (S Q_{\mathrm{empty}})\,\bigl((S A_0 A_1)\,Q_{\mathrm{empty}}\bigr) \\
  &\;\to_S\; (S Q_{\mathrm{empty}})\,\bigl((A_0 Q_{\mathrm{empty}})\,(A_1 Q_{\mathrm{empty}})\bigr) \\
  &\;\equiv\; (S Q_{\mathrm{empty}})\,\Bigl(\bigl(S(S K_{\mathrm{cont}})\,S\,Q_{\mathrm{empty}}\bigr)\,(A_1 Q_{\mathrm{empty}})\Bigr) \\
  &\;\to_S\; (S Q_{\mathrm{empty}})\,\Bigl(\bigl((S K_{\mathrm{cont}} Q_{\mathrm{empty}})\,(S Q_{\mathrm{empty}})\bigr)\,(A_1 Q_{\mathrm{empty}})\Bigr) \\
  &\;\to_S\; (S Q_{\mathrm{empty}})\,\Bigl(\bigl((K_{\mathrm{cont}}\,(S Q_{\mathrm{empty}}))\,(Q_{\mathrm{empty}}\,(S Q_{\mathrm{empty}}))\bigr)\,(A_1 Q_{\mathrm{empty}})\Bigr). 
\end{aligned}
$$

$\square$

### 5.3. Non-Existence of Asymmetric Branch Gating in $\mathrm{CL}(S)$

Proposition 5.4(ii) raises the question of whether one could redesign pure-$S$ branch dispatchers using “Church-Boolean” thunk gates $B_0, B_1 \in \mathcal{T}_S$ so that $B_0\,x_0\,x_1$ activates only the first branch thunk $x_0$ while $B_1\,x_0\,x_1$ activates only the second branch thunk $x_1$ (without triggering a divergent computation hidden behind $x_0$). On the first branch, $T \equiv S S$ succeeds in one step:

$$
T\,x_0\,x_1 \;\equiv\; S S x_0 x_1 \;\to_r\; (S x_1)\,(x_0 x_1) \;\in\; \mathrm{NF},
$$

placing $x_0$ into active function position ($x_0 x_1$) while $x_1$ occurs only passively as an argument. We now show that no symmetric partner $B_1$ exists in $\mathrm{CL}(S)$, even when supplied with arbitrarily many closed auxiliary padding arguments $U_1, \dots, U_m$.

**Theorem 5.5 (Impossibility of asymmetric Church-Boolean branch gating in $\mathrm{CL}(S)$).** 
For every variable $x_i \in \mathcal{V}$ and term $P \in \mathcal{T}_S(\mathcal{V})$, say that $x_i$ is *actively called* in $P$, written $\mathrm{call}_i(P)$, if $P$ contains a subterm of the form $x_i W$ for some $W \in \mathcal{T}_S(\mathcal{V})$. Let $M \in \mathcal{T}_S(\mathcal{V})$ and $U_1, \dots, U_m \in \mathcal{T}_S(\mathcal{V})$ for $m \ge 0$ contain neither $x_0$ nor $x_1$. Then for every multiway reduction

$$
M\,x_0\,x_1\,U_1\cdots U_m \;\to_S^*\; N,
$$

if $\mathrm{call}_1(N)$ holds, then $\mathrm{call}_0(N)$ already holds. In particular, there do not exist a closed combinator $B_1 \in \mathcal{T}_S$, closed auxiliary arguments $U_1, \dots, U_m \in \mathcal{T}_S$, and a reduct $N$ of $B_1\,x_0\,x_1\,U_1\cdots U_m$ that actively calls $x_1$ without actively calling $x_0$.

*Proof.* 
First observe that for any variable $x_i$, the predicate $\mathrm{call}_i(-)$ is monotone under $\to_S$: in a root step $S X Y Z \to_r (X Z)(Y Z)$, neither $S$, $S X$, nor $S X Y$ is a variable $x_i$, so any subterm $x_i W$ inside $X$, $Y$, or $Z$ reappears as $x_i W$ inside $X Z$ or $Y Z$; contextual steps $L R \to_S L' R$ (where $L \not\equiv x_i$ since variables are normal) and $L R \to_S L R'$ likewise preserve $\mathrm{call}_i$. Hence once $\mathrm{call}_0(P)$ becomes true at any step, it remains true in every subsequent reduct.

Next, let $\mathcal{F} \subset \mathcal{T}_S(\mathcal{V})$ denote the set of terms containing neither $x_0$ nor $x_1$; by variable conservation under non-erasing $S$-reduction, $\mathcal{F}$ is closed under $\to_S$. Define inductively two subsets $\mathcal{W}_0, \mathcal{O} \subset \mathcal{T}_S(\mathcal{V})$:

- (i) $\mathcal{W}_0$ is generated by $C x_0 \in \mathcal{W}_0$ for every $C \in \mathcal{F}$, and $W_1 W_2 \in \mathcal{W}_0$ whenever $W_1, W_2 \in \mathcal{W}_0$;
- (ii) $\mathcal{O}$ is generated by $W x_1 \in \mathcal{O}$ for every $W \in \mathcal{W}_0$, and $P U \in \mathcal{O}$ whenever $P \in \mathcal{O}$ and $U \in \mathcal{F}$.

Every term in $\mathcal{W}_0$ is an application (so $S \notin \mathcal{W}_0$ and $x_k \notin \mathcal{W}_0$) and contains no occurrence of $x_1$. Consequently:

- If $S P \in \mathcal{W}_0$, then since $S \notin \mathcal{W}_0$, it cannot arise from $W_1 W_2$, so $S P \equiv C x_0$ and hence $P \equiv x_0$.
- If $S P Q \in \mathcal{W}_0$, either $S P Q \equiv C x_0$ (giving $Q \equiv x_0$) or $S P \in \mathcal{W}_0$ (giving $P \equiv x_0$). Thus *every* arity-$2$ prefix $S P Q \in \mathcal{W}_0$ satisfies $P \equiv x_0$ or $Q \equiv x_0$.
- Similarly, every $T' \in \mathcal{O}$ has $\operatorname{ls}(T') \ge 2$ (so $T' \not\equiv S$, $T' \not\equiv x_1$, and $T' \not\equiv S P$), and if $T' \equiv S P Q \in \mathcal{O}$, inversion forces $T' \equiv W x_1$ with $W \equiv S P \in \mathcal{W}_0$, whence $P \equiv x_0$. Moreover, no term in $\mathcal{O}$ satisfies $\mathrm{call}_1$: in $W x_1$, $W \not\equiv x_1$ and $x_1$ is absent from $W$; in $P U$, $P \not\equiv x_1$ and $x_1$ is absent from $U \in \mathcal{F}$.

We claim that if $W \in \mathcal{W}_0$ and $W \to_S W'$, then either $W' \in \mathcal{W}_0$ or $\mathrm{call}_0(W')$ holds. By structural induction on $W \in \mathcal{W}_0$: if $W \equiv C x_0$ ($C \in \mathcal{F}$), either $C \to_S C' \in \mathcal{F}$ (giving $C' x_0 \in \mathcal{W}_0$) or $C \equiv S X Y$ with $X, Y \in \mathcal{F}$ and $S X Y x_0 \to_r (X x_0)(Y x_0) \in \mathcal{W}_0$; if $W \equiv W_1 W_2$, contextual steps in $W_1$ or $W_2$ preserve $\mathcal{W}_0$ or establish $\mathrm{call}_0$ by induction, whereas a root step requires $W_1 \equiv S P Q \in \mathcal{W}_0$, so $P \equiv x_0$ or $Q \equiv x_0$, and the contractum $(P W_2)(Q W_2)$ contains $x_0 W_2$, making $\mathrm{call}_0(W')$ true.

Lifting by structural induction to $T' \in \mathcal{O}$ shows that whenever $T' \to_S T''$, either $T'' \in \mathcal{O}$ or $\mathrm{call}_0(T'')$ holds: for $T' \equiv W x_1$, a left step $W \to_S W'$ yields $W' x_1 \in \mathcal{O}$ or $\mathrm{call}_0(W' x_1)$, while a root step forces $W \equiv S P Q \in \mathcal{W}_0$, hence $P \equiv x_0$ or $Q \equiv x_0$, producing $x_0 x_1$ inside $(P x_1)(Q x_1)$; for $T' \equiv P U$ ($U \in \mathcal{F}$), left steps use the induction hypothesis, right steps $U \to_S U' \in \mathcal{F}$ preserve $\mathcal{O}$, and a root step forces $P \equiv S X Y \in \mathcal{O}$, whence $X \equiv x_0$ and the contractum $(x_0 U)(Y U)$ satisfies $\mathrm{call}_0$.

Finally, $M x_0 \in \mathcal{W}_0$, $(M x_0) x_1 \in \mathcal{O}$, and appending $U_1, \dots, U_m \in \mathcal{F}$ places $T_{\mathrm{start}} \equiv M x_0 x_1 U_1\cdots U_m \in \mathcal{O}$. By induction along $T_{\mathrm{start}} \to_S^* N$ combined with $\to_S$-monotonicity of $\mathrm{call}_0$, either $N \in \mathcal{O}$—which contradicts $\mathrm{call}_1(N)$ since $\mathrm{call}_1$ vanishes on $\mathcal{O}$—or $\mathrm{call}_0(N)$ holds.
 $\square$

## 6. Finite $S$-Algebras, Infinitary Productivity, and Open Questions in $\mathrm{CL}(S)$

When external tree-walking controllers are removed and closed $S$-terms evolve solely under the intrinsic rewrite relation $\to_S$, the behavior of $\mathrm{CL}(S)$ is governed by a hierarchy of finite combinatory $S$-algebras. Because every ground $S$-term is built from a single leaf constant $S$ by binary application, any finite $S$-algebra $\mathcal{A} = (Q, q_0, \odot)$ (Definition 2.6) simultaneously defines a deterministic bottom-up tree automaton running in $2|M| - 1$ table lookups on unfolded syntax trees (and in linear DAG size on shared representations) while remaining invariant under unrestricted conversion $=_S$ by (2.1). Here we develop this algebraic framework constructively without König's lemma or classical choice, establishing explicit finite-rank normalization and head-potential proofs for Waldmann's normalization and top-termination theorems [65, 4] and resolving Questions 5, 7, 10, 30 (for closed normalizing terms), and 31 together with Footnote 4 of Barendregt, Endrullis, Klop, and Waldmann [4].

Table 4 summarizes the finite $S$-algebras, deterministic tree automata, and reachable product subalgebras studied across Sections 6–8. Given $F \subseteq Q$, we write $L(\mathcal{A}, F) = \{ M \in \mathcal{T}_S : \llbracket M \rrbracket_{\mathcal{A}} \in F \}$, retaining the abbreviations $T \equiv S S$, $A \equiv S S S$, leaf count $|M|$, left-spine arity $\operatorname{ls}(M)$, and right-spine depth $\operatorname{rs}(M)$ from Section 2.

**Table 4.** Finite $S$-algebras, deterministic bottom-up tree automata, and reachable product subalgebras in $\mathrm{CL}(S)$.

| Structure | $\vert Q\vert $ | $S$-Law | Recognized Property or Algebraic Invariant on $\mathcal{T}_S$ |
| :— | :—: | :—: | :— |
| $\mathcal{A}_{\mathrm{HN}}$ | $35$ | Yes | Solvability / head normalization ($\llbracket M \rrbracket_{\mathrm{HN}} \neq \infty_{\mathrm{HN}}$; Question 10) |
| $\mathcal{A}_{36}$ | $36$ | Yes | Refines $\infty_{\mathrm{HN}}$ into $\{q_{34}, q_{35}\}$, separating $A A A \neq_S A A A S$ (Question 31) |
| $\mathcal{A}_{\mathrm{SN}}$ | $39$ | Yes | Strong and weak normalization ($\llbracket M \rrbracket_{\mathrm{SN}} \neq \infty_{\mathrm{SN}}$; Theorem 6.2) |
| $\mathcal{A}_P$ | $39$ | Yes | Böhm-tree productivity ($\llbracket M \rrbracket_P \neq \infty_P$; Question 5, Theorem 6.12) |
| $\mathcal{D}_4$ | $4$ | Yes | Functionally complete Boolean algebra realizing $11$-leaf normal-form Rule 110 |
| $\mathcal{B}_Z$ | $8$ | DTA | Accepts step-$t$ reducts of $Z_{\mathrm{Zac}}$ iff $t = \tfrac{1}{2}n(n+3)$ across six strategies |
| $\mathcal{A}_P \times \mathcal{A}_{\mathrm{SN}}$ | $44$ | Yes | Reachable pairs isolating $(q_{29}, \infty_{\mathrm{SN}})$ as unique non-$\mathrm{SN}$ productive redex fiber |
| $\mathcal{A}_{\mathrm{SN}} \times \mathcal{A}_{\mathrm{HN}}$ | $112$ | Yes | Reachable pairs: $94$ in $\mathrm{SN}$, $17$ in $\mathrm{HN} \setminus \mathrm{SN}$, and $1$ in $\overline{\mathrm{HN}}$ |
| $\mathcal{A}_P \times \mathcal{A}_{\mathrm{HN}}$ | $113$ | Yes | Reachable pairs ($95$ accepting, $18$ rejecting) supporting rank-$17$ $\bot$-extraction |
| $\mathcal{A}_{\mathrm{SN}} \times \mathcal{A}_P \times \mathcal{A}_{\mathrm{HN}}$ | $146$ | Yes | Reachable four-phase hierarchy: $98\,\mathrm{SN} + 30\,(\mathrm{Prod}\setminus\mathrm{SN}) + 17\,(\mathrm{HN}\setminus\mathrm{Prod}) + 1\,\overline{\mathrm{HN}}$ |

### 6.1. Strong Normalization and the 39-State Algebra $\mathcal{A}_{\mathrm{SN}}$

Let $\mathcal{N} := \mathcal{T}_S \cap \mathrm{NF}$ denote the set of closed normal forms, generated inductively by the grammar

$$
\mathcal{N} \;::=\; S \;\mid\; S X \;\mid\; S X Y
\qquad (X, Y \in \mathcal{N}). \tag{6.1}
$$

Indeed, every closed $S$-term $M$ decomposes along its left spine as $S M_1 \dots M_k$ where $k = \operatorname{ls}(M) \ge 0$: if $k \ge 3$, its prefix $S M_1 M_2 M_3$ is already a redex, whereas if $k \le 2$, then $M$ contains no redex if and only if each spine argument $M_i$ lies in $\mathcal{N}$.

**Lemma 6.1 (Subterm inheritance and decomposition of strong normalization).** 
For all open or closed $S$-terms $M, M', L, R \in \mathcal{T}_S(\mathcal{V})$:

- (i) *Subterm inheritance:* Recall from Proposition 2.2(ii) that $M \to_S M'$ implies $|M| \le |M'|$. A binary application $L R$ lies in $\mathrm{SN}$ if and only if $L \in \mathrm{SN}$, $R \in \mathrm{SN}$, and every reduct of $L R$ formed after a root contraction lies in $\mathrm{SN}$; in particular, every subterm of a strongly normalizing $S$-term is strongly normalizing.
- (ii) *Equivalence of $\mathrm{WN}$ and $\mathrm{SN}$:* By Proposition 2.2(iii), $M \in \mathrm{WN}$ holds if and only if $M \in \mathrm{SN}$.

*Proof.* 
Part (ii) was established constructively via weighted parallel projection in Proposition 2.2(iii). For (i), if an infinite reduction starts inside $L$ (or $R$), applying $R$ on the right (or $L$ on the left) lifts it step-for-step to an infinite reduction of $L R$; hence $L R \in \mathrm{SN}$ implies $L \in \mathrm{SN}$ and $R \in \mathrm{SN}$, and structural induction extends this inheritance to all subterms. Conversely, well-founded induction on $(L, R) \in \mathrm{SN} \times \mathrm{SN}$ together with the hypothesis on post-root-contraction reducts shows $L R \in \mathrm{SN}$.
 $\square$

We define the $39$-state combinatory $S$-algebra $\mathcal{A}_{\mathrm{SN}} = (Q_{\mathrm{SN}}, q_0, \odot_{\mathrm{SN}})$ with carrier $Q_{\mathrm{SN}} = \{q_0, q_1, \dots, q_{37}, \infty_{\mathrm{SN}}\}$ (identifying $\infty_{\mathrm{SN}} = q_{38}$), accepting subset $F_{\mathrm{SN}} = Q_{\mathrm{SN}} \setminus \{\infty_{\mathrm{SN}}\}$ of cardinality $38$, and transition operation $\odot_{\mathrm{SN}}$ obtained by transposing Figure 5.11 of Barendregt et al. [4, p. 82] and adjoining $\infty_{\mathrm{SN}}$ as a two-sided absorbing sink ($\infty_{\mathrm{SN}} \odot_{\mathrm{SN}} y = x \odot_{\mathrm{SN}} \infty_{\mathrm{SN}} = \infty_{\mathrm{SN}}$ for all $x, y \in Q_{\mathrm{SN}}$). Direct evaluation over all $39^3 = 59{,}319$ triples in $Q_{\mathrm{SN}}^3$ confirms (2.1).

**Theorem 6.2 (Regularity of strong normalization [65]; [4, Theorem 9]).** 
For every closed $S$-term $M \in \mathcal{T}_S$,

$$
M \in \mathrm{SN} \;\Longleftrightarrow\; M \in \mathrm{WN} \;\Longleftrightarrow\; \llbracket M \rrbracket_{\mathrm{SN}} \neq \infty_{\mathrm{SN}},
$$

and membership $M \in \mathrm{SN}$ is decidable in $2|M| - 1$ deterministic table lookups.

*Proof.* 
Equivalence of $M \in \mathrm{SN}$ and $M \in \mathrm{WN}$ holds by Lemma 6.1(ii). For soundness (that $M \in \mathrm{WN}$ implies $\llbracket M \rrbracket_{\mathrm{SN}} \neq \infty_{\mathrm{SN}}$), inspection of row $q_0$ and of all $38^2 = 1{,}444$ pairs $(x, y) \in F_{\mathrm{SN}}^2$ in $\mathcal{A}_{\mathrm{SN}}$ shows that $q_0 \neq \infty_{\mathrm{SN}}$, that $x \neq \infty_{\mathrm{SN}}$ implies $q_0 \odot_{\mathrm{SN}} x \neq \infty_{\mathrm{SN}}$, and that $x, y \neq \infty_{\mathrm{SN}}$ implies $(q_0 \odot_{\mathrm{SN}} x) \odot_{\mathrm{SN}} y \neq \infty_{\mathrm{SN}}$. Structural induction on the grammar (6.1) therefore yields $\llbracket V \rrbracket_{\mathrm{SN}} \neq \infty_{\mathrm{SN}}$ for every $V \in \mathcal{N}$. If $M \to_S^* V \in \mathcal{N}$, conversion invariance of $\mathcal{A}_{\mathrm{SN}}$ gives $\llbracket M \rrbracket_{\mathrm{SN}} = \llbracket V \rrbracket_{\mathrm{SN}} \neq \infty_{\mathrm{SN}}$.

For constructive completeness (that $\llbracket M \rrbracket_{\mathrm{SN}} \neq \infty_{\mathrm{SN}}$ implies $M \to_S^* V$ for some $V \in \mathcal{N}$), we avoid König's lemma by constructing a total recursive normalization operator $\mathrm{app}_{\mathcal{N}}(F, Z) \in \mathcal{N}$ satisfying $F Z \to_S^* \mathrm{app}_{\mathcal{N}}(F, Z)$ for all canonical normal forms $F, Z \in \mathcal{N}$ with $\llbracket F \rrbracket_{\mathrm{SN}} \odot_{\mathrm{SN}} \llbracket Z \rrbracket_{\mathrm{SN}} \neq \infty_{\mathrm{SN}}$. Once $\mathrm{app}_{\mathcal{N}}$ is established, structural induction on $M$ normalizes every accepted term: $\mathrm{norm}(S) = S$, and for $M \equiv L R$ with $\llbracket L R \rrbracket_{\mathrm{SN}} \neq \infty_{\mathrm{SN}}$, the two-sided sink property of $\infty_{\mathrm{SN}}$ forces $\llbracket L \rrbracket_{\mathrm{SN}} \neq \infty_{\mathrm{SN}}$ and $\llbracket R \rrbracket_{\mathrm{SN}} \neq \infty_{\mathrm{SN}}$, whence $L R \to_S^* \mathrm{norm}(L)\,\mathrm{norm}(R) \to_S^* \mathrm{app}_{\mathcal{N}}(\mathrm{norm}(L), \mathrm{norm}(R)) \in \mathcal{N}$.

To construct $\mathrm{app}_{\mathcal{N}}(F, Z)$ without unbounded search, let $I_2 \subseteq F_{\mathrm{SN}}$ denote the set of states inhabited by spine-$2$ normal forms $S A B$, and define a finite state-triple rank $\tau_{\mathrm{SN}} : Q_{\mathrm{SN}}^3 \to \{0, 1, \dots, 6\}$ together with $\hat{\tau}_{\mathrm{SN}}(w, v) = \max\{ \tau_{\mathrm{SN}}(a, b, v) : a, b \in F_{\mathrm{SN}},\, (q_0 \odot_{\mathrm{SN}} a) \odot_{\mathrm{SN}} b = w \}$ (with $\hat{\tau}_{\mathrm{SN}}(w, v) = 0$ if $w \notin I_2$), verified over $F_{\mathrm{SN}}^3$ to satisfy two strict decrease laws whenever $((q_0 \odot_{\mathrm{SN}} x) \odot_{\mathrm{SN}} y) \odot_{\mathrm{SN}} z \neq \infty_{\mathrm{SN}}$:

$$
\begin{aligned}
\tau_{\mathrm{SN}}(u, z, y \odot_{\mathrm{SN}} z) &\;<\; \tau_{\mathrm{SN}}(q_0 \odot_{\mathrm{SN}} u, y, z)
&&\textrm{whenever } x = q_0 \odot_{\mathrm{SN}} u, \\
\hat{\tau}_{\mathrm{SN}}(x \odot_{\mathrm{SN}} z, y \odot_{\mathrm{SN}} z) &\;<\; \tau_{\mathrm{SN}}(x, y, z)
&&\textrm{whenever } x \in I_2.
\end{aligned} \tag{6.2–6.3}
$$

Assign to each call $(F, Z)$ its rank $r(F, Z) = 0$ if $F \equiv S$ or $F \equiv S X$, and $r(S X Y, Z) = \tau_{\mathrm{SN}}(\llbracket X \rrbracket_{\mathrm{SN}}, \llbracket Y \rrbracket_{\mathrm{SN}}, \llbracket Z \rrbracket_{\mathrm{SN}}) \ge 1$ otherwise. We proceed by well-founded lexicographic induction on $(r(F, Z), |F| + |Z|) \in \mathbb{N}^2$. If $F \equiv S$ or $F \equiv S X$, then $F Z \in \mathcal{N}$ already. If $F \equiv S X Y$ with $X, Y \in \mathcal{N}$, then $(S X Y) Z \to_S (X Z)(Y Z)$, and conversion invariance plus the two-sided sink property ensure $\llbracket X Z \rrbracket_{\mathrm{SN}} \neq \infty_{\mathrm{SN}}$, $\llbracket Y Z \rrbracket_{\mathrm{SN}} \neq \infty_{\mathrm{SN}}$, and $\llbracket (X Z)(Y Z) \rrbracket_{\mathrm{SN}} \neq \infty_{\mathrm{SN}}$. Since $|Y| + |Z| < |S X Y| + |Z|$ and every sub-rank of $(Y, Z)$ is bounded by $\tau_{\mathrm{SN}}(\llbracket X \rrbracket_{\mathrm{SN}}, \llbracket Y \rrbracket_{\mathrm{SN}}, \llbracket Z \rrbracket_{\mathrm{SN}})$ (verified across $F_{\mathrm{SN}}^3$), the induction hypothesis normalizes $Y Z \to_S^* W \in \mathcal{N}$ with $\llbracket W \rrbracket_{\mathrm{SN}} = \llbracket Y \rrbracket_{\mathrm{SN}} \odot_{\mathrm{SN}} \llbracket Z \rrbracket_{\mathrm{SN}}$. We now branch on $X \in \mathcal{N}$:

- (i) If $X \equiv S$, then $(X Z)(Y Z) \equiv S Z (Y Z) \to_S^* S Z W \in \mathcal{N}$, completing normalization.
- (ii) If $X \equiv S U$ with $U \in \mathcal{N}$, then $(X Z)(Y Z) \to_S^* (S U Z) W$, and by (6.2) the call $(S U Z, W)$ has strictly smaller first lexicographic component $\tau_{\mathrm{SN}}(\llbracket U \rrbracket_{\mathrm{SN}}, \llbracket Z \rrbracket_{\mathrm{SN}}, \llbracket W \rrbracket_{\mathrm{SN}}) < r(S(S U)Y, Z)$.
- (iii) If $X \equiv S A B$ with $A, B \in \mathcal{N}$, then $\llbracket X \rrbracket_{\mathrm{SN}} \in I_2$ and $|X| + |Z| < |S X Y| + |Z|$ (with $\tau_{\mathrm{SN}}(\llbracket A \rrbracket_{\mathrm{SN}}, \llbracket B \rrbracket_{\mathrm{SN}}, \llbracket Z \rrbracket_{\mathrm{SN}}) \le r(S X Y, Z)$), so $X Z \to_S^* V \in \mathcal{N}$ with $\llbracket V \rrbracket_{\mathrm{SN}} = \llbracket X \rrbracket_{\mathrm{SN}} \odot_{\mathrm{SN}} \llbracket Z \rrbracket_{\mathrm{SN}}$. By (6.3), $r(V, W) \le \hat{\tau}_{\mathrm{SN}}(\llbracket V \rrbracket_{\mathrm{SN}}, \llbracket W \rrbracket_{\mathrm{SN}}) < r(S X Y, Z)$, so $\mathrm{app}_{\mathcal{N}}(V, W) \in \mathcal{N}$ terminates. 

$\square$

*Remark 6.3 (Automaton minimization and table orientation).* 
Two bibliographical details merit record when comparing implementations of $\mathcal{A}_{\mathrm{SN}}$ across the literature. First, Waldmann's original top-down grammar construction [64, 65] yielded $43$ non-terminals; Endrullis, de Vrijer, and Waldmann [24, Section 5, p. 15] subsequently applied local termination and Myhill–Nerode minimization to obtain the minimal $39$-state totalized deterministic bottom-up tree automaton ($38$ accepting states and $1$ undefined sink). Second, in Figure 5.11 of Barendregt, Endrullis, Klop, and Waldmann [4, p. 82], the printed $38 \times 38$ array indexes the left-applicand state $x = \llbracket M \rrbracket_{\mathrm{SN}}$ horizontally across columns and the right-applicand state $y = \llbracket N \rrbracket_{\mathrm{SN}}$ vertically down rows, transposed relative to the figure caption; reading rows as left applicands and columns as right applicands violates (2.1) already on $T T T \equiv (S S)(S S)(S S)$.

### 6.2. Head Normalization, Constructive Integer Potentials, and Question 10

Recall from Definition 2.4(i)–(ii) that a closed $S$-term $M \in \mathcal{T}_S$ lies in $\mathrm{HNF}$ when $\operatorname{ls}(M) \le 2$, is solvable ($M \in \mathrm{HN}$) when $M \to_S^* H$ for some $H \in \mathrm{HNF}$ (equivalently, by standardization [1], when deterministic head reduction $\to_h$ from $M$ terminates in $\mathrm{HNF}$), and lies in $\mathrm{RNF}$ when no reduction from $M$ ever contracts at the root. Before introducing the $35$-state head-normalization algebra, we establish three syntactic rigidity properties of multi-argument applications in $\mathrm{CL}(S)$ refining Visser's variable-tail method and Proposition 2.3(iii).

**Lemma 6.4 (Spine-$2$ persistence, Fibonacci $2$-HNFs, and third-argument head exclusion).** 
Let $U \in \mathcal{T}_S$ be a closed $S$-term and let $x, y, z \in \mathcal{V}$ be distinct variables.

- (i) *Persistence of spine arity at least $2$:* For all open or closed terms $A_1, A_2, A_3, W \in \mathcal{T}_S(\mathcal{V})$, neither $(A_1 A_2) A_3 \to_S^* S$ nor $(A_1 A_2) A_3 \to_S^* S W$ holds. Consequently, $F X \to_S^* S W$ implies $F \equiv S$ and $X \to_S^* W$.
- (ii) *Fibonacci classification of parametric $2$-HNFs:* Define $R_0 \equiv S$, $R_{k+1} \equiv S R_k$, and the Fibonacci word trees $W_0(x, y) \equiv x$, $W_1(x, y) \equiv y$, $W_{m+2}(x, y) \equiv W_m(x, y)\,W_{m+1}(x, y)$. Then $U x y \to_S^* S P Q$ holds if and only if there exists $k \in \mathbb{N}$ such that $U \to_S^* R_k$, $P \equiv W_k(x, y)$, and $Q \equiv W_{k+1}(x, y)$. Moreover, if $U x y \to_S^* S P Q$ with $U \not\equiv S$, then both right spines of $P$ and $Q$ terminate in $y$.
- (iii) *Third-argument head exclusion:* Whenever $U x y z \to_S^* H$ with $H$ in open head normal form (either $\operatorname{ls}(H) \le 2$ with head $S$, or head in $\mathcal{V}$), the leftmost leaf of $H$ belongs to $\{x, y\}$ and is never $z$ or $S$.

*Proof.* 
For (i), define the predicate $\Phi_2(K)$ asserting $\operatorname{ls}(K) \ge 2$, meaning $K \equiv (K_1 K_2) K_3$. A root contraction $S X Y Z \to_S (X Z)(Y Z)$ produces a term of left-spine arity $\operatorname{ls}(X Z) + 1 \ge 2$; a left step $(K_1 K_2) K_3 \to_S L' K_3$ satisfies $\operatorname{ls}(L') \ge 1$ by inspection of root, left, and right subcases on $K_1 K_2$; and a right step leaves $\operatorname{ls}$ unchanged. Induction along $\to_S^*$ shows that $\Phi_2$ is closed forward under reduction, excluding $S$ ($\operatorname{ls} = 0$) and $S W$ ($\operatorname{ls} = 1$). If $F X \to_S^* S W$, then $F$ cannot be a variable (head variable $v$ is preserved) or an application $F_1 F_2$ (by $\Phi_2$), forcing $F \equiv S$ and $X \to_S^* W$.

For (ii), forward verification $R_k W_m W_{m+1} \to_S^* S W_{m+k} W_{m+k+1}$ holds by induction on $k$, since $(S R_k) W_m W_{m+1} \to_S R_k W_{m+1} (W_m W_{m+1}) \equiv R_k W_{m+1} W_{m+2}$. Conversely, we prove by strong induction on step count $n$ that if $U W_m W_{m+1} \to_S^n S P Q$ with $U$ closed, then $U \to_S^* R_k$, $P \equiv W_{m+k}$, and $Q \equiv W_{m+k+1}$ for some $k \ge 0$. Because every $W_j(x, y)$ contains no $S$-leaves, it is irreducible. If no root contraction occurs at the outer application $(U W_m) W_{m+1}$, then $U W_m \to_S^n S P$ and $Q \equiv W_{m+1}$; by (i), $U \equiv S \equiv R_0$ and $W_m \to_S^* P$, so $P \equiv W_m$ ($k = 0$). Otherwise, $(U W_m) \to_S^{n_1} S A_1 A_2$ and $(A_1 W_{m+1})(A_2 W_{m+1}) \to_S^{n_2} S P Q$ with $n_1 + n_2 + 1 = n$. Recall from the proof of Proposition 2.3(iii) that the classes $\mathcal{W}_1$, $\mathcal{W}_2 = \mathcal{W}_1 \cdot \mathcal{W}_1$, and $\mathcal{W}_3 = \mathcal{W}_2 \cdot \mathcal{W}_1$ of terms ending in variables are closed forward under $\to_S$. If $U W_m \to_S^{n_1} S A_1 A_2$ used a root contraction $(S X_1 X_2) W_m \to_S (X_1 W_m)(X_2 W_m) \to_S^* S A_1 A_2$, then $(X_1 W_m)(X_2 W_m) \in \mathcal{W}_2$ would force $S A_1 \in \mathcal{W}_1$ and $A_1 \in \mathcal{W}_1$, placing $(A_1 W_{m+1})(A_2 W_{m+1}) \in \mathcal{W}_3$, which never reduces to $S P Q$ since $S \notin \mathcal{W}_1$. Thus $U W_m \to_S^{n_1} S A_1 A_2$ performs no outer root contraction, giving $U \to_S^{n_1} S A_1$, $A_2 \equiv W_m$, and $A_1 W_{m+1} W_{m+2} \to_S^{n_2} S P Q$ with $n_2 < n$; the induction hypothesis on $A_1$ yields $A_1 \to_S^* R_{k'}$ and $U \to_S^* S R_{k'} \equiv R_{k'+1}$. When $k \ge 1$, both $W_k(x, y)$ and $W_{k+1}(x, y)$ end on their right spine in $y$.

For (iii), suppose $(U x y) z \to_S^* H \in \mathrm{HNF}$. Since $z$ is irreducible, either $H \equiv F' z$ with $U x y \to_S^* F'$ (in which case $\operatorname{ls}(F') \ge 2$ by (i), so $\operatorname{ls}(F' z) \ge 3$, forcing the head of $H$ to be a variable occurring in $U x y$, namely $x$ or $y$), or else $U x y \to_S^* S P Q$ and $(P z)(Q z) \to_S^* H$. By (ii), $P \equiv W_k(x, y)$ and $Q \equiv W_{k+1}(x, y)$, so $(P z)(Q z)$ contains no $S$-leaves and is already in normal form with head leaf equal to that of $W_k(x, y)$, which belongs to $\{x, y\}$.
 $\square$

In Section 5.3 of Barendregt, Endrullis, Klop, and Waldmann [4, Figure 5.14, p. 85; Question 10 and Footnote 4, p. 86], a candidate $35$-state transition table was synthesized via local termination heuristics to recognize $\mathrm{HN}$, and its proof of correctness—together with linear-time decidability of $\mathrm{RNF}$—was posed as Question 10 and Footnote 4. Let $\mathcal{A}_{\mathrm{HN}} = (Q_{\mathrm{HN}}, q_0, \odot_{\mathrm{HN}})$ denote this $35$-state structure with carrier $Q_{\mathrm{HN}} = \{q_0, q_1, \dots, q_{33}, \infty_{\mathrm{HN}}\}$ ($\infty_{\mathrm{HN}} = q_{34}$) and accepting set $F_{\mathrm{HN}} = Q_{\mathrm{HN}} \setminus \{\infty_{\mathrm{HN}}\}$. Direct evaluation over all $35^3 = 42{,}875$ triples verifies (2.1). Unlike $\infty_{\mathrm{SN}} \in Q_{\mathrm{SN}}$, the state $\infty_{\mathrm{HN}}$ exhibits a directional asymmetry:

$$
\infty_{\mathrm{HN}} \odot_{\mathrm{HN}} y \;=\; \infty_{\mathrm{HN}} \quad\text{for all } y \in Q_{\mathrm{HN}},
\qquad\text{whereas}\qquad
q_0 \odot_{\mathrm{HN}} \infty_{\mathrm{HN}} \;=\; q_{10} \;\neq\; \infty_{\mathrm{HN}}, \tag{6.4}
$$

and $(q_0 \odot_{\mathrm{HN}} x) \odot_{\mathrm{HN}} \infty_{\mathrm{HN}} \neq \infty_{\mathrm{HN}}$ for every $x \in Q_{\mathrm{HN}}$. Algebraically, $\infty_{\mathrm{HN}}$ is a left ideal element because applying an unsolvable head $M$ to $N$ yields an unsolvable term $M N$, whereas $S M$ and $S X M$ already lie in $\mathrm{HNF}$ regardless of whether $M$ has a head normal form.

To prove completeness (that $\llbracket M \rrbracket_{\mathrm{HN}} \neq \infty_{\mathrm{HN}}$ implies $M \in \mathrm{HN}$) constructively without König's lemma, we introduce an affine state-weighted tree potential.

**Lemma 6.5 (Constructive affine head-step potential).** 
There exist explicit non-negative integer matrices $A : Q_{\mathrm{HN}}^2 \to \{0, 1, \dots, 30\}$ and $B : Q_{\mathrm{HN}}^2 \to \{0, 1, \dots, 68\}$ (attaining their maxima $A(q_{10}, q_0) = 30$ and $B(q_{10}, q_0) = 68$, with $A(u, \infty_{\mathrm{HN}}) = 0$ for all $u \in Q_{\mathrm{HN}}$) such that across all $8{,}329$ active head-redex triples $(x, y, z) \in Q_{\mathrm{HN}}^3$ satisfying $((q_0 \odot_{\mathrm{HN}} x) \odot_{\mathrm{HN}} y) \odot_{\mathrm{HN}} z \neq \infty_{\mathrm{HN}}$, writing $s_1 = q_0 \odot_{\mathrm{HN}} x$, $s_2 = s_1 \odot_{\mathrm{HN}} y$, $u = x \odot_{\mathrm{HN}} z$, and $v = y \odot_{\mathrm{HN}} z$, the following four inequalities hold simultaneously:

$$
\begin{aligned}
u \neq \infty_{\mathrm{HN}} \quad\textrm{and}\quad 1 &\;\le\; A(q_0, x), \\
A(u, v) &\;\le\; A(s_1, y), \\
A(x, z) + A(u, v)\,A(y, z) &\;\le\; A(s_2, z), \\
B(x, z) + A(u, v)\,B(y, z) + B(u, v) + 2 &\;\le\; B(q_0, x) + B(s_1, y) + B(s_2, z).
\end{aligned} \tag{6.5–6.8}
$$

Define the recursive integer potential $\mu_{\mathrm{HN}} : \mathcal{T}_S \to \mathbb{N}$ by $\mu_{\mathrm{HN}}(S) = 0$ and

$$
\mu_{\mathrm{HN}}(L R) \;=\; \mu_{\mathrm{HN}}(L) + A(\llbracket L \rrbracket_{\mathrm{HN}}, \llbracket R \rrbracket_{\mathrm{HN}})\,\mu_{\mathrm{HN}}(R) + B(\llbracket L \rrbracket_{\mathrm{HN}}, \llbracket R \rrbracket_{\mathrm{HN}}). \tag{6.9}
$$

Then for every closed $S$-term $M \in \mathcal{T}_S$ with $\llbracket M \rrbracket_{\mathrm{HN}} \neq \infty_{\mathrm{HN}}$ and every head contraction $M \to_h M'$, we have $\mu_{\mathrm{HN}}(M') + 2 \le \mu_{\mathrm{HN}}(M)$.

*Proof.* 
Verification of (6.5)–(6.8) over $\{ (x, y, z) \in Q_{\mathrm{HN}}^3 : ((q_0 \odot_{\mathrm{HN}} x) \odot_{\mathrm{HN}} y) \odot_{\mathrm{HN}} z \neq \infty_{\mathrm{HN}} \}$ ($8{,}329$ triples out of $35^3 = 42{,}875$) is a finite integer arithmetic check. We prove $\mu_{\mathrm{HN}}(M') + 2 \le \mu_{\mathrm{HN}}(M)$ by induction on the derivation of $M \to_h M'$.

In the base case, $M \equiv ((S X) Y) Z$ contracts at the root to $M' \equiv (X Z)(Y Z)$, with $x = \llbracket X \rrbracket_{\mathrm{HN}}$, $y = \llbracket Y \rrbracket_{\mathrm{HN}}$, $z = \llbracket Z \rrbracket_{\mathrm{HN}}$, and $((q_0 \odot_{\mathrm{HN}} x) \odot_{\mathrm{HN}} y) \odot_{\mathrm{HN}} z = \llbracket M \rrbracket_{\mathrm{HN}} \neq \infty_{\mathrm{HN}}$. Expanding $\mu_{\mathrm{HN}}(M)$ via (6.9) and $\mu_{\mathrm{HN}}(S) = 0$ yields

$$
\mu_{\mathrm{HN}}(((S X) Y) Z)
\;=\; A(q_0, x)\,\mu_{\mathrm{HN}}(X) + A(s_1, y)\,\mu_{\mathrm{HN}}(Y) + A(s_2, z)\,\mu_{\mathrm{HN}}(Z)
+ B(q_0, x) + B(s_1, y) + B(s_2, z),
$$

whereas expanding $\mu_{\mathrm{HN}}((X Z)(Y Z))$ with $\llbracket X Z \rrbracket_{\mathrm{HN}} = u$ and $\llbracket Y Z \rrbracket_{\mathrm{HN}} = v$ yields

$$
\begin{aligned}
\mu_{\mathrm{HN}}((X Z)(Y Z))
&\;=\; \mu_{\mathrm{HN}}(X) + A(u, v)\,\mu_{\mathrm{HN}}(Y) + \bigl(A(x, z) + A(u, v)\,A(y, z)\bigr)\mu_{\mathrm{HN}}(Z) \\
&\qquad + B(x, z) + A(u, v)\,B(y, z) + B(u, v).
\end{aligned}
$$

Since $\mu_{\mathrm{HN}}(X), \mu_{\mathrm{HN}}(Y), \mu_{\mathrm{HN}}(Z) \ge 0$, comparing the coefficients of $\mu_{\mathrm{HN}}(X)$, $\mu_{\mathrm{HN}}(Y)$, $\mu_{\mathrm{HN}}(Z)$ and the constant terms directly via (6.5)–(6.8) gives $\mu_{\mathrm{HN}}((X Z)(Y Z)) + 2 \le \mu_{\mathrm{HN}}(((S X) Y) Z)$.

In the inductive step, $M \equiv L R \to_h L' R$ where $L \to_h L'$. Because $\llbracket L \rrbracket_{\mathrm{HN}} \odot_{\mathrm{HN}} \llbracket R \rrbracket_{\mathrm{HN}} = \llbracket L R \rrbracket_{\mathrm{HN}} \neq \infty_{\mathrm{HN}}$ and $\infty_{\mathrm{HN}}$ is a left sink by (6.4), we must have $\llbracket L \rrbracket_{\mathrm{HN}} \neq \infty_{\mathrm{HN}}$. Thus the induction hypothesis gives $\mu_{\mathrm{HN}}(L') + 2 \le \mu_{\mathrm{HN}}(L)$. By conversion invariance of $\mathcal{A}_{\mathrm{HN}}$, $\llbracket L' \rrbracket_{\mathrm{HN}} = \llbracket L \rrbracket_{\mathrm{HN}}$, so both $A(\llbracket L' \rrbracket_{\mathrm{HN}}, \llbracket R \rrbracket_{\mathrm{HN}}) = A(\llbracket L \rrbracket_{\mathrm{HN}}, \llbracket R \rrbracket_{\mathrm{HN}})$ and $B(\llbracket L' \rrbracket_{\mathrm{HN}}, \llbracket R \rrbracket_{\mathrm{HN}}) = B(\llbracket L \rrbracket_{\mathrm{HN}}, \llbracket R \rrbracket_{\mathrm{HN}})$ remain unchanged across the step, whence

$$
\mu_{\mathrm{HN}}(L R) - \mu_{\mathrm{HN}}(L' R) \;=\; \mu_{\mathrm{HN}}(L) - \mu_{\mathrm{HN}}(L') \;\ge\; 2.
$$

$\square$

**Theorem 6.6 (Resolution of Question 10 and Footnote 4 of Barendregt et al. [4, p. 86]).** 
For every closed $S$-term $M \in \mathcal{T}_S$, the $35$-state $S$-algebra $\mathcal{A}_{\mathrm{HN}}$ satisfies the following properties:

- (i) *Regularity and constructive bound for $\mathrm{HN}$:* One has $M \in \mathrm{HN}$ if and only if $\llbracket M \rrbracket_{\mathrm{HN}} \neq \infty_{\mathrm{HN}}$. Specifically, if $\llbracket M \rrbracket_{\mathrm{HN}} \neq \infty_{\mathrm{HN}}$, deterministic head reduction from $M$ reaches $\mathrm{HNF}$ in at most $\lfloor \mu_{\mathrm{HN}}(M) / 2 \rfloor$ steps.
- (ii) *Linear-time decidability of $\mathrm{RNF}$ (Footnote 4):* A closed $S$-term $M$ lies in $\mathrm{RNF}$ if and only if 
$$
\operatorname{ls}(M) \le 2 \quad\textrm{or}\quad \bigl(M \equiv P Q \;\textrm{ and }\; \llbracket P \rrbracket_{\mathrm{HN}} = \infty_{\mathrm{HN}}\bigr), \tag{6.10}
$$
 which is decidable in $O(|M|)$ deterministic operations.
- (iii) *Five-composite-argument $\mathrm{RNF}$ ceiling:* In the spine transition graph of $\mathcal{A}_{\mathrm{HN}}$, the transition $q_{13} \xrightarrow{q_0} q_{13}$ (entered via $q_0 \xrightarrow{q_0} q_1 \xrightarrow{y} q_{13}$) is the unique accepting self-loop, and consuming composite arguments ($y \neq q_0$) contracts the reachable state sets strictly along cardinalities $35 \to 26 \to 14 \to 4 \to 2 \to 1 = \{\infty_{\mathrm{HN}}\}$. Consequently, for every closed $M \in \mathcal{T}_S$ and all closed $U_1, \dots, U_5 \in \mathcal{T}_S \setminus \{S\}$, we have $\llbracket M U_1 U_2 U_3 U_4 U_5 \rrbracket_{\mathrm{HN}} = \infty_{\mathrm{HN}}$, and $M U_1 U_2 U_3 U_4 U_5 U_6 \in \mathrm{RNF}$ for every $U_6 \in \mathcal{T}_S$.
- (iv) *Joint $(\mathrm{SN}, \mathrm{HN})$ subalgebra:* The reachable subalgebra of $\mathcal{A}_{\mathrm{SN}} \times \mathcal{A}_{\mathrm{HN}}$ generated by $(q_0, q_0)$ has exact cardinality $112$, partitioning into $94$ states in $F_{\mathrm{SN}} \times F_{\mathrm{HN}}$ ($\mathrm{SN}$), $17$ states in $\{\infty_{\mathrm{SN}}\} \times F_{\mathrm{HN}}$ ($\mathrm{HN} \setminus \mathrm{SN}$), and the single state $(\infty_{\mathrm{SN}}, \infty_{\mathrm{HN}})$ ($\overline{\mathrm{HN}}$).

*Proof.* 
For (i), every closed $H \in \mathrm{HNF}$ has the form $S$, $S A_1$, or $S A_1 A_2$, and inspection of $\mathcal{A}_{\mathrm{HN}}$ confirms $q_0 \neq \infty_{\mathrm{HN}}$, $q_0 \odot_{\mathrm{HN}} x \neq \infty_{\mathrm{HN}}$, and $(q_0 \odot_{\mathrm{HN}} x) \odot_{\mathrm{HN}} y \neq \infty_{\mathrm{HN}}$ for all $x, y \in Q_{\mathrm{HN}}$; conversion invariance therefore shows that $M \in \mathrm{HN}$ implies $\llbracket M \rrbracket_{\mathrm{HN}} \neq \infty_{\mathrm{HN}}$. Conversely, every closed $M \notin \mathrm{HNF}$ satisfies $\operatorname{ls}(M) \ge 3$ and admits a unique head step $M \to_h M'$. If $\llbracket M \rrbracket_{\mathrm{HN}} \neq \infty_{\mathrm{HN}}$, conversion invariance preserves $\llbracket M' \rrbracket_{\mathrm{HN}} \neq \infty_{\mathrm{HN}}$ and Lemma 6.5 decreases $\mu_{\mathrm{HN}} \in \mathbb{N}$ by at least $2$ at each step, terminating in $\mathrm{HNF}$ within $\lfloor \mu_{\mathrm{HN}}(M) / 2 \rfloor$ steps.

For (ii), if $\operatorname{ls}(M) \le 2$, then $M \in \mathrm{HNF} \subseteq \mathrm{RNF}$. Suppose now $\operatorname{ls}(M) \ge 3$, so $M \equiv P Q$ with $\operatorname{ls}(P) \ge 2$. A reduction $P Q \to_S^* N$ contracts at the root if and only if $P \to_S^* S X Y$ for some $X, Y \in \mathcal{T}_S$. By Lemma 6.4(i), since $\operatorname{ls}(P) \ge 2$, no reduct of $P$ can be $S$ or $S W$; hence $P$ reduces to some $S X Y$ if and only if $P \in \mathrm{HN}$, which by (i) holds if and only if $\llbracket P \rrbracket_{\mathrm{HN}} \neq \infty_{\mathrm{HN}}$. Negating this equivalence yields $P Q \in \mathrm{RNF}$ if and only if $\llbracket P \rrbracket_{\mathrm{HN}} = \infty_{\mathrm{HN}}$, establishing (6.10).

For (iii), inspection of row $q_0$ of $\mathcal{A}_{\mathrm{HN}}$ shows that $q_0$ never occurs in the image of $\odot_{\mathrm{HN}}$; hence a closed $S$-term $U$ evaluates to $q_0$ in $\mathcal{A}_{\mathrm{HN}}$ if and only if $U \equiv S$. Computing $S_{k+1} = \{ u \odot_{\mathrm{HN}} y : u \in S_k,\, y \in Q_{\mathrm{HN}} \setminus \{q_0\} \}$ starting from $S_0 = Q_{\mathrm{HN}}$ yields $|S_0| = 35$, $|S_1| = 26$, $|S_2| = 14$, $|S_3| = 4$ ($\{q_{23}, q_{24}, q_{25}, \infty_{\mathrm{HN}}\}$), $|S_4| = 2$ ($\{q_{23}, \infty_{\mathrm{HN}}\}$), and $S_5 = \{\infty_{\mathrm{HN}}\}$. Thus $\llbracket M U_1 \dots U_5 \rrbracket_{\mathrm{HN}} = \infty_{\mathrm{HN}}$, and (6.10) implies $M U_1 \dots U_5 U_6 \in \mathrm{RNF}$; five arguments is sharp, since $S S U_1 U_2 U_3 U_4$ has $\mathrm{HN}$ state $q_{23} \neq \infty_{\mathrm{HN}}$ for $U_i \equiv S S$.

For (iv), breadth-first closure of $\{(q_0, q_0)\} \subseteq Q_{\mathrm{SN}} \times Q_{\mathrm{HN}}$ under componentwise $\odot$ stabilizes at $112$ pairs, none of which lies in $F_{\mathrm{SN}} \times \{\infty_{\mathrm{HN}}\}$, reflecting $\mathrm{SN} \subsetneq \mathrm{HN}$ algebraically.
 $\square$

### 6.3. Global Top-Termination, Root Normal Forms, and Absence of Mute Terms

In untyped $\lambda$-calculus and full $\mathrm{CL}(S, K)$, unsolvable terms divide into those reducing to an application of unsolvable terms and *mute* (or root-active) terms in the sense of Berarducci [9, 8], such as $\Omega \equiv (\lambda x.\,x x)(\lambda x.\,x x) \to_r \Omega$. Waldmann [65] (see also [4, Theorem 29]) established via semantic labelling [76] that $\mathrm{CL}(S)$ is globally *top-terminating*: no infinite reduction sequence contracts at the root infinitely often. Using $\mathcal{A}_{\mathrm{HN}}$ and Lemma 6.5, we give a direct constructive proof yielding a total root-normalizing function $\mathrm{rnf}$.

**Theorem 6.7 (Constructive global top-termination and root normal forms [65]; [4, Theorem 29]).**

- (i) *Global top-termination:* Every open or closed $S$-term $M \in \mathcal{T}_S(\mathcal{V})$ is top-terminating: there exists no infinite sequence $M = M_0 \to_{\mathrm{nr}}^* M'_0 \to_r M_1 \to_{\mathrm{nr}}^* M'_1 \to_r \cdots$ containing infinitely many root contractions $\to_r$ interspersed with non-root steps $\to_{\mathrm{nr}}$.
- (ii) *Total root normalizer $\mathrm{rnf}$ and absence of Berarducci mute terms:* There is a total constructive procedure $\mathrm{rnf} : \mathcal{T}_S \to \mathrm{RNF}$ satisfying $M \to_S^* \mathrm{rnf}(M)$ for every $M \in \mathcal{T}_S$. Consequently, $\mathrm{CL}(S)$ contains no Berarducci mute terms [8]: every unsolvable closed $M \in \mathcal{T}_S \setminus \mathrm{HN}$ reduces to an applicative root normal form $P Q \in \mathrm{RNF}$ with $P \in \mathcal{T}_S \setminus \mathrm{HN}$, and every closed $S$-term possesses a $\bot$-free Berarducci tree $\operatorname{BeT}(M)$.
- (iii) *Root-step bound on $A A A$:* By Proposition 2.3(i), $\to_S^+$ is irreflexive on $\mathcal{T}_S(\mathcal{V})$; moreover, every multiway reduction starting from $A A A \equiv (S S S)(S S S)(S S S)$ executes at most $3$ root contractions, reaching its root normal form in $6$ deterministic head steps.

*Proof.* 
For (i), consider first closed $M \in \mathcal{T}_S$ with $\llbracket M \rrbracket_{\mathrm{HN}} \neq \infty_{\mathrm{HN}}$. Define the truncated potential $\nu_{\mathrm{HN}} : \mathcal{T}_S \to \mathbb{N}$ by $\nu_{\mathrm{HN}}(U) = 0$ if $\llbracket U \rrbracket_{\mathrm{HN}} = \infty_{\mathrm{HN}}$, $\nu_{\mathrm{HN}}(S) = 0$, and $\nu_{\mathrm{HN}}(L R) = \nu_{\mathrm{HN}}(L) + A(\llbracket L \rrbracket_{\mathrm{HN}}, \llbracket R \rrbracket_{\mathrm{HN}})\,\nu_{\mathrm{HN}}(R) + B(\llbracket L \rrbracket_{\mathrm{HN}}, \llbracket R \rrbracket_{\mathrm{HN}})$ whenever $\llbracket L R \rrbracket_{\mathrm{HN}} \neq \infty_{\mathrm{HN}}$. Because $A(u, \infty_{\mathrm{HN}}) = 0$ for all $u \in Q_{\mathrm{HN}}$ and $\infty_{\mathrm{HN}}$ is a left sink, $\nu_{\mathrm{HN}}$ agrees with $\mu_{\mathrm{HN}}$ modulo zeroing out $\infty_{\mathrm{HN}}$-subterms, which carry multiplier $0$ whenever they appear on the right of an accepted parent. By Lemma 6.5 and conversion invariance of $\llbracket \cdot \rrbracket_{\mathrm{HN}}$, every non-root step $N \to_{\mathrm{nr}} N'$ anywhere inside $N$ satisfies $\nu_{\mathrm{HN}}(N') \le \nu_{\mathrm{HN}}(N)$, while every root contraction $N \to_r N'$ on $\llbracket N \rrbracket_{\mathrm{HN}} \neq \infty_{\mathrm{HN}}$ satisfies $\nu_{\mathrm{HN}}(N') + 2 \le \nu_{\mathrm{HN}}(N)$. Thus $M$ executes at most $\lfloor \nu_{\mathrm{HN}}(M) / 2 \rfloor$ root contractions.

Next consider closed $M \in \mathcal{T}_S$ with $\llbracket M \rrbracket_{\mathrm{HN}} = \infty_{\mathrm{HN}}$. By Proposition 2.2(ii), right-spine depth $\operatorname{rs}$ satisfies $\operatorname{rs}(N) \le \operatorname{rs}(N')$ for every non-root step $N \to_{\mathrm{nr}} N'$, whereas every root contraction $S X Y Z \to_r (X Z)(Y Z)$ yields $\operatorname{rs}((X Z)(Y Z)) = \operatorname{rs}(S X Y Z) + 1$. Stratifying $Q_{\mathrm{HN}}$ into nested root-contraction capacity classes $G_{\ge 0} \supset G_{\ge 1} \supset \dots \supset G_{\ge 5}$ of cardinalities $(35, 34, 26, 18, 17, 16)$ and tracking the maximal strongly connected spine prefixes on $\infty_{\mathrm{HN}}$ once $\operatorname{rs}(N) \ge 6$ shows that at most finitely many root steps can occur before the left child of $N \equiv P Q$ locks permanently into $\infty_{\mathrm{HN}}$, where Theorem 6.6(ii) forces $N \in \mathrm{RNF}$. For an arbitrary open term $M \in \mathcal{T}_S(\mathcal{V})$, the variable-erasing homomorphism $\sigma_S : \mathcal{T}_S(\mathcal{V}) \to \mathcal{T}_S$ sending every $v \in \mathcal{V}$ to $S$ maps root steps to root steps and non-root steps to non-root steps, lifting well-foundedness of $\to_{\mathrm{nr}}^* \cdot \to_r$ from $\mathcal{T}_S$ to $\mathcal{T}_S(\mathcal{V})$.

For (ii), well-founded recursion on the relative root relation $\to_{\mathrm{nr}}^* \cdot \to_r$ defines $\mathrm{rnf}(M)$: check whether $M \in \mathrm{RNF}$ in $O(|M|)$ time via Theorem 6.6(ii); if so, return $M$; otherwise $M \equiv P Q$ has $\operatorname{ls}(P) \ge 2$ and $\llbracket P \rrbracket_{\mathrm{HN}} \neq \infty_{\mathrm{HN}}$, so head-normalizing $P \to_h^* S X Y$ within $\lfloor \mu_{\mathrm{HN}}(P)/2 \rfloor$ steps and contracting $(S X Y) Q \to_r (X Q)(Y Q)$ performs one relative root step, allowing recursive invocation $\mathrm{rnf}((X Q)(Y Q))$. If $M \in \mathcal{T}_S \setminus \mathrm{HN}$, then $\mathrm{rnf}(M) \in \mathrm{RNF} \setminus \mathrm{HN}$ cannot satisfy $\operatorname{ls}(\mathrm{rnf}(M)) \le 2$, so by (6.10) it has the form $P Q$ with $\llbracket P \rrbracket_{\mathrm{HN}} = \infty_{\mathrm{HN}}$. Coinductively unfolding $\mathrm{rnf}$ on $P$ and $Q$ generates a total $\bot$-free Berarducci tree $\operatorname{BeT}(M)$, proving the absence of mute terms.

For (iii), for $A A A \equiv (S S S)(S S S)(S S S)$ we have $\operatorname{rs}(A A A) = 2$, and finite enumeration of the root-contracting reachable cone confirms that $A A A$ admits at most $3$ root contractions along any multiway path, reaching the root normal form $\bigl((S A A)\,(S A (S A A))\bigr)\bigl(S(S A A)\,(S A (S A A))\bigr)$ in $6$ deterministic head steps.
 $\square$

### 6.4. Regularity of Böhm-Tree Productivity and Resolution of Question 5

Recall from Definition 2.4(iii)–(iv) and Lemma 2.5 that a closed $S$-term $M \in \mathcal{T}_S$ is *productive* ($M \in \mathrm{Prod}$) when $\operatorname{BT}(M)$ contains no occurrence of $\bot$ at any finite depth—formally, when $\neg\bot_d(M)$ holds for all $d \in \mathbb{N}$—and that $\bot_d$ is conversion-invariant and monotone in $d$ ($\bot_d(M)$ implies $\bot_{d+1}(M)$). Every strongly normalizing term is productive because its normal form is a finite $\bot$-free Böhm tree. As discovered by Zachos [75] (see [4, p. 80]), $\mathrm{Prod}$ strictly contains $\mathrm{SN}$: defining the normal-form tower

$$
G_0 \;\equiv\; S T T \;\equiv\; S(S S)(S S),
\qquad
G_{k+1} \;\equiv\; T G_k \;\equiv\; (S S)\,G_k
\qquad (k \in \mathbb{N}), \tag{6.11}
$$

we have $G_0 G_n \equiv S T T G_n \to_h (T G_n)(T G_n) \equiv G_{n+1} G_{n+1}$ and $G_{k+1} G_m \equiv S S G_k G_m \to_h S G_m (G_k G_m) \in \mathrm{HNF}$ (whose left child $G_m$ lies in $\mathcal{N}$), so $Z_{\mathrm{Zac}} \equiv G_0 G_0$ ($10$ leaves) is non-normalizing yet generates an infinite $\bot$-free Böhm tree. Question 5 of Barendregt et al. [4, p. 80] asks how to characterize $\mathrm{Prod}$, whether $\mathrm{Prod}$ is regular, and whether productivity is decidable.

Our resolution of Question 5 rests on two structural lemmas showing how non-erasure in $\mathrm{CL}(S)$ forces $\bot$ to propagate across both sides of binary application, and why Zachos pairs $G_m G_n$ lose productivity upon receiving any further right argument.

**Lemma 6.8 (Left and right $\bot$-propagation on closed $S$-terms).** 
For every depth $d \in \mathbb{N}$ and all closed $S$-terms $Y, Z, F, W \in \mathcal{T}_S$:

$$
\bot_d(Y) \;\Longrightarrow\; \bot_d(Y Z)
\qquad\textrm{and}\qquad
\bot_d(W) \;\Longrightarrow\; \bot_{d+1}(F W). \tag{6.12}
$$

Consequently, $M N \in \mathrm{Prod}$ implies both $M \in \mathrm{Prod}$ and $N \in \mathrm{Prod}$.

*Proof.* 
Consider first an invariant of head reduction on open $\{S, x_0\}$-terms: writing the left spine of $U$ as $U \equiv h\,U_1 \dots U_r$ ($h \in \{S, x_0\}$, $r \ge 0$), define $\mathrm{hasX}(U)$ to hold if either $h = x_0$ or there exists $i \in \{1, \dots, r\}$ whose leftmost leaf is $x_0$. Under a root head step $S A_1 A_2 A_3 \to_h (A_1 A_3)(A_2 A_3)$, the left-spine arguments of $(A_1 A_3)(A_2 A_3)$ consist of the left-spine arguments of $A_1$, followed by $A_3$, followed by $A_2 A_3$:

- if the leftmost leaf of $A_1$ is $x_0$, then the leftmost leaf of $(A_1 A_3)(A_2 A_3)$ is $x_0$;
- if the leftmost leaf of $A_2$ is $x_0$, then the leftmost leaf of the final spine argument $A_2 A_3$ is $x_0$;
- if the leftmost leaf of $A_3$ is $x_0$, then the spine argument $A_3$ itself appears on the left spine of $(A_1 A_3)(A_2 A_3)$ with leftmost leaf $x_0$.

Inductive left steps $L R \to_h L' R$ append $R$ to the spine of $L'$, preserving $\mathrm{hasX}$ unconditionally. Since $F x_0$ (for closed $F \in \mathcal{T}_S$) satisfies $\mathrm{hasX}(F x_0)$ via its final spine argument $x_0$, whenever $\llbracket F W \rrbracket_{\mathrm{HN}} \neq \infty_{\mathrm{HN}}$, substituting $x_0 \mapsto W$ shows that head reduction of $F x_0$ terminates within $\lfloor \mu_{\mathrm{HN}}(F W)/2 \rfloor$ steps at an open head normal form $U^*$ satisfying $\mathrm{hasX}(U^*)$. Because $U^*$ contains only $\{S, x_0\}$ and lies in head normal form, either: (a) $U^*$ has head leaf $x_0$; (b) $U^* \equiv S A_1$ where $A_1$ has head leaf $x_0$; or (c) $U^* \equiv S A_1 A_2$ where $A_1$ or $A_2$ has head leaf $x_0$.

Consequently, at any fixed depth $d$, left propagation at depth $d$ implies right propagation at depth $d$: if $\llbracket F W \rrbracket_{\mathrm{HN}} = \infty_{\mathrm{HN}}$, then $\bot_0(F W)$ gives $\bot_{d+1}(F W)$ by monotonicity; otherwise $F W \equiv (F x_0)[x_0 := W] \to_S^* U^*[x_0 := W]$, and any subterm $K$ with head leaf $x_0$ substitutes to $W K_1[x_0 := W] \dots K_m[x_0 := W]$, which satisfies $\bot_d$ by $m$-fold application of left propagation at depth $d$, placing $\bot_d$ either at $U^*[x_0 := W]$ itself in case (a) or in a direct child of the head normal form $U^*[x_0 := W]$ in cases (b)–(c), yielding $\bot_{d+1}(F W)$ by Lemma 2.5.

We now prove both laws in (6.12) simultaneously by induction on $d \in \mathbb{N}$.

- (i) For $d = 0$, if $\bot_0(Y)$, Theorem 6.6(i) gives $\llbracket Y \rrbracket_{\mathrm{HN}} = \infty_{\mathrm{HN}}$, so $\llbracket Y Z \rrbracket_{\mathrm{HN}} = \infty_{\mathrm{HN}} \odot_{\mathrm{HN}} \llbracket Z \rrbracket_{\mathrm{HN}} = \infty_{\mathrm{HN}}$ by (6.4), giving $\bot_0(Y Z)$. Right propagation at $d = 0$ follows by the reduction above.
- (ii) For $d + 1$, assume both laws in (6.12) hold at depth $d$, and suppose $\bot_{d+1}(Y)$. If $Y \notin \mathrm{HN}$, then $Y Z \notin \mathrm{HN}$ as in the base case, giving $\bot_{d+1}(Y Z)$. If $Y \to_S^* S A_1$ with $\bot_d(A_1)$, then $Y Z \to_S^* S A_1 Z \in \mathrm{HNF}$ has first child $A_1$, giving $\bot_{d+1}(Y Z)$. If $Y \to_S^* S A_1 A_2$ with $\bot_d(A_1)$, then $Y Z \to_S^* (S A_1 A_2) Z \to_S (A_1 Z)(A_2 Z)$; two applications of the depth-$d$ left-propagation hypothesis yield $\bot_d(A_1 Z)$ and $\bot_d((A_1 Z)(A_2 Z))$, whence $\bot_{d+1}(Y Z)$. Finally, if $Y \to_S^* S A_1 A_2$ with $\bot_d(A_2)$, the depth-$d$ left-propagation hypothesis yields $\bot_d(A_2 Z)$, and the depth-$d$ right-propagation hypothesis applied to $(A_1 Z)(A_2 Z)$ yields $\bot_{d+1}((A_1 Z)(A_2 Z))$, whence $\bot_{d+1}(Y Z)$ by Lemma 2.5. Right propagation at $d + 1$ then follows from left propagation at $d + 1$. 

$\square$

**Lemma 6.9 (Zachos right-application $\bot$-absorption).** 
Let $G_k$ ($k \in \mathbb{N}$) be Zachos's normal-form tower (6.11). For all $m, n \in \mathbb{N}$ and every closed $S$-term $U \in \mathcal{T}_S$, there exists $d \in \mathbb{N}$ such that $\bot_d\bigl((G_m G_n) U\bigr)$; in particular, $(G_m G_n) U \notin \mathrm{Prod}$.

*Proof.* 
We first establish an auxiliary claim by induction on $n \in \mathbb{N}$: for any closed $Z, W \in \mathcal{T}_S$, if $\llbracket (G_0 Z) W \rrbracket_{\mathrm{HN}} = \infty_{\mathrm{HN}}$, then there exists $d \in \mathbb{N}$ with $\bot_d((G_n Z) W)$. For $n = 0$, Theorem 6.6(i) directly gives $\bot_0((G_0 Z) W)$. For $n + 1$, expanding $G_{n+1} \equiv S S G_n$ gives the two-step reduction

$$
(G_{n+1} Z) W \;\equiv\; (S S G_n Z) W \;\to_S\; \bigl(S Z (G_n Z)\bigr) W \;\to_S\; (Z W)\bigl((G_n Z) W\bigr).
$$

By the induction hypothesis, $\bot_d((G_n Z) W)$ holds for some $d$; applying Lemma 6.8 to $(Z W)((G_n Z) W)$ yields $\bot_{d+1}\bigl((Z W)((G_n Z) W)\bigr)$, and Lemma 2.5 gives $\bot_{d+1}((G_{n+1} Z) W)$.

Now consider $(G_m G_n) U$ for $m = k + 1 \ge 1$. Two contractions yield $(G_{k+1} G_n) U \to_S^2 (G_n U)\bigl((G_k G_n) U\bigr)$. Set $W \equiv (G_k G_n) U$. In $\mathcal{A}_{\mathrm{HN}}$, one computes $\llbracket G_0 \rrbracket_{\mathrm{HN}} = q_{16}$ and $\llbracket G_{r+1} \rrbracket_{\mathrm{HN}} = q_{13}$ for all $r \ge 0$, whence $\llbracket G_k G_n \rrbracket_{\mathrm{HN}} \in \{ q_{16} \odot_{\mathrm{HN}} q_{16}, q_{16} \odot_{\mathrm{HN}} q_{13}, q_{13} \odot_{\mathrm{HN}} q_{16}, q_{13} \odot_{\mathrm{HN}} q_{13} \} = \{q_{23}, q_{24}\}$. Inspection of rows $q_{23}$ and $q_{24}$ of $\mathcal{A}_{\mathrm{HN}}$ shows that for every $h = \llbracket U \rrbracket_{\mathrm{HN}} \in Q_{\mathrm{HN}}$, both $q_{23} \odot_{\mathrm{HN}} h$ and $q_{24} \odot_{\mathrm{HN}} h$ belong to $\{q_{23}, \infty_{\mathrm{HN}}\}$, so $\llbracket W \rrbracket_{\mathrm{HN}} \in \{q_{23}, \infty_{\mathrm{HN}}\}$. Moreover, for every $h \in Q_{\mathrm{HN}}$, the state $s = q_{16} \odot_{\mathrm{HN}} h = \llbracket G_0 U \rrbracket_{\mathrm{HN}}$ satisfies $s \odot_{\mathrm{HN}} q_{23} = \infty_{\mathrm{HN}}$ and $s \odot_{\mathrm{HN}} \infty_{\mathrm{HN}} = \infty_{\mathrm{HN}}$, giving $\llbracket (G_0 U) W \rrbracket_{\mathrm{HN}} = \infty_{\mathrm{HN}}$. By the auxiliary claim above, $(G_n U) W$ satisfies $\bot_d$ for some $d$, so $(G_{k+1} G_n) U$ satisfies $\bot_d$. Finally, for $m = 0$, we have $(G_0 G_n) U \equiv (S T T G_n) U \to_S (G_{n+1} G_{n+1}) U$, reducing immediately to the case $m = n + 1 \ge 1$.
 $\square$

We now define the $39$-state productivity $S$-algebra $\mathcal{A}_P = (Q_P, q_0, \odot_P)$ with carrier $Q_P = \{q_0, q_1, \dots, q_{36}, \infty_P, q_{38}\}$ (identifying the unique rejecting sink as $\infty_P = q_{37}$ and the accepting set as $F_P = Q_P \setminus \{\infty_P\}$, $|F_P| = 38$). Direct verification over all $39^3 = 59{,}319$ triples confirms (2.1), and $\infty_P$ is a two-sided sink ($\infty_P \odot_P y = x \odot_P \infty_P = \infty_P$), matching Lemma 6.8 algebraically, while row $q_{29}$ satisfies $q_{29} \odot_P y = \infty_P$ for every $y \in Q_P$, matching Lemma 6.9 since $\llbracket G_m G_n \rrbracket_P = q_{29}$.

**Proposition 6.10 (Coinductive soundness of $\mathcal{A}_P$ and $34$-of-$38$ strong-normalization stratification).**

- (i) *HNF closure and soundness:* For all $x, y \in Q_P$, one has $q_0 \odot_P x \in F_P$ if and only if $x \in F_P$, and $(q_0 \odot_P x) \odot_P y \in F_P$ if and only if both $x \in F_P$ and $y \in F_P$. Every closed $S$-term $M$ with $\llbracket M \rrbracket_P \neq \infty_P$ satisfies $\llbracket M \rrbracket_{\mathrm{HN}} \neq \infty_{\mathrm{HN}}$ and $M \in \mathrm{Prod}$.
- (ii) *Non-isomorphism with $\mathcal{A}_{\mathrm{SN}}$ and unique non-$\mathrm{SN}$ root-redex fiber:* Although $|Q_P| = |Q_{\mathrm{SN}}| = 39$, the reachable subalgebra of $\mathcal{A}_P \times \mathcal{A}_{\mathrm{SN}}$ has $44$ states. Out of the $38$ accepting states of $\mathcal{A}_P$, $34$ states—every $q \in F_P \setminus \{q_{18}, q_{24}, q_{29}, q_{33}\}$—pair exclusively with $F_{\mathrm{SN}}$ and therefore contain only strongly normalizing terms. Furthermore, every term in $(q_{18}, \infty_{\mathrm{SN}})$, $(q_{24}, \infty_{\mathrm{SN}})$, or $(q_{33}, \infty_{\mathrm{SN}})$ reduces to a spine-$1$ or spine-$2$ $\mathrm{HNF}$ without executing any root contraction, leaving $(q_{29}, \infty_{\mathrm{SN}})$ as the unique non-$\mathrm{SN}$ productive root-redex state pair in $\mathrm{CL}(S)$.

*Proof.* 
For (i), the $\mathrm{HNF}$ biconditionals hold by direct inspection of $\odot_P$. Reachable closure of $(q_0, q_0) \in Q_P \times Q_{\mathrm{HN}}$ yields $113$ pairs ($95$ with $\llbracket M \rrbracket_P \in F_P$ and $18$ with $\llbracket M \rrbracket_P = \infty_P$), and $(\infty_P, \infty_{\mathrm{HN}})$ is the sole pair whose second coordinate is $\infty_{\mathrm{HN}}$; hence $\llbracket M \rrbracket_P \neq \infty_P$ implies $\llbracket M \rrbracket_{\mathrm{HN}} \neq \infty_{\mathrm{HN}}$. We prove by induction on $d \in \mathbb{N}$ that $\llbracket M \rrbracket_P \neq \infty_P$ implies $\neg\bot_d(M)$. At $d = 0$, $\llbracket M \rrbracket_{\mathrm{HN}} \neq \infty_{\mathrm{HN}}$ refutes $M \notin \mathrm{HN}$ by Theorem 6.6(i); at $d + 1$, if $M \to_S^* S A_1 \dots A_k$ ($1 \le k \le 2$), conversion invariance gives $\llbracket S A_1 \dots A_k \rrbracket_P = \llbracket M \rrbracket_P \in F_P$, so the $\mathrm{HNF}$ biconditionals give $\llbracket A_i \rrbracket_P \in F_P$ and hence $\neg\bot_d(A_i)$ for each $i$ by the depth-$d$ induction hypothesis. Thus $\neg\bot_d(M)$ holds for all $d \in \mathbb{N}$.

For (ii), reachable closure of $(q_0, q_0) \in Q_P \times Q_{\mathrm{SN}}$ produces $44$ pairs, of which only $(q_{18}, \infty_{\mathrm{SN}})$, $(q_{24}, \infty_{\mathrm{SN}})$, $(q_{29}, \infty_{\mathrm{SN}})$, $(q_{33}, \infty_{\mathrm{SN}})$, and $(\infty_P, \infty_{\mathrm{SN}})$ have second coordinate $\infty_{\mathrm{SN}}$; Theorem 6.2 implies all other $34$ states of $F_P$ inhabit $\mathrm{SN}$. Inspecting all joint transition pairs $(u, v) \mapsto u \odot v$ landing in $(q_{18}, \infty_{\mathrm{SN}})$, $(q_{24}, \infty_{\mathrm{SN}})$, or $(q_{33}, \infty_{\mathrm{SN}})$ reveals that in every such application $L R$, the left child $L$ satisfies $\llbracket L \rrbracket_{\mathrm{SN}} \neq \infty_{\mathrm{SN}}$ and normalizes to $S$ or $S U$, so $L R \to_S^* S R$ or $S U R \in \mathrm{HNF}$ without root contractions. Only $(q_{29}, \infty_{\mathrm{SN}})$ admits non-$\mathrm{SN}$ root-contracting terms, such as $Z_{\mathrm{Zac}} \equiv G_0 G_0$ and $Z_0 \equiv S(S T)(S T)T$.
 $\square$

To prove completeness (that $\llbracket M \rrbracket_P = \infty_P$ implies $\bot_d(M)$ for some $d \in \mathbb{N}$), we replace normal forms $\mathcal{N}$ by a grammar of *canonical productive values* $\mathcal{V}_P \subset \mathcal{T}_S$ that internalizes the unique non-$\mathrm{SN}$ productive root-redex family $G_m G_n$ directly as a value constructor:

$$
\mathcal{V}_P \;::=\; S \;\mid\; S V \;\mid\; S V_1 V_2 \;\mid\; G_m G_n
\qquad (V, V_1, V_2 \in \mathcal{V}_P,\; m, n \in \mathbb{N}). \tag{6.13}
$$

**Lemma 6.11 (Syntactic rigidity of $\mathcal{V}_P$ and rank-$6$ canonical normalization).** 
Every $V \in \mathcal{V}_P$ satisfies $\llbracket V \rrbracket_P \in F_P$, and $\mathcal{V}_P$ obeys three syntactic rigidity laws:

$$
\llbracket V \rrbracket_P = q_0 \Longrightarrow V \equiv S,
\qquad
\llbracket V \rrbracket_P = q_1 \Longrightarrow V \equiv T \equiv S S,
\qquad
\llbracket V \rrbracket_P \in \{q_{14}, q_{32}\} \Longrightarrow \exists k \in \mathbb{N},\; V \equiv G_k. \tag{6.14}
$$

Moreover, there is a constructive rank-$6$ application operator $\mathrm{app}_{\mathcal{V}_P}(V_1, V_2) \in \mathcal{V}_P$ defined for all $V_1, V_2 \in \mathcal{V}_P$ with $\llbracket V_1 \rrbracket_P \odot_P \llbracket V_2 \rrbracket_P \neq \infty_P$ such that $V_1 V_2 \to_S^* \mathrm{app}_{\mathcal{V}_P}(V_1, V_2)$; consequently, every closed $M \in \mathcal{T}_S$ with $\llbracket M \rrbracket_P \neq \infty_P$ reduces constructively to some $V \in \mathcal{V}_P$.

*Proof.* 
Because $\llbracket G_0 \rrbracket_P = q_{14}$, $\llbracket G_{k+1} \rrbracket_P = q_{32}$, and $\llbracket G_m G_n \rrbracket_P = q_{29} \in F_P$, structural induction on (6.13) via Proposition 6.10(i) confirms $\llbracket V \rrbracket_P \in F_P$ for all $V \in \mathcal{V}_P$. For (6.14), we induct on $V \in \mathcal{V}_P$: $q_0$ never lies in the image of $\odot_P$, forcing $V \equiv S$; the sole pair $(a, b) \in Q_P^2$ with $a \odot_P b = q_1$ is $(q_0, q_0)$, forcing $V \equiv S S \equiv T$; the sole spine-$2$ transition $(q_0 \odot_P x) \odot_P y \in \{q_{14}, q_{32}\}$ is $(q_0 \odot_P q_1) \odot_P q_1 = q_2 \odot_P q_1 = q_{14}$, which by the $q_1$ case forces $V \equiv S T T \equiv G_0$; and the sole spine-$1$ or non-spine-$2$ transition landing in $\{q_{14}, q_{32}\}$ from $\mathcal{V}_P$ is $q_1 \odot_P y = q_{32}$ for $y \in \{q_{14}, q_{32}\}$ (since $G_m G_n$ has state $q_{29} \notin \{q_0, q_1, q_{14}, q_{32}\}$), which by the induction hypothesis forces $V \equiv T G_k \equiv G_{k+1}$.

To define $\mathrm{app}_{\mathcal{V}_P}(V_1, V_2)$ when $\llbracket V_1 \rrbracket_P \odot_P \llbracket V_2 \rrbracket_P \neq \infty_P$, observe first that $V_1$ can never be $G_m G_n$, because $\llbracket G_m G_n \rrbracket_P = q_{29}$ and $q_{29} \odot_P z = \infty_P$ for all $z \in Q_P$. If $V_1 \equiv S$ or $V_1 \equiv S U$, then $V_1 V_2 \in \mathcal{V}_P$ directly. If $V_1 \equiv S X Y$ with $X, Y \in \mathcal{V}_P$, inspect the cases entering the Zachos stream: the only pairs $(u, z) \in F_P^2$ where a spine-$2$ state $u = (q_0 \odot_P x) \odot_P y$ transitions via non-terminating Zachos core products to $q_{29}$ are $x = y = q_1$ ($V_1 \equiv S T T \equiv G_0$) with $z \in \{q_{14}, q_{32}\}$ ($V_2 \equiv G_n$ by (6.14)), for which $V_1 V_2 \equiv G_0 G_n \in \mathcal{V}_P$ directly, and $V_1 \equiv T G_k \equiv S S G_k$ ($u = q_{32}$) with $z \in \{q_{14}, q_{32}\}$ ($V_2 \equiv G_n$), for which $(S S G_k) G_n \to_S S G_n (G_k G_n) \in \mathcal{V}_P$ in one step because both $G_n \in \mathcal{V}_P$ and $G_k G_n \in \mathcal{V}_P$. Outside these Zachos constructors, an explicit rank function $\tau_P : Q_P^3 \to \{0, 1, \dots, 6\}$ over the $1{,}882$ active triples satisfies exact analogues of (6.2)–(6.3), terminating by lexicographic induction on $(\tau_P, |V_1| + |V_2|)$ because every structural recursive call on $X$ or $Y$ of $S X Y$ strictly decreases tree size even when $X$ or $Y$ contains a $G_m G_n$ subterm. Structural induction on $M \in \mathcal{T}_S$ using the two-sided sink property of $\infty_P$ then reduces every accepted $M$ to $\mathcal{V}_P$.
 $\square$

**Theorem 6.12 (Regularity of Böhm-tree productivity and resolution of Question 5 [4, p. 80]).** 
For every closed $S$-term $M \in \mathcal{T}_S$,

$$
M \in \mathrm{Prod} \;\Longleftrightarrow\; \llbracket M \rrbracket_P \neq \infty_P, \tag{6.15}
$$

so the set $\mathrm{Prod}$ of productive closed $S$-terms is a regular tree language decidable in $2|M| - 1$ deterministic table lookups. Constructively, for every closed $M \in \mathcal{T}_S$, either $M \in \mathrm{Prod}$ or there exists an explicit bound $d \in \mathbb{N}$ such that $\bot_d(M)$.

*Proof.* 
Soundness (that $\llbracket M \rrbracket_P \neq \infty_P$ implies $M \in \mathrm{Prod}$) was proved in Proposition 6.10(i). For constructive completeness, since $\llbracket M \rrbracket_P \in Q_P$ is decidable, it suffices to construct a depth witness $d \in \mathbb{N}$ with $\bot_d(M)$ whenever $\llbracket M \rrbracket_P = \infty_P$.

First, we induct structurally on $M$ with $\llbracket M \rrbracket_P = \infty_P$: since $\llbracket S \rrbracket_P = q_0 \neq \infty_P$, we have $M \equiv L R$. If $\llbracket L \rrbracket_P = \infty_P$, the induction hypothesis yields $\bot_d(L)$ and Lemma 6.8 gives $\bot_d(L R)$; if $\llbracket R \rrbracket_P = \infty_P$, the induction hypothesis yields $\bot_d(R)$ and Lemma 6.8 gives $\bot_{d+1}(L R)$. We are therefore reduced to the critical entry frontier where $\llbracket L \rrbracket_P \in F_P$, $\llbracket R \rrbracket_P \in F_P$, and $\llbracket L \rrbracket_P \odot_P \llbracket R \rrbracket_P = \infty_P$. Applying Lemma 6.11 normalizes $L \to_S^* V_1 \in \mathcal{V}_P$ and $R \to_S^* V_2 \in \mathcal{V}_P$; by Lemma 2.5, it suffices to exhibit $d \in \mathbb{N}$ with $\bot_d(V_1 V_2)$ for all $V_1, V_2 \in \mathcal{V}_P$ satisfying $\llbracket V_1 V_2 \rrbracket_P = \infty_P$.

If $V_1 \equiv G_m G_n$, Lemma 6.9 yields $\bot_d((G_m G_n) V_2)$ for some $d \in \mathbb{N}$. Since $V_1 \equiv S$ and $V_1 \equiv S U$ ($U \in \mathcal{V}_P$) satisfy $\llbracket V_1 V_2 \rrbracket_P \in F_P$ by Proposition 6.10(i), every remaining critical pair has $V_1 \equiv S X Y$ with $X, Y, V_2 \in \mathcal{V}_P$, contracting in one step to $(X V_2)(Y V_2)$.

To prove termination of $\bot$-extraction across all such triples without König's lemma, we work over the $113$-state reachable subalgebra $\mathrm{PH} \subseteq Q_P \times Q_{\mathrm{HN}}$ ($95$ accepting states $\mathrm{PH}_{\mathrm{acc}}$ partitioned into $\{(q_0, q_0)\}$, $23$ arity-$1$ states, and $71$ arity-$2$ or Zachos states; $17$ solvable rejecting states; and $(\infty_P, \infty_{\mathrm{HN}})$). If $\llbracket (S X Y) V_2 \rrbracket_{\mathrm{HN}} = \infty_{\mathrm{HN}}$, then $\bot_0((S X Y) V_2)$ holds directly. Otherwise, letting $\mathbf{x} = \llbracket X \rrbracket_{\mathrm{PH}}$, $\mathbf{y} = \llbracket Y \rrbracket_{\mathrm{PH}}$, and $\mathbf{z} = \llbracket V_2 \rrbracket_{\mathrm{PH}} \in \mathrm{PH}_{\mathrm{acc}}$, the contracted children $(X V_2)$ and $(Y V_2)$ divide into three cases:

- (i) *Left absorption ($\llbracket X V_2 \rrbracket_P = \infty_P$):* Exhibiting $\bot_d(X V_2)$ lifts via Lemma 6.8 to $\bot_d((X V_2)(Y V_2))$.
- (ii) *Right absorption ($\llbracket X V_2 \rrbracket_P \neq \infty_P$ and $\llbracket Y V_2 \rrbracket_P = \infty_P$):* Exhibiting $\bot_d(Y V_2)$ lifts via Lemma 6.8 to $\bot_{d+1}((X V_2)(Y V_2))$.
- (iii) *Joint critical transition ($\llbracket X V_2 \rrbracket_P \neq \infty_P$, $\llbracket Y V_2 \rrbracket_P \neq \infty_P$, and $\llbracket (X V_2)(Y V_2) \rrbracket_P = \infty_P$):* Lemma 6.11 normalizes $X V_2 \to_S^* W_1 \in \mathcal{V}_P$ and $Y V_2 \to_S^* W_2 \in \mathcal{V}_P$, producing a critical pair $(W_1, W_2)$; when $X \equiv S U$ ($U \in \mathcal{V}_P$), $(S U V_2)(Y V_2)$ reduces directly via $(S(S U)Y)V_2 \to_S^2 (U(Y V_2))(V_2(Y V_2)) \to_S^* (U W_2)(V_2 W_2)$.

Recording for each pair $(\mathbf{x}, \mathbf{z}) \in \mathrm{PH}_{\mathrm{acc}}^2$ the finite set $\mathrm{out}_{2\mathrm{d}}(\mathbf{x}, \mathbf{z}) \subseteq \mathrm{PH}_{\mathrm{acc}}^2$ of state pairs $(\llbracket A_1 \rrbracket_{\mathrm{PH}}, \llbracket A_2 \rrbracket_{\mathrm{PH}})$ attainable when $\mathrm{app}_{\mathcal{V}_P}(X, V_2) \equiv S A_1 A_2$ allows all $4{,}899$ root critical pairs ($80{,}193$ reachable critical triples) to be stratified by two explicit integer rank tables bounded by $17$ ($5{,}072$ entries for critical pairs $(\mathbf{u}, \mathbf{z})$ and $10{,}067$ entries across $826$ pairs $(\mathbf{x}, \mathbf{z})$ for joint critical transitions). Every recursive call strictly decreases the well-founded lexicographic measure in $\{0, \dots, 17\} \times \{0, \dots, 17\} \times \mathbb{N}$, yielding an explicit finite depth $d$ with $\bot_d(V_1 V_2)$ in every branch.
 $\square$

Even at leaf size $8$, completeness of $\mathcal{A}_P$ requires selective branch choice: chasing the leftmost unproductive child of each $\mathrm{HNF}$ can loop forever without visiting $\infty_{\mathrm{HN}}$.

**Proposition 6.13 (Böhm-game branch asymmetry at leaf size $8$).** 
Consider the $8$-leaf closed $S$-term $L_{\mathrm{loop}} \equiv S T S T T \equiv S(S S)S(S S)(S S)$, which satisfies $\llbracket L_{\mathrm{loop}} \rrbracket_P = \infty_P$ and $\llbracket L_{\mathrm{loop}} \rrbracket_{\mathrm{HN}} = q_{24} \neq \infty_{\mathrm{HN}}$. Under the rightmost-unproductive Böhm strategy (head-normalizing and selecting the rightmost spine child having $P$-state $\infty_P$), $L_{\mathrm{loop}}$ reaches $\infty_{\mathrm{HN}}$ in $4$ steps, witnessing $\bot_4(L_{\mathrm{loop}})$. Under the leftmost-unproductive Böhm strategy, by contrast, $L_{\mathrm{loop}}$ never reaches $\infty_{\mathrm{HN}}$, cycling forever through solvable terms $K_0 K_n \mapsto^{n+2} K_0 K_{n+1}$ ($n \ge 1$), where $K_0 \equiv S S (S T)T$ and $K_{m+1} \equiv T K_m$ satisfy $|K_m| = 2m + 7 \to \infty$.

*Proof.* 
Set $G_0 \equiv S T T$, $K_0 \equiv S S (S T) T \equiv T(S T)T$, and $K_{m+1} \equiv T K_m \in \mathcal{N}$ ($\llbracket K_m \rrbracket_P \in F_P$). Five deterministic head steps reduce $L_{\mathrm{loop}}$ to a spine-$2$ head normal form:

$$
S T S T T
\;\longrightarrow_h\; (T T)(S T)T
\;\longrightarrow_h\; S(S T)\bigl(T(S T)\bigr)T
\;\longrightarrow_h\; G_0\,K_0
\;\longrightarrow_h\; K_1\,K_1
\;\longrightarrow_h\; S\,K_1\,(K_0 K_1) \;\in\; \mathrm{HNF}.
$$

Because $\llbracket K_1 \rrbracket_P \in F_P$ and $\llbracket K_0 K_1 \rrbracket_P = \infty_P$, the first step of both the leftmost- and rightmost-unproductive strategies enters $K_0 K_1$. For every $n \ge 1$, three head contractions yield

$$
K_0 K_n \;\equiv\; (S S (S T) T)\,K_n
\;\longrightarrow_h\; (S T G_0)\,K_n
\;\longrightarrow_h\; (T K_n)(G_0 K_n)
\;\longrightarrow_h\; S\,(G_0 K_n)\,\bigl(K_n(G_0 K_n)\bigr) \;\in\; \mathrm{HNF},
$$

in which both spine children $G_0 K_n$ and $K_n(G_0 K_n)$ evaluate to $\infty_P$ in $\mathcal{A}_P$. At $n = 1$, the rightmost-unproductive strategy selects $K_1(G_0 K_1)$, which in two further Böhm transitions reaches $(G_0 K_1)\bigl(G_0(G_0 K_1)\bigr)$, a term of $\mathrm{HN}$ state $\infty_{\mathrm{HN}}$, certifying $\bot_4(L_{\mathrm{loop}})$. Conversely, for every $n \ge 1$, the leftmost-unproductive strategy selects $G_0 K_n \equiv S T T K_n \to_h^2 S\,K_{n+1}\,(K_n K_{n+1}) \in \mathrm{HNF}$, whose sole $\infty_P$-child is $K_n K_{n+1}$; $n$ subsequent head-normalizations $K_{m+1} K_{n+1} \equiv S S K_m K_{n+1} \to_h S\,K_{n+1}\,(K_m K_{n+1})$ ($m = n - 1, \dots, 0$) each have productive left child $K_{n+1} \in \mathcal{N}$ and return to $K_0 K_{n+1}$ in $n + 2$ Böhm steps without ever visiting $\infty_{\mathrm{HN}}$.
 $\square$

### 6.5. Refinement Alternation (Question 7), Böhm Unfaithfulness (Question 31), and Closed-$\mathrm{SN}$ Convertibility (Question 30)

We conclude Section 6 by resolving Questions 7 and 31 of Barendregt, Endrullis, Klop, and Waldmann [4, pp. 81, 93] and situating closed-$\mathrm{SN}$ convertibility within the study of single-combinator word problems and reduction complexity [54, 14, 56, 57] (Scott's Question 30). Whereas Statman established general basis obstructions for single combinators [56] and proved decidability of the word problem for Smullyan's lark combinator $L x y \to x(y y)$ [57], decidability of unrestricted $=_S$ on $\mathrm{CL}(S)$ remains open; Proposition 6.16 below characterizes $=_S$ via Gross–Knuth cofinality and resolves the closed normalizing fragment.

In Question 7 (the “colour change” or refinement puzzle [4, p. 81]), Barendregt et al. observe that replacing an $S$-leaf inside an $S$-term by a larger closed $S$-term can turn a non-normalizing term into a normalizing one, and ask whether an infinite chain of successive leaf refinements can alternate forever between $\mathrm{SN}$ and $\mathcal{T}_S \setminus \mathrm{SN}$, and which closed plugs can rescue non-normalizing contexts in a single step.

**Theorem 6.14 (Infinite refinement alternation and rescue classification, Question 7 [4, p. 81]).** 
Recall $T \equiv S S$ and $A \equiv S S S$, and define the context gadget $R(X) \equiv X A S A$.

- (i) *Infinite $\mathrm{SN} / \overline{\mathrm{SN}}$ refinement chain:* One has $R(S) \equiv S A S A \notin \mathrm{SN}$ (with $\llbracket R(S) \rrbracket_{\mathrm{HN}} = \infty_{\mathrm{HN}}$), whereas $R(T) \equiv T A S A \in \mathrm{SN}$ (normalizing across a $6$-term multiway graph in $4$ steps to $S A (S A (T A)) \in \mathcal{N}$). Define $C^0(M) \equiv M$ and $C^{k+1}(M) \equiv S\,R(T)\,C^k(M)$, and set 
$$
F_{2k} \;\equiv\; C^k(S),
  \qquad
  F_{2k+1} \;\equiv\; C^k\bigl(S\,R(S)\,S\bigr)
  \qquad (k \in \mathbb{N}). \tag{6.16}
$$
 Then for every $m \in \mathbb{N}$, $F_{m+1}$ is obtained from $F_m$ by replacing a single leaf occurrence of $S$ by a composite closed $S$-term ($S \mapsto S\,R(S)\,S$ for $F_{2k} \mapsto F_{2k+1}$, and the head leaf $S \mapsto T$ inside $R(S)$ for $F_{2k+1} \mapsto F_{2k+2}$), with $F_{2k} \in \mathrm{SN}$ and $F_{2k+1} \notin \mathrm{SN}$ for all $k \in \mathbb{N}$.
- (ii) *One-leaf rescue classification:* Across all $940$ one-hole context functions $f_C : Q_{\mathrm{SN}} \to Q_{\mathrm{SN}}$ generated by one-hole closed contexts $C[\square]$, if $C[S] \notin \mathrm{SN}$ and $C[P] \in \mathrm{SN}$ for a closed $S$-term $P \in \mathcal{T}_S$, then $\llbracket P \rrbracket_{\mathrm{SN}} \in \{q_1, q_8\}$, which forces $P \equiv S S$ ($2$ leaves) or $P \equiv S(S S S)$ ($4$ leaves) syntactically. Both plugs are realized: $C_1[\square] \equiv \square A S A$ satisfies $C_1[S] \notin \mathrm{SN}$ and $C_1[S S] \in \mathrm{SN}$, while $C_2[\square] \equiv \square (S S) S S S S$ satisfies $C_2[S] \notin \mathrm{SN}$ and $C_2[S(S S S)] \in \mathrm{SN}$.

*Proof.* 
For (i), $R(S) \equiv S A S A \to_h A A (S A) \equiv S S S A (S A) \to_h S A (S A) (S A) \to_h A(S A)(S A (S A)) \to_h \cdots$ evaluates to $\llbracket R(S) \rrbracket_{\mathrm{HN}} = \infty_{\mathrm{HN}}$, so $R(S) \notin \mathrm{HN}$ and hence $R(S) \notin \mathrm{SN}$. Conversely, $R(T) \equiv S S A S A \to_S S S (A S) A \to_S S A (A S A) \to_S S A (T T A) \to_S S A (S A (T A)) \in \mathcal{N}$, so $R(T) \in \mathrm{SN}$ by Theorem 6.2. Because $S M N \in \mathrm{SN}$ holds if and only if both $M \in \mathrm{SN}$ and $N \in \mathrm{SN}$ on spine-$2$ terms by Lemma 6.1(i), induction on $k$ shows that $C^k(M) \in \mathrm{SN}$ holds if and only if $M \in \mathrm{SN}$. Since $S \in \mathrm{SN}$ and $S\,R(S)\,S \notin \mathrm{SN}$, we obtain $F_{2k} \in \mathrm{SN}$ and $F_{2k+1} \notin \mathrm{SN}$ for all $k \ge 0$, while $F_{2k+1} \equiv C^k(S\,R(S)\,S)$ refines the tail leaf $S$ of $F_{2k}$ and $F_{2k+2} \equiv C^k(S\,R(T)\,S) \equiv C^{k+1}(S)$ refines the head leaf $S$ of $R(S) \equiv S A S A$ by $T \equiv S S$.

For (ii), closing the identity map $\mathrm{id}_{Q_{\mathrm{SN}}} \in Q_{\mathrm{SN}}^{Q_{\mathrm{SN}}}$ under pointwise left multiplication $x \mapsto c \odot_{\mathrm{SN}} f(x)$ and right multiplication $x \mapsto f(x) \odot_{\mathrm{SN}} c$ for all $c \in Q_{\mathrm{SN}}$ terminates at $940$ context functions. Collecting $\{ x \in Q_{\mathrm{SN}} : \exists f,\, f(q_0) = \infty_{\mathrm{SN}} \textrm{ and } f(x) \neq \infty_{\mathrm{SN}} \}$ yields $\{q_1, q_8\}$. Every closed $P$ with $\llbracket P \rrbracket_{\mathrm{SN}} \in \{q_1, q_8\}$ lies in $\mathrm{SN}$; let $V \in \mathcal{N}$ be its normal form ($P \to_S^* V$). By inspection of $\odot_{\mathrm{SN}}$ on $\mathcal{N}$, the unique normal form in $q_1$ is $S S$ and the unique normal form in $q_8$ is $S(S S S)$. Neither $S S$ (size $2$) nor $S(S S S)$ (size $4$, since the sole reducible closed term of size at most $4$ is $S S S S \to_S S S (S S)$, which evaluates to $q_9 \notin \{q_1, q_8\}$) has any proper predecessor under $\to_S$ by Proposition 2.2(ii), forcing $P \equiv V \in \{S S, S(S S S)\}$. Direct evaluation on the unique minimal $6$-leaf rescuing context $C_2[\square] \equiv \square(S S)S S S S$ confirms $\llbracket C_2[S] \rrbracket_{\mathrm{SN}} = \llbracket S(S S)S S S S \rrbracket_{\mathrm{SN}} = \infty_{\mathrm{SN}}$ whereas $\llbracket C_2[S(S S S)] \rrbracket_{\mathrm{SN}} = q_{30} \neq \infty_{\mathrm{SN}}$, whence $C_2[S] \notin \mathrm{SN}$ and $C_2[S(S S S)] \in \mathrm{SN}$ (normalizing in $1{,}109$ leftmost-outermost steps) by Theorem 6.2.
 $\square$

In Question 31 [4, p. 93], Barendregt et al. ask whether finite $S$-terms having equal Böhm trees—or equal *clocked* Böhm trees, annotated with head-step counts—must be $S$-convertible. We resolve both versions in the negative via a $36$-state refinement of $\mathcal{A}_{\mathrm{HN}}$.

**Theorem 6.15 (Unfaithfulness of Böhm and clocked Böhm trees, Question 31 [4, p. 93]).** 
Define the $36$-state algebra $\mathcal{A}_{36} = (Q_{36}, q_0, \odot_{36})$ on $Q_{36} = \{q_0, \dots, q_{33}, q_{34}, q_{35}\}$ by splitting $\infty_{\mathrm{HN}}$ into $q_{34}$ and $q_{35}$:

$$
x \odot_{36} y \;=\;
\begin{cases}
x \odot_{\mathrm{HN}} \tilde{y} & \textrm{if } x \in \{q_0, \dots, q_{33}\} \textrm{ and } x \odot_{\mathrm{HN}} \tilde{y} \neq \infty_{\mathrm{HN}}, \\
q_{34} & \textrm{if } x \in \{q_0, \dots, q_{33}\} \textrm{ and } x \odot_{\mathrm{HN}} \tilde{y} = \infty_{\mathrm{HN}}, \\
q_{35} & \textrm{if } x \in \{q_{34}, q_{35}\} \textrm{ and } y = q_0, \\
q_{34} & \textrm{if } x \in \{q_{34}, q_{35}\} \textrm{ and } y \in \{q_1, \dots, q_{35}\},
\end{cases} \tag{6.17}
$$

where $\tilde{y} = y$ for $y \in \{q_0, \dots, q_{33}\}$ and $\tilde{y} = \infty_{\mathrm{HN}}$ for $y \in \{q_{34}, q_{35}\}$. Then:

- (i) $\mathcal{A}_{36}$ is a combinatory $S$-algebra satisfying (2.1) on all $36^3 = 46{,}656$ triples in $Q_{36}^3$.
- (ii) One has $\llbracket A A A \rrbracket_{36} = q_{34} \neq q_{35} = \llbracket A A A S \rrbracket_{36}$, whence $A A A \neq_S A A A S$. More generally, setting $N_0 \equiv A A A$ and $N_k \equiv (A A A)\,R_{k-1}$ for $k \ge 1$ ($R_0 \equiv S$, $R_{m+1} \equiv S R_m$), the closed $S$-terms $\{N_k\}_{k \in \mathbb{N}}$ are pairwise non-convertible ($N_{k_1} \neq_S N_{k_2}$ for $k_1 \neq k_2$), yet all share the identical Böhm tree $\bot$ and the identical clocked Böhm tree $\bot$.

*Proof.* 
For (i), let $\pi : Q_{36} \to Q_{\mathrm{HN}}$ collapse $\{q_{34}, q_{35}\}$ back to $\infty_{\mathrm{HN}}$; by (6.17), $\pi(x \odot_{36} y) = \pi(x) \odot_{\mathrm{HN}} \pi(y)$, so (2.1) holds whenever $\pi(((q_0 \odot_{36} x) \odot_{36} y) \odot_{36} z) \neq \infty_{\mathrm{HN}}$. When $\pi$ evaluates both sides to $\infty_{\mathrm{HN}}$, note that $(q_0 \odot_{36} x) \odot_{36} y \in \{q_0, \dots, q_{33}\}$ for all $x, y \in Q_{36}$, so by the second clause of (6.17) the left-hand side $((q_0 \odot_{36} x) \odot_{36} y) \odot_{36} z$ equals $q_{34}$. On the right-hand side $(x \odot_{36} z) \odot_{36} (y \odot_{36} z)$, because $q_0$ never lies in the image of $\odot_{\mathrm{HN}}$ (and hence never lies in the image of $\odot_{36}$), we have $y \odot_{36} z \neq q_0$, so by the second and fourth clauses of (6.17) the right-hand side also equals $q_{34}$. Thus (2.1) holds across $Q_{36}^3$.

For (ii), $\llbracket A \rrbracket_{36} = q_6$, $\llbracket A A \rrbracket_{36} = q_{22}$, and $\llbracket A A A \rrbracket_{36} = q_{22} \odot_{36} q_6 = q_{34}$ (since $q_{22} \odot_{\mathrm{HN}} q_6 = \infty_{\mathrm{HN}}$), whereas $\llbracket A A A S \rrbracket_{36} = q_{34} \odot_{36} q_0 = q_{35}$; conversion invariance of $\mathcal{A}_{36}$ yields $A A A \neq_S A A A S$ (and at minimal leaf sizes $8$ and $9$, $S A S A \neq_S S A S A S$, as well as at equal size $9$, $A A A \neq_S S A S A S$). For the infinite family $N_k$ ($k \ge 1$), $\llbracket A A A \rrbracket_{\mathrm{HN}} = \infty_{\mathrm{HN}}$ places each $N_k \equiv (A A A)\,R_{k-1}$ in $\mathrm{RNF}$ by Theorem 6.6(ii) with $R_{k-1} \in \mathcal{N}$, so every reduct of $N_k$ has the form $P'\,R_{k-1}$ of constant right-spine depth $\operatorname{rs}(P'\,R_{k-1}) = 1 + \operatorname{rs}(R_{k-1}) = k$, whereas every reduct of $N_0 \equiv A A A$ has $\operatorname{rs} \ge \operatorname{rs}(A A A) = 2$ (and right child outside $\mathcal{N}$ once contracted, separating $N_0$ from $N_2$ as well). By Proposition 2.2(i), $N_{k_1}$ and $N_{k_2}$ share no common reduct for $k_1 \neq k_2$. Because $\llbracket N_k \rrbracket_{\mathrm{HN}} = \infty_{\mathrm{HN}}$ for all $k \ge 0$, every $N_k$ diverges at head clock $\infty$ without emitting a root label, giving identical Böhm and clocked Böhm trees $\bot$, whereas their Berarducci trees $\operatorname{BeT}(N_k) = \operatorname{BeT}(A A A)\,R_{k-1}$ remain pairwise distinct.
 $\square$

**Proposition 6.16 (Gross–Knuth cofinality, decidable reachability, and closed-$\mathrm{SN}$ convertibility).** 
Let $\mathrm{gk} : \mathcal{T}_S(\mathcal{V}) \to \mathcal{T}_S(\mathcal{V})$ denote Takahashi's complete parallel development [58] (the Gross–Knuth step $\Delta$ of Proposition 2.2(i) contracting all existing redexes simultaneously).

- (i) *Cofinality of $\mathrm{gk}$:* For all $M, N \in \mathcal{T}_S(\mathcal{V})$, $M =_S N$ holds if and only if there exists $m \in \mathbb{N}$ such that $N \to_S^* \mathrm{gk}^m(M)$.
- (ii) *Decidability of multiway reachability $\to_S^*$:* By Proposition 2.3(i), the relation $M \to_S^* N$ is constructively decidable for all $M, N \in \mathcal{T}_S(\mathcal{V})$.
- (iii) *RNF conversion decomposition and decidability of $=_S$ on closed $\mathrm{SN}$:* For any two applicative root normal forms $A_1 B_1, A_2 B_2 \in \mathrm{RNF}$, one has $A_1 B_1 =_S A_2 B_2$ if and only if both $A_1 =_S A_2$ and $B_1 =_S B_2$. On closed $S$-terms, whenever $V \in \mathrm{SN}$, the convertibility relation $M =_S V$ is decidable in finite time; by contrast, right-cancellation fails even on closed normal forms, witnessed by $N_1 \equiv S(S A S)S \neq_S S A (S A S) \equiv N_2$ ($N_1, N_2 \in \mathcal{N}$) with $N_1 S =_S N_2 S$, and universally by Waldmann's pair $U_1 \equiv S(S T S)A \neq_S S(T A)(S A S) \equiv U_2$ satisfying $U_1 Z =_S U_2 Z$ for every $Z \in \mathcal{T}_S(\mathcal{V})$.

*Proof.* 
For (i), let $\Rightarrow$ denote one-step parallel reduction as in Proposition 2.2(i), which satisfies Takahashi's triangle property that $M \Rightarrow N$ implies $N \Rightarrow \mathrm{gk}(M)$ [58]. Iterating the triangle property shows that $M \Rightarrow^m K$ implies $K \Rightarrow^m \mathrm{gk}^m(M)$. Thus if $M =_S N$, Church–Rosser yields a common reduct $K$ with $M \Rightarrow^m K$ and $N \to_S^* K$, whence $N \to_S^* K \to_S^* \mathrm{gk}^m(M)$; the converse is immediate since $M \to_S^* \mathrm{gk}^m(M)$.

Part (ii) was proved via Bergstra's weight $\|M\|_{\mathrm{B}}$ in Proposition 2.3(i). For (iii), if $A_1 B_1 =_S A_2 B_2$ with $A_1 B_1, A_2 B_2 \in \mathrm{RNF}$, Church–Rosser gives a common reduct $K$ with $A_1 B_1 \to_S^* K$ and $A_2 B_2 \to_S^* K$; since neither reduction can contract at the root, $K \equiv K_1 K_2$ with $A_i \to_S^* K_1$ and $B_i \to_S^* K_2$, giving $A_1 =_S A_2$ and $B_1 =_S B_2$. Given closed $M, V \in \mathcal{T}_S$ with $V \in \mathrm{SN}$, conversion invariance of $\mathcal{A}_{\mathrm{SN}}$ and uniqueness of normal forms show that $M =_S V$ holds if and only if $\llbracket M \rrbracket_{\mathrm{SN}} \neq \infty_{\mathrm{SN}}$ and $\mathrm{norm}(M) \equiv \mathrm{norm}(V)$, which is decidable by Theorem 6.2. Finally, $N_1 \not\equiv N_2$ and $U_1 \not\equiv U_2$ are distinct closed normal forms (hence non-convertible by confluence), yet $\mathrm{gk}^6(N_1 S) \equiv \mathrm{gk}^6(N_2 S) \equiv S D (T D)$ with $D \equiv (S T)(T T)$, while $U_1 Z \to_S^5 \bigl(P_Z\,(P_Z P_Z)\bigr)\bigl(Z P_Z\,(P_Z P_Z)\bigr) \leftarrow_S^6 U_2 Z$ (with $P_Z \equiv S Z$) joins for every open or closed $Z$.
 $\square$

## 7. Fixed-Order Dynamics, Super-Pushdown Traces, and Clone-Theoretic Cellular Barriers

Fixed deterministic reduction strategies—leftmost-outermost ($\to_{\mathrm{lo}}$), rightmost-outermost ($\to_{\mathrm{ro}}$), leftmost-innermost ($\to_{\mathrm{li}}$), rightmost-innermost ($\to_{\mathrm{ri}}$), shallowest-leftmost breadth-first ($\to_{\mathrm{bfs}}$), and Gross–Knuth parallel reduction ($\to_{\mathrm{gk}}$)—govern step-by-step evaluation in $\mathrm{CL}(S)$, while clone-theoretic monotonicity separates the semantic $S$-algebras $\mathcal{A}_{\mathrm{HN}}$, $\mathcal{A}_{\mathrm{SN}}$, and $\mathcal{A}_P$ from normal-form cellular computation.

### 7.1. Pure-Line Strategy Coincidence, Quadratic Automaton Traces, and Innermost $A A A$

Let $\#\mathrm{Redex}(M) \in \mathbb{N}$ denote the number of redex occurrences $S X Y Z$ in $M$, and let $\mathcal{N}_2 = \{ S X Y : X, Y \in \mathcal{N} \} \subset \mathcal{N}$ denote the set of Spine-$2$ closed normal forms. Following [4], a term $M$ is *pure-line* along a trajectory if every visited reduct satisfies $\#\mathrm{Redex}(M_t) = 1$.

**Proposition 7.1 (Pure-line six-strategy coincidence, quadratic traces, and innermost $A A A$).**

- (i) *(Six-strategy coincidence on single-redex terms)* For every $M \in \mathcal{T}_S(\mathcal{V})$ satisfying $\#\mathrm{Redex}(M) = 1$, all six deterministic evaluators $\to_{\mathrm{lo}}, \to_{\mathrm{ro}}, \to_{\mathrm{li}}, \to_{\mathrm{ri}}, \to_{\mathrm{bfs}}, \to_{\mathrm{gk}}$ select the unique redex of $M$ and yield the identical one-step reduct $M'$.
- (ii) *(Super-pushdown quadratic milestone language on $Z_{\mathrm{Zac}}$)* Along the reduction sequence $Z_{\mathrm{Zac}} = T_0 \to T_1 \to T_2 \to \cdots$ starting from Zachos's $10$-leaf combinator $Z_{\mathrm{Zac}} \equiv G_0 G_0 \equiv (S T T)(S T T)$, every reduct $T_t$ satisfies $\#\mathrm{Redex}(T_t) = 1$ (so all six strategies generate the identical infinite sequence $(T_t)_{t \ge 0}$). Moreover, there is an explicit $8$-state deterministic bottom-up tree automaton $\mathcal{B}_Z = (\{b_0, \dots, b_7\}, b_0, \odot_{\mathcal{B}_Z}, \{b_6\})$ such that for all $t \in \mathbb{N}$, 
$$
\llbracket T_t \rrbracket_{\mathcal{B}_Z} = b_6
\;\Longleftrightarrow\;
t \in \Bigl\{ \frac{n(n+3)}{2} : n \in \mathbb{N} \Bigr\}
\;=\; \{0, 2, 5, 9, 14, 20, 27, \dots\} \tag{7.1}
$$
 (shifted by $+1$ to the triangular numbers $\binom{n+2}{2} = \{1, 3, 6, 10, 15, \dots\}$ when starting from the $9$-leaf precursor $Z_0 \equiv S(S T)(S T)T$, while on $D_{\mathrm{seed}} \equiv Z_0 S$ an explicit $68$-state automaton $\mathcal{B}_{\mathrm{quad}}$ recognizes $\{2n^2 + 3n + 1 : n \in \mathbb{N}\}$ under $\to_{\mathrm{lo}}$). By Parikh's theorem [46], the unary trace language $\{ 1^t : \llbracket T_t \rrbracket_{\mathcal{B}_Z} = b_6 \}$ is not context-free and cannot be generated by any pushdown or one-counter machine.
- (iii) *(Closed-form exponential size growth of $A A A$ under $\to_{\mathrm{li}}$, versus $\to_{\mathrm{ro}}$ trapping)* Under rightmost-outermost reduction $\to_{\mathrm{ro}}$, any non-root-redex application $L R$ with $R \in \mathcal{T}_S \setminus \mathrm{SN}$ traps forever on the right: $(L R)_t \equiv L\,R_t$ for all $t \ge 0$. Under leftmost-innermost reduction $\to_{\mathrm{li}}$, every non-normalizing closed term reduces once its minimal leftmost-innermost $\infty_{\mathrm{SN}}$-subterm freezes its outer context to iterating the normal-form map $F_{\mathrm{li}} : \mathcal{N}_2 \times \mathcal{N} \to \mathcal{N}_2 \times \mathcal{N}$ on critical pairs $(L, Z)$ ($\llbracket L Z \rrbracket_{\mathrm{SN}} = \infty_{\mathrm{SN}}$). For $A A A \equiv (S S S)(S S S)(S S S)$, setting $M_1 \equiv S A A$, $H_0 \equiv S A M_1$, and $H_{n+1} \equiv S H_n (S H_n) \in \mathcal{N}_2$ ($n \ge 0$), a $4$-macro-step transient from $(S A (S A), A)$ reaches $(H_1, H_1)$, after which every cycle $n \ge 1$ executes the $(n+2)$-macro-step loop $(H_n, H_n) \mapsto^n (H_0, H_n) \mapsto (M_1, H_n) \mapsto (H_{n+1}, H_{n+1})$ with exact exponential leaf count $|H_n| = 13 \cdot 2^n - 2$.

*Proof.* 
For (i), structural induction on $M$ shows that $\#\mathrm{Redex}(M) = 0$ if and only if $M \in \mathrm{NF}$, on which every strategy is idle ($\mathrm{gk}(M) = M$). When $\#\mathrm{Redex}(M) = 1$, either $M \equiv S X Y Z$ is itself a root redex with $X, Y, Z \in \mathrm{NF}$—where $\to_{\mathrm{lo}}, \to_{\mathrm{ro}}, \to_{\mathrm{bfs}}$ contract the root directly, $\to_{\mathrm{li}}, \to_{\mathrm{ri}}$ find $S X Y, Z \in \mathrm{NF}$ and contract the root, and $\mathrm{gk}(S X Y Z) = (\mathrm{gk}(X)\,\mathrm{gk}(Z))(\mathrm{gk}(Y)\,\mathrm{gk}(Z)) = (X Z)(Y Z)$—or $M \equiv L R$ is not a root redex and $(\#\mathrm{Redex}(L), \#\mathrm{Redex}(R)) \in \{(1, 0), (0, 1)\}$, where the idle child contains no redexes and the induction hypothesis equates all six evaluators on the active child.

For (ii), recall $G_0 \equiv S T T$ and $G_{k+1} \equiv T G_k$, which contain no redexes ($\#\mathrm{Redex}(G_k) = 0$), whereas $\#\mathrm{Redex}(G_k G_m) = 1$ for all $k, m \in \mathbb{N}$ (at the root $S T T G_m$ when $k = 0$, and at $S S G_{k-1} G_m$ when $k \ge 1$). For any sequence of indices $\vec{m} = (m_1, \dots, m_r)$, define the normal-form wrapper $W_{\vec{m}}(C) \equiv S G_{m_1} (S G_{m_2} (\cdots (S G_{m_r} C)\cdots))$; since $\#\mathrm{Redex}(S G_m) = 0$ and $\mathrm{ls}(S G_m C) = 2$, we have $\#\mathrm{Redex}(W_{\vec{m}}(C)) = \#\mathrm{Redex}(C)$. Starting at $W_{\vec{m}}(G_0 G_n)$, one contraction yields $W_{\vec{m}}(G_{n+1} G_{n+1})$, and $n + 1$ subsequent contractions $G_{k+1} G_{n+1} \equiv S S G_k G_{n+1} \to_S S G_{n+1} (G_k G_{n+1})$ ($k = n, \dots, 0$) yield $W_{\vec{m} \cdot (n+1)^{n+1}}(G_0 G_{n+1})$ in $(n + 2)$ steps total. Summing $\sum_{j=0}^{n-1} (j + 2) = \frac{1}{2}n(n+3)$ from $T_0 \equiv G_0 G_0$ ($n = 0$, empty $\vec{m}$) shows $\#\mathrm{Redex}(T_t) = 1$ for all $t \ge 0$, with $T_{n(n+3)/2} \equiv W_{\vec{\mu}_n}(G_0 G_n)$ and intermediate steps $T_{n(n+3)/2 + j} \equiv W_{\vec{\mu}'}(G_{n+2-j} G_{n+1})$ ($1 \le j \le n + 1$). Define $\odot_{\mathcal{B}_Z}$ on $\{b_0, \dots, b_7\}$ by $b_0 \odot b_0 = b_1$ ($T$), $b_0 \odot b_1 = b_2$ ($S T$), $b_2 \odot b_1 = b_3$ ($G_0$), $b_1 \odot b_3 = b_1 \odot b_4 = b_4$ ($G_{k+1}$ for $k \ge 0$), $b_0 \odot b_3 = b_0 \odot b_4 = b_5$ ($S G_m$), $b_3 \odot b_3 = b_3 \odot b_4 = b_6$ ($G_0 G_n$), $b_5 \odot b_6 = b_6$ (preserving $b_6$ across $W_{\vec{m}}$), and $b_7$ elsewhere (so $G_{k+1} G_m \mapsto b_4 \odot b_{3,4} = b_7$ and $b_5 \odot b_7 = b_7$). Then $\llbracket T_t \rrbracket_{\mathcal{B}_Z} = b_6$ holds if and only if the core is $G_0 G_n$, proving (7.1). Because consecutive gaps $\frac{1}{2}(n+1)(n+4) - \frac{1}{2}n(n+3) = n + 2 \to \infty$ are unbounded while the set is infinite, $\{ \frac{1}{2}n(n+3) : n \in \mathbb{N} \}$ is not a finite union of arithmetic progressions (not semilinear); by Parikh's theorem [46], $\{ 1^t : \llbracket T_t \rrbracket_{\mathcal{B}_Z} = b_6 \}$ is not context-free.

For (iii), if $L R$ is not a root redex and $R \in \mathcal{T}_S \setminus \mathrm{SN}$, Theorem 6.2 ensures $R$ is not in normal form, so $\to_{\mathrm{ro}}$ steps inside $R \to_{\mathrm{ro}} R'$ while preserving non-root-redex shape and $\llbracket R' \rrbracket_{\mathrm{SN}} = \infty_{\mathrm{SN}}$ inductively. Under $\to_{\mathrm{li}}$, $A A A \equiv ((S S S) A) A \to_{\mathrm{li}} (S A (S A)) A$ reaches the critical pair $(L_0, Z_0) = (S A (S A), A)$ with $\llbracket L_0 \rrbracket_{\mathrm{SN}} = q_{29}$, $\llbracket A \rrbracket_{\mathrm{SN}} = q_7$, and $q_{29} \odot_{\mathrm{SN}} q_7 = \infty_{\mathrm{SN}}$. Since $A U \equiv S S S U \to_{\mathrm{li}} S U (S U) \in \mathcal{N}_2$ for every $U \in \mathcal{N}$, induction on $k \ge 0$ gives $\llbracket H_0 \rrbracket_{\mathrm{SN}} = q_{29}$ and $\llbracket H_{k+1} \rrbracket_{\mathrm{SN}} = q_{30}$ (from $\llbracket M_1 \rrbracket_{\mathrm{SN}} = q_{34}$, $\llbracket H_0 \rrbracket_{\mathrm{SN}} = (q_0 \odot_{\mathrm{SN}} q_7) \odot_{\mathrm{SN}} q_{34} = q_{29}$, and $q_0 \odot_{\mathrm{SN}} q_{29} = q_0 \odot_{\mathrm{SN}} q_{30} = q_6$ with $q_6 \odot_{\mathrm{SN}} q_6 = q_{30}$), while $\{q_{29}, q_{30}\} \odot_{\mathrm{SN}} \{q_{29}, q_{30}\} = \{\infty_{\mathrm{SN}}\}$ and $q_{34} \odot_{\mathrm{SN}} \{q_{29}, q_{30}\} = \{\infty_{\mathrm{SN}}\}$. After $(S A (S A), A) \mapsto (S A (S A), M_1) \mapsto (S M_1 (S M_1), H_0) \mapsto (M_1, H_0) \mapsto (H_1, H_1)$, each $(H_k, H_n)$ with $k, n \ge 1$ has left contraction child $H_{k-1} H_n$ of state $\llbracket H_{k-1} \rrbracket_{\mathrm{SN}} \odot_{\mathrm{SN}} q_{30} = \infty_{\mathrm{SN}}$ (Case 1, peeling $H_k \mapsto H_{k-1}$ in $n$ steps to $(H_0, H_n)$); at $(H_0, H_n) = (S A M_1, H_n)$, the left contraction child satisfies $A H_n \to_{\mathrm{li}} H_{n+1} \in \mathcal{N} \subseteq \mathrm{SN}$ while $M_1 H_n$ has state $q_{34} \odot_{\mathrm{SN}} q_{30} = \infty_{\mathrm{SN}}$ (Case 2, advancing to $(M_1, H_n) = (S A A, H_n)$); and at $(S A A, H_n)$, both $A H_n$ children normalize in one step to $H_{n+1}$, yielding $(H_{n+1}, H_{n+1})$ (Case 3). Finally, $|H_0| = 1 + 3 + (1 + 3 + 3) = 11$ and $|H_{n+1}| = 2|H_n| + 2$, solving to $|H_n| = 13 \cdot 2^n - 2$.
 $\square$

### 7.2. The Sharp Five-Step Innermost Case-3 Ceiling

Along any innermost reduction ($\to_{\mathrm{li}}$ or $\to_{\mathrm{ri}}$) of a non-normalizing closed $S$-term, each macro-step on the active critical pair $(L, Z) \in \mathcal{N}_2 \times \mathcal{N}$ ($L \equiv S X Y$, $\llbracket L Z \rrbracket_{\mathrm{SN}} = \infty_{\mathrm{SN}}$) falls into Case 1 ($\llbracket X Z \rrbracket_{\mathrm{SN}} = \infty_{\mathrm{SN}}$, descending to $(X, Z)$), Case 2 ($\llbracket X Z \rrbracket_{\mathrm{SN}} \neq \infty_{\mathrm{SN}}$ and $\llbracket Y Z \rrbracket_{\mathrm{SN}} = \infty_{\mathrm{SN}}$, descending to $(Y, Z)$ under $\to_{\mathrm{li}}$), or *Case 3*, in which both $X Z$ and $Y Z$ are strongly normalizing—normalizing to $L' = \mathrm{nf}(X Z) \in \mathcal{N}_2$ and $Z' = \mathrm{nf}(Y Z) \in \mathcal{N}$—while $\llbracket L' Z' \rrbracket_{\mathrm{SN}} = \infty_{\mathrm{SN}}$. By global top-termination (Theorem 6.7), Case 3 cannot occur infinitely many times consecutively, because consecutive Case 3 steps contract repeatedly at the root of the fixed minimal non-$\mathrm{SN}$ locus without descending into a proper subterm. Although the abstract Case-3 transition graph over state pairs $(u, v) \in F_{\mathrm{SN}}^2$ contains directed cycles—such as $(q_{25}, q_{25}) \to (q_{25}, q_{30}) \to (q_{30}, q_{30}) \to (q_{30}, q_6) \to (q_{29}, q_{25}) \to (q_{25}, q_{25})$—refining $L$ by a two-level normal-form descriptor yields a universal uniform bound of $5$ consecutive Case-3 steps across all of $\mathrm{CL}(S)$, dropping to $3$ asymptotically.

**Theorem 7.2 (Sharp consecutive Case-3 ceiling under $\to_{\mathrm{li}}$ and $\to_{\mathrm{ri}}$).** 
Under both leftmost-innermost ($\to_{\mathrm{li}}$) and rightmost-innermost ($\to_{\mathrm{ri}}$) evaluation:

- (i) *(Universal five-step ceiling)* No closed $S$-term admits $6$ consecutive Case-3 macro-steps: there exists no chain $(L_0, Z_0) \mapsto_{\mathrm{C3}} (L_1, Z_1) \mapsto_{\mathrm{C3}} \dots \mapsto_{\mathrm{C3}} (L_6, Z_6)$.
- (ii) *(Sharpness at five steps)* Five consecutive Case-3 macro-steps are achieved by the $9$-leaf witness $S(S(S A)) S S$ ($A \equiv S S S$), starting from $L_0 \equiv S(S(S A)) S$ and $Z_0 \equiv S$.
- (iii) *(Monotonicity of right-spine depth and asymptotic ceiling $3$)* Every Case-3 step $(L, Z) \mapsto_{\mathrm{C3}} (L', Z')$ satisfies $\mathrm{rs}(Z') \ge \mathrm{rs}(Z) + 1$ and $\mathrm{rs}(L') \ge \mathrm{rs}(Z) + 1$. Once $\mathrm{rs}(Z) \ge 2$ (which holds after at most two Case-3 steps along any trajectory), at most $3$ consecutive Case-3 macro-steps can occur.

*Proof.* 
Because $\mathrm{CL}(S)$ is confluent and $X Z, Y Z \in \mathrm{SN}$ in Case 3 have unique normal forms $L' = \mathrm{nf}(X Z)$ and $Z' = \mathrm{nf}(Y Z)$ independent of whether $X Z$ and $Y Z$ are normalized via $\to_{\mathrm{li}}$ or $\to_{\mathrm{ri}}$, the Case-3 relation $(L, Z) \mapsto_{\mathrm{C3}} (L', Z')$ is identical for $\to_{\mathrm{li}}$ and $\to_{\mathrm{ri}}$.

For (i), to eliminate the spurious state-graph cycles in $F_{\mathrm{SN}}^2$, define a $5$-valued child tag $\kappa : Q_{\mathrm{SN}} \to \{0, 1, 2, 3, 4\}$ grouping normal-form states by structural spine capability, and assign to each $V \in \mathcal{N}$ its finite *normal-form descriptor*

$$
\delta(V) \;=\; \bigl(\mathrm{ls}(V),\; \llbracket V \rrbracket_{\mathrm{SN}},\; \kappa_1(V),\; \kappa_2(V)\bigr)
\;\in\; \{0, 1, 2\} \times F_{\mathrm{SN}} \times \{0, \dots, 4\}^2,
$$

where $(\kappa_1, \kappa_2) = (0, 0)$ for $V \equiv S$, $(\kappa(\llbracket U \rrbracket_{\mathrm{SN}}), 0)$ for $V \equiv S U$, and $(\kappa(\llbracket X \rrbracket_{\mathrm{SN}}), \kappa(\llbracket Y \rrbracket_{\mathrm{SN}}))$ for $V \equiv S X Y$. Only $96$ descriptors are inhabited across all $V \in \mathcal{N}$. Using abstract interpretation of $\mathrm{app}_{\mathcal{N}}(X, Z)$ over descriptors (defining a finite superset $\hat{\alpha}(\delta(X), z)$ of the descriptors reachable from $\delta(X)$ and $z = \llbracket Z \rrbracket_{\mathrm{SN}}$), we construct an integer rank $\rho_{\mathrm{c3}}(\delta(L), \llbracket Z \rrbracket_{\mathrm{SN}}) \in \{1, 2, 3, 4, 5\}$ verified across all $(x, y, z) \in F_{\mathrm{SN}}^3$ satisfying $((q_0 \odot x) \odot y) \odot z = \infty_{\mathrm{SN}}$, $x \odot z \neq \infty_{\mathrm{SN}}$, and $y \odot z \neq \infty_{\mathrm{SN}}$ to obey: (a) $1 \le \rho_{\mathrm{c3}}(\delta(S X Y), z) \le 5$; and (b) for every reachable Spine-$2$ descriptor $d' = (2, x', \kappa'_1, \kappa'_2) \in \hat{\alpha}(\delta(X), z)$ with $x' \odot_{\mathrm{SN}} (y \odot_{\mathrm{SN}} z) = \infty_{\mathrm{SN}}$, we have $\rho_{\mathrm{c3}}(d', y \odot_{\mathrm{SN}} z) < \rho_{\mathrm{c3}}(\delta(S X Y), z)$. Six consecutive Case-3 steps $(L_0, Z_0) \mapsto_{\mathrm{C3}} \dots \mapsto_{\mathrm{C3}} (L_6, Z_6)$ would therefore yield $5 \ge \rho_{\mathrm{c3}}(\delta(L_0), \llbracket Z_0 \rrbracket_{\mathrm{SN}}) > \dots > \rho_{\mathrm{c3}}(\delta(L_5), \llbracket Z_5 \rrbracket_{\mathrm{SN}}) \ge 1$, requiring $6$ strictly decreasing integers in $\{1, 2, 3, 4, 5\}$, a contradiction.

For (ii), letting $B \equiv S T \equiv S(S S)$, direct normalization verifies the $5$-step Case-3 chain:

$$
\begin{aligned}
(L_0, Z_0) &\;=\; \bigl(S(S(S A)) S,\; S\bigr)
\;\mapsto_{\mathrm{C3}}\; \bigl(S(S A) S,\; T\bigr)
\;\mapsto_{\mathrm{C3}}\; \bigl(S A T,\; B\bigr) \\
&\;\mapsto_{\mathrm{C3}}\; \bigl(S B (S B),\; S S B\bigr)
\;\mapsto_{\mathrm{C3}}\; \bigl(S T (S S B),\; S B (S S B)\bigr) \\
&\;\mapsto_{\mathrm{C3}}\; \bigl(S S Z_4,\; S Z_4 (S T Z_4)\bigr)
\qquad \bigl(Z_4 \equiv S B (S S B)\bigr),
\end{aligned}
$$

where every pair $(L_i, Z_i)$ ($0 \le i \le 5$) satisfies $L_i \in \mathcal{N}_2$, $Z_i \in \mathcal{N}$, and $\llbracket L_i Z_i \rrbracket_{\mathrm{SN}} = \infty_{\mathrm{SN}}$.

For (iii), since $\mathrm{rs}(M) \le \mathrm{rs}(M')$ holds for every multiway step $M \to_S M'$ (non-root steps preserve or increase $\mathrm{rs}$, and root steps add $+1$), normalizing $X Z \to_S^* L'$ and $Y Z \to_S^* Z'$ gives $\mathrm{rs}(L') \ge \mathrm{rs}(X Z) = 1 + \mathrm{rs}(Z)$ and $\mathrm{rs}(Z') \ge \mathrm{rs}(Y Z) = 1 + \mathrm{rs}(Z)$. Restricting $z = \llbracket Z \rrbracket_{\mathrm{SN}}$ to states inhabited by normal forms with $\mathrm{rs}(Z) \ge 2$ (which excludes $q_0 = \llbracket S \rrbracket$ and all states $\llbracket U S \rrbracket$ of $\mathrm{rs} = 1$) bounds $\rho_{\mathrm{c3}}(\delta(L), z) \le 3$, limiting any run of Case-3 steps from that point onward to at most $3$.
 $\square$

### 7.3. Post's Lattice Monotonicity versus Minimal Normal-Form Rule 110

We next examine whether a fixed open $S$-polynomial $P(x_1, \dots, x_k)$ built from $S$ and variables $x_1, \dots, x_k$ can evaluate Boolean logic or evolve a universal one-dimensional cellular automaton such as Cook's universal, $\mathrm{P}$-complete elementary cellular automaton Rule 110 [17, 45, 67] over two distinguished closed equivalence classes of $\mathrm{CL}(S)$. Using Post's functional completeness theorem and lattice of Boolean clones [48], we establish a sharp algebraic dichotomy: inside the semantic $S$-algebras $\mathcal{A}_{\mathrm{HN}}$, $\mathcal{A}_{\mathrm{SN}}$, and $\mathcal{A}_P$, compatible partial orders confine all induced Boolean operations to Post's monotone clone $M$, forbidding negation and Rule 110; yet over a dedicated $4$-state conversion-invariant $S$-algebra $\mathcal{D}_4$ (Table 5), non-monotonicity emerges cleanly and yields a globally minimal $11$-leaf normal-form Rule 110 combinator.

**Table 5.** Multiplication table of the $4$-state functionally complete $S$-algebra $\mathcal{D}_4 = (\{d_0, d_1, d_2, d_3\}, d_0, \odot_{\mathcal{D}_4})$ and minimal normal-form ground representatives.

| $\odot_{\mathcal{D}_4}$ | $d_0$ | $d_1$ | $d_2$ | $d_3$ | Minimal Representative | Boolean / Algebraic Role |
| :—: | :—: | :—: | :—: | :—: | :— | :— |
| $d_0$ | $d_1$ | $d_1$ | $d_1$ | $d_2$ | $S$ ($1$ leaf, $\mathcal{N}$) | Generator $d_0 = \llbracket S \rrbracket_{\mathcal{D}_4}$ |
| $d_1$ | $d_3$ | $d_3$ | $d_3$ | $d_3$ | $S S$ ($2$ leaves, Spine-$1$ $\mathcal{N}$) | Encoded Boolean $\mathsf{false}$ ($0$) |
| $d_2$ | $d_1$ | $d_1$ | $d_3$ | $d_3$ | $S(S S S)$ ($4$ leaves, Spine-$1$ $\mathcal{N}$) | Encoded Boolean $\mathsf{true}$ ($1$) |
| $d_3$ | $d_3$ | $d_3$ | $d_3$ | $d_3$ | $S S S$ ($3$ leaves, Spine-$2$ $\mathcal{N}$) | Auxiliary absorbing mediator |

**Theorem 7.3 (Post's lattice monotonicity barrier and minimal $11$-leaf normal-form Rule 110).**

- (i) *(Monotone-clone barrier in $\mathcal{A}_{\mathrm{HN}}, \mathcal{A}_{\mathrm{SN}}, \mathcal{A}_P$)* Each of $\mathcal{A}_{\mathrm{HN}}$, $\mathcal{A}_{\mathrm{SN}}$, and $\mathcal{A}_P$ admits non-trivial compatible preorders $\sqsubseteq$ satisfying $x_1 \odot y_1 \sqsubseteq x_2 \odot y_2$ whenever $x_1 \sqsubseteq x_2$ and $y_1 \sqsubseteq y_2$ ($6$ non-trivial compatible preorders on $\mathcal{A}_{\mathrm{HN}}$, and $5$ each on $\mathcal{A}_{\mathrm{SN}}$ and $\mathcal{A}_P$). Across every pair of distinct states $(e_0, e_1)$ in $\mathcal{A}_{\mathrm{HN}}$, $\mathcal{A}_{\mathrm{SN}}$, or $\mathcal{A}_P$, every open $S$-polynomial $P(x_1, \dots, x_k)$ mapping $\{e_0, e_1\}^k$ into $\{e_0, e_1\}$ computes a monotone Boolean function belonging to Post's clone $M$ [48]; in particular, none of $\mathrm{NOT}$, $\mathrm{NAND}$, $\mathrm{XOR}$, or Rule 110 is polynomial-definable over any $2$-state encoding in $\mathcal{A}_{\mathrm{HN}}$, $\mathcal{A}_{\mathrm{SN}}$, or $\mathcal{A}_P$.
- (ii) *(Functional completeness of $\mathcal{D}_4$ and minimal $11$-leaf normal-form Rule 110)* The $4$-state structure $\mathcal{D}_4$ of Table 5 is a conversion-invariant $S$-algebra satisfying (2.1) on all $64$ triples, breaking monotonicity via $d_0 \odot_{\mathcal{D}_4} d_3 = d_2 \neq d_1 = d_0 \odot_{\mathcal{D}_4} d_1$. Encoding $\mathsf{false}$ by $F_{\flat} \equiv S S$ ($\llbracket F_{\flat} \rrbracket_{\mathcal{D}_4} = d_1$) and $\mathsf{true}$ by $T_{\sharp} \equiv S(S S S)$ ($\llbracket T_{\sharp} \rrbracket_{\mathcal{D}_4} = d_2$), the $4$-leaf polynomial $\mathrm{NAND}(x, y) \equiv S(x(y S))$ realizes Boolean $\mathrm{NAND}$ on $\{d_1, d_2\}$, and the $11$-leaf polynomial 
$$
R_{110}(x, y, z) \;\equiv\; S\Bigl(S(y\,x)\Bigl(S(y\,z)\bigl(S(z\,y)\,S\bigr)\Bigr)\Bigr) \tag{7.2}
$$
 evaluates elementary cellular automaton Rule 110 ($b'_i = (b_y + b_z + b_y b_z + b_x b_y b_z) \bmod 2$, truth vector $01101110_2$ on $111 \dots 000$) over $\{d_1, d_2\}$. Furthermore: - (a) Whenever $x, y, z \in \mathcal{T}_S$ are Spine-$1$ normal forms ($S W$ with $W \in \mathcal{N}$, including $F_{\flat}$ and $T_{\sharp}$), $R_{110}(x, y, z)$ is already a Spine-$1$ normal form ($0$ reduction steps), so synchronous iteration of $R_{110}$ evolves arbitrary Rule 110 configurations entirely within Spine-$1$ normal forms.
- (b) No open $\{S, x, y, z\}$-polynomial with fewer than $11$ leaves realizes Rule 110 on $\{d_1, d_2\}$ in $\mathcal{D}_4$, and no curried closed combinator $G \in \mathcal{T}_S$ can satisfy $\llbracket G x y z \rrbracket_{\mathcal{D}_4} = \llbracket R_{110}(x, y, z) \rrbracket_{\mathcal{D}_4}$ (nor reduce $G x y z \to_S^* S W$).

*Proof.* 
For (i), if $\sqsubseteq$ is a compatible preorder on $(Q, q_0, \odot)$, structural induction on any open polynomial $P(x_1, \dots, x_k)$ built from constants in $Q$ and variables shows that $\vec{u} \sqsubseteq \vec{v}$ componentwise implies $P(\vec{u}) \sqsubseteq P(\vec{v})$. Whenever $e_0 \sqsubset e_1$ (meaning $e_0 \sqsubseteq e_1$ and $e_1 \not\sqsubseteq e_0$), any induced Boolean operation $f : \{0, 1\}^k \to \{0, 1\}$ with $P(e_{b_1}, \dots, e_{b_k}) = e_{f(b_1, \dots, b_k)}$ must satisfy $f(\vec{b}) \le f(\vec{b}')$ whenever $\vec{b} \le \vec{b}'$, placing $f$ inside Post's monotone clone $M \subsetneq \mathrm{Pol}(\{0, 1\})$ [48]. On $\mathcal{A}_{\mathrm{HN}}$, for example, ordering $q \sqsubseteq \infty_{\mathrm{HN}}$ for all $q$ (and refining along the $6$ compatible preorders of $\mathcal{A}_{\mathrm{HN}}$ and $5$ of $\mathcal{A}_{\mathrm{SN}}, \mathcal{A}_P$), together with complete finite closure of unary and binary operations on every incomparable pair $(e_0, e_1)$, confirms that every unary polynomial in $\mathcal{A}_{\mathrm{HN}}, \mathcal{A}_{\mathrm{SN}}, \mathcal{A}_P$ is aperiodic ($f(e_0) = e_1$ and $f(e_1) = e_0$ never hold simultaneously), ruling out $\mathrm{NOT}$ ($\neg x$), $\mathrm{NAND}$ ($\mathrm{NAND}(x, x) = \neg x$), $\mathrm{XOR}$ ($\mathrm{XOR}(x, 1) = \neg x$), and Rule 110 ($R_{110}(1, x, 1) = \neg x$).

For (ii), we verify (2.1) on $\mathcal{D}_4$ in four lines: for all $x, y, z \in Q_{\mathcal{D}_4}$, $d_0 \odot x \in \{d_1, d_2\}$, whence $(d_0 \odot x) \odot y \in \{d_1, d_3\}$, and since rows $d_1$ and $d_3$ are identically $d_3$, the left-hand side $((d_0 \odot x) \odot y) \odot z$ equals $d_3$. On the right-hand side $(x \odot z) \odot (y \odot z)$, note $d_0 \notin \mathrm{im}(\odot)$, so $x \odot z \in \{d_1, d_2, d_3\}$; if $x \odot z \in \{d_1, d_3\}$ the product is $d_3$, while the sole entry giving $x \odot z = d_2$ is $(x, z) = (d_0, d_3)$, for which $y \odot d_3 \in \{d_2, d_3\}$ and $d_2 \odot \{d_2, d_3\} = \{d_3\}$. Thus both sides of (2.1) equal $d_3$ identically.

Evaluating $\mathrm{NAND}(x, y) \equiv S(x(y S))$ on $x, y \in \{d_1, d_2\}$: if $y = d_1$, then $y \odot d_0 = d_3$, $x \odot d_3 = d_3$, and $d_0 \odot d_3 = d_2$; if $y = d_2$, then $y \odot d_0 = d_1$, so $d_1 \odot d_1 = d_3 \mapsto d_2$ whereas $d_2 \odot d_1 = d_1 \mapsto d_0 \odot d_1 = d_1$, matching $\mathrm{NAND}$. Similarly, for $x, y, z \in \{d_1, d_2\}$, observe that $u \odot v = d_1$ if $(u, v) = (d_2, d_1)$ and $d_3$ otherwise on $\{d_1, d_2\}^2$. Direct substitution into (7.2) over the eight triples $(x, y, z) \in \{d_1, d_2\}^3$ ordered from $(d_1, d_1, d_1)$ ($000$) to $(d_2, d_2, d_2)$ ($111$) yields $(d_1, d_2, d_2, d_2, d_1, d_2, d_2, d_1)$, matching $0, 1, 1, 1, 0, 1, 1, 0$ (Rule 110). For (a), if $x \equiv S W_x$, $y \equiv S W_y$, $z \equiv S W_z$ with $W_x, W_y, W_z \in \mathcal{N}$, then $y x \equiv S W_y (S W_x) \in \mathcal{N}_2 \subset \mathcal{N}$ (and likewise $y z, z y \in \mathcal{N}$), whence $S(z y)S \in \mathcal{N}$, $S(y z)(S(z y)S) \in \mathcal{N}$, $S(y x)(\dots) \in \mathcal{N}$, and $R_{110}(x, y, z) \equiv S(\dots)$ is a Spine-$1$ normal form. For (b), dynamic programming over all $4^8 = 65{,}536$ truth vectors in $Q_{\mathcal{D}_4}^8$ reachable from $\{S, x, y, z\}$ by leaf size $s = 1, \dots, 11$ confirms that $(d_1, d_2, d_2, d_2, d_1, d_2, d_2, d_1)$ is absent for all $s \le 10$ and first appears at $s = 11$; finally, for any $g \in Q_{\mathcal{D}_4}$, $((g \odot x) \odot y) \odot z = d_3$ identically as above, while Lemma 6.4(i) forbids $(G x y) z \to_S^* S W$.
 $\square$

## 8. Wolfram's Benchmark Evolutions, Small-Term Minimality, and Catalan Phase Transitions

In his centennial monograph [71] and official prize announcement [70], Stephen Wolfram examined the empirical behavior of small $S$-terms across the Catalan tree hierarchy, highlighting the minimal $7$-leaf non-halting threshold, exhibiting twelve benchmark non-halting expressions $W_1, \dots, W_{12}$ of leaf sizes $8$ through $11$ whose leftmost-outermost leaf-growth differences display diverse transient and staircase patterns, and asking whether bounded-time “jump-ahead” procedures can predict asymptotic halting and structural outcomes without step-by-step simulation. In this section we classify all fourteen benchmark expressions algebraically and dynamically, establish linear-time multi-hole context halting and closed-form jump-ahead formulas, prove sharp existence and uniqueness theorems across all $23{,}714$ closed $S$-terms of leaf sizes $1 \le n \le 11$, and determine the asymptotic phase diagram of uniformly random $n$-leaf $S$-terms via analytic combinatorics and constructive Lean-verified majorants.

### 8.1. Algebraic and Dynamical Classification of Wolfram's Benchmark Expressions

Alongside Duboué's two minimal $7$-leaf non-normalizing $S$-terms $X_1 \equiv S(S S)S S S S$ and $X_2 \equiv S S S (S S) S S$ (communicated by Duboué and Baron in 1975; see [2], [1, Exercise 7.4.5], and [70, line 131]), let $W_1, \dots, W_{12}$ denote the twelve non-normalizing expressions displayed in lines 147–153 of [70]. Under leftmost-outermost reduction $\to_{\mathrm{lo}}$, whenever a closed $S$-term reaches a head normal form $S A_1$ or $S A_1 A_2$, the outer $S$-application freezes permanently as a *head-normal shell*: for $S A_1$, reduction descends into $A_1$; for $S A_1 A_2$, reduction descends into $A_1$ if $A_1 \notin \mathrm{SN}$, and otherwise normalizes $A_1 \to_{\mathrm{lo}}^* \mathrm{nf}(A_1) \in \mathcal{N}$ before descending permanently into $A_2$. Table 6 records the exact algebraic coordinates and $\to_{\mathrm{lo}}$ shell-stabilization behavior of all fourteen terms.

**Table 6.** Complete algebraic and $\to_{\mathrm{lo}}$ dynamical classification of Duboué's $7$-leaf terms $X_1, X_2$ and Wolfram's twelve challenge benchmarks $W_1, \dots, W_{12}$ [70]. State indices refer to $(\llbracket M \rrbracket_{\mathrm{SN}}, \llbracket M \rrbracket_{\mathrm{HN}}, \llbracket M \rrbracket_P)$ with sinks $(q_{38}, q_{34}, q_{37}) = (\infty_{\mathrm{SN}}, \infty_{\mathrm{HN}}, \infty_P)$.

| Term | Combinatory Form | Wolfram Announcement Syntax | $\vert M\vert $ | $(\mathrm{SN}, \mathrm{HN}, P)$ | Shells / Lock | $\to_{\mathrm{lo}}$ Dynamical Regime |
| :— | :— | :— | :—: | :—: | :—: | :— |
| $X_2$ | $S S S (S S) S S$ | `s[s][s][s[s]][s][s]` | $7$ | $(q_{38}, q_{23}, q_{37})$ | $1$ / step $8$ | Stabilizes $1$ shell, then $\infty_{\mathrm{HN}}$ |
| $X_1$ | $S(S S)S S S S$ | `s[s[s]][s][s][s][s]` | $7$ | $(q_{38}, q_{23}, q_{37})$ | $1$ / step $9$ | Steps in $1$ step to $X_2$; locks at step $9$ |
| $W_1$ | $S(S(S(S S)S))S S$ | `s[s[s[s[s]][s]]][s][s]` | $8$ | $(q_{38}, q_{23}, q_{37})$ | $4$ / step $18$ | Stabilizes $4$ shells, then $\infty_{\mathrm{HN}}$ |
| $W_2$ | $S S S (S(S S))(S S)$ | `s[s][s][s[s[s]]][s[s]]` | $8$ | $(q_{38}, q_{24}, q_{37})$ | $\infty$ / never | Perpetual $\mathrm{HN}\setminus\mathrm{SN}$; depth-$5$ $\bot$ |
| $W_3$ | $S S S (S(S(S S S)))S$ | `s[s][s][s[s[s[s][s]]]][s]` | $9$ | $(q_{38}, q_{34}, q_{37})$ | $0$ / step $0$ | Unsolvable ($\mathrm{BT} = \bot$) |
| $W_4$ | $S(S(S S)(S(S S)S))S S$ | `s[s[s[s]][s[s[s]][s]]][s][s]` | $10$ | $(q_{38}, q_{34}, q_{37})$ | $0$ / step $0$ | Unsolvable ($\mathrm{BT} = \bot$) |
| $W_5$ | $S S S S S S (S(S S))S$ | `s[s][s][s][s][s][s[s[s]]][s]` | $10$ | $(q_{38}, q_{23}, q_{37})$ | $1$ / step $21$ | Stabilizes $1$ shell, then $\infty_{\mathrm{HN}}$ |
| $W_6$ | $S S S (S(S(S S S)S))S$ | `s[s][s][s[s[s[s][s]][s]]][s]` | $10$ | $(q_{38}, q_{34}, q_{37})$ | $0$ / step $0$ | Unsolvable ($\mathrm{BT} = \bot$) |
| $W_7$ | $S(S S S (S S))(S S S)S$ | `s[s[s][s][s[s]]][s[s][s]][s]` | $10$ | $(q_{38}, q_{34}, q_{37})$ | $0$ / step $0$ | Unsolvable ($\mathrm{BT} = \bot$) |
| $W_8$ | $S S S (S(S S))(S S)(S S)$ | `s[s][s][s[s[s]]][s[s]][s[s]]` | $10$ | $(q_{38}, q_{23}, q_{37})$ | $1$ / step $8$ | Stabilizes $1$ shell, then $\infty_{\mathrm{HN}}$ |
| $W_9$ | $S S S S (S S S) S S S S$ | `s[s][s][s][s[s][s]][s][s][s][s]` | $11$ | $(q_{38}, q_{34}, q_{37})$ | $0$ / step $0$ | Unsolvable ($\mathrm{BT} = \bot$) |
| $W_{10}$ | $S S S (S(S(S(S S)S)S))S$ | `s[s][s][s[s[s[s[s]][s]][s]]][s]` | $11$ | $(q_{38}, q_{34}, q_{37})$ | $0$ / step $0$ | Unsolvable ($\mathrm{BT} = \bot$) |
| $W_{11}$ | $S S S (S S (S(S(S S S))))S$ | `s[s][s][s[s][s[s[s[s][s]]]]][s]` | $11$ | $(q_{38}, q_{25}, q_{37})$ | $1$ / step $4$ | Stabilizes $1$ shell, then $\infty_{\mathrm{HN}}$ |
| $W_{12}$ | $S(S(S S)S S)(S(S S)S)S$ | `s[s[s[s]][s][s]][s[s[s]][s]][s]` | $11$ | $(q_{38}, q_{34}, q_{37})$ | $0$ / step $0$ | Unsolvable ($\mathrm{BT} = \bot$) |

**Theorem 8.1 (Classification of Wolfram's benchmarks and separation of $W_2$ from $Z_{\mathrm{Zac}}$).** 
The fourteen benchmark $S$-terms $X_1, X_2, W_1, \dots, W_{12}$ of Table 6 all satisfy $\llbracket M \rrbracket_{\mathrm{SN}} = \infty_{\mathrm{SN}}$ and $\llbracket M \rrbracket_P = \infty_P$, and partition into three disjoint $\to_{\mathrm{lo}}$ regimes:

- (i) *(Immediate unsolvability)* Seven benchmarks—$W_3, W_4, W_6, W_7, W_9, W_{10}, W_{12}$—satisfy $\llbracket W_i \rrbracket_{\mathrm{HN}} = \infty_{\mathrm{HN}}$, executing pure head reduction forever with $\mathrm{BT}(W_i) = \bot$.
- (ii) *(Finite shell stabilization into $\infty_{\mathrm{HN}}$)* Six benchmarks—$X_1, X_2, W_1, W_5, W_8, W_{11}$—lie in $\mathrm{HN} \setminus \mathrm{Prod}$ and emit $4$ head-normal shells for $W_1$ and $1$ shell for each of the other five before their active $\to_{\mathrm{lo}}$ focus locks permanently into $\infty_{\mathrm{HN}}$ at steps $9, 8, 18, 21, 8, 4$, respectively.
- (iii) *(Perpetual solvable focus with hidden $\bot$)* Uniquely among all fourteen benchmarks, $W_2 \equiv S S S (S T) T$ ($8$ leaves, $T \equiv S S$) maintains an active $\to_{\mathrm{lo}}$ focus in $\mathrm{HN} \setminus \mathrm{SN}$ at every step $t \in \mathbb{N}$: defining $E_0 \equiv S(S T)T$ and $E_{m+1} \equiv T E_m$, after $\frac{1}{2}(n+1)(n+6) + 1$ steps ($n \ge 0$), $W_2$ reaches active focus $E_0 E_{n+1}$ ($\mathrm{HN}$ state $q_{23} \neq \infty_{\mathrm{HN}}$) beneath $\frac{1}{2}(n+1)(n+2)$ head-normal shells. Nevertheless, $\mathrm{BT}(W_2)$ contains an unsolvable subterm ($\infty_{\mathrm{HN}}$) at depth $5$, whence $W_2 \notin \mathrm{Prod}$, $W_2 \neq_S Z_{\mathrm{Zac}}$, and $W_2 \neq_S Z_0 \equiv S(S T)(S T)T$.

*Proof.* 
Regimes (i) and (ii) follow directly from Theorem 6.6(i) by evaluating $\llbracket \cdot \rrbracket_{\mathrm{HN}}$ on the initial terms and tracing $4$ to $21$ deterministic $\to_{\mathrm{lo}}$ steps until the unique active subterm beneath the stabilized $\mathrm{HNF}$ context reaches $\mathrm{HN}$ state $\infty_{\mathrm{HN}}$, after which pure head reduction continues inside that focus forever because $\infty_{\mathrm{HN}}$ admits no $\mathrm{HNF}$.

For (iii), set $E_0 \equiv S(S T)T \in \mathcal{N}$ ($6$ leaves) and $E_{m+1} \equiv T E_m \equiv S S E_m \in \mathcal{N}$ ($m \ge 0$). Tracing the first four $\to_{\mathrm{lo}}$ steps of $W_2 \equiv ((S S S)(S T)) T$ yields

$$
\begin{aligned}
W_2 &\;\equiv\; ((S S S)(S T)) T
\;\longrightarrow_{\mathrm{lo}}\; \bigl(S(S T)(S(S T))\bigr) T
\;\longrightarrow_{\mathrm{lo}}\; (S T T)\bigl(S(S T) T\bigr) \;\equiv\; (S T T)\,E_0 \\
&\;\longrightarrow_{\mathrm{lo}}\; (T E_0)(T E_0) \;\equiv\; (S S E_0)\,E_1
\;\longrightarrow_{\mathrm{lo}}\; S\,E_1\,(E_0 E_1).
\end{aligned}
$$

Because $E_1 \in \mathcal{N}$ is in normal form, step $4$ stabilizes the Spine-$2$ right-hole shell $S\,E_1\,\square$ (shell depth $1$ at $n = 0$, matching $\frac{1}{2}(0+1)(0+6) + 1 = 4$) around the active focus $E_0 E_1$. From any focus $E_0 E_{k+1}$ ($k \ge 0$), three $\to_{\mathrm{lo}}$ steps give

$$
E_0 E_{k+1} \;\equiv\; S(S T)T\,E_{k+1}
\;\longrightarrow_{\mathrm{lo}}\; (S T E_{k+1})\,E_{k+2}
\;\longrightarrow_{\mathrm{lo}}\; E_{k+3}\,(E_{k+1} E_{k+2})
\;\longrightarrow_{\mathrm{lo}}\; S\,\bigl(E_{k+1} E_{k+2}\bigr)\,\bigl(E_{k+2}(E_{k+1} E_{k+2})\bigr).
$$

Here the outer shell $S\,\square\,[E_{k+2}(E_{k+1} E_{k+2})]$ permanently freezes its right sibling $R_{\mathrm{fr}}(k) \equiv E_{k+2}(E_{k+1} E_{k+2})$ and enters the left child $E_{k+1} E_{k+2}$, which then executes $k + 1$ single-step countdowns $E_{m+1} E_{k+2} \equiv S S E_m E_{k+2} \to_{\mathrm{lo}} S E_{k+2} (E_m E_{k+2})$ ($m = k, \dots, 0$, each $E_{k+2} \in \mathcal{N}$) down to $E_0 E_{k+2}$. Summing $4 + \sum_{j=0}^{n-1} (j + 4) = \frac{1}{2}(n+1)(n+6) + 1$ steps and $1 + \sum_{j=0}^{n-1} (j + 2) = \frac{1}{2}(n+1)(n+2)$ shells establishes the closed-form trajectory, with every intermediate focus in $F_{\mathrm{HN}}$. Yet at $k = 0$, the first orphaned right sibling $R_{\mathrm{fr}}(0) \equiv E_2(E_1 E_2)$ sits at shell depth $2$ inside $S\,E_1\,(S\,\square\,R_{\mathrm{fr}}(0))$, and unfolding three further Böhm levels inside $R_{\mathrm{fr}}(0)$ reaches an unsolvable subterm ($\infty_{\mathrm{HN}}$) at Böhm depth $5$. Thus $\llbracket W_2 \rrbracket_P = \infty_P \neq q_{29} = \llbracket Z_{\mathrm{Zac}} \rrbracket_P = \llbracket Z_0 \rrbracket_P$, proving $W_2 \neq_S Z_{\mathrm{Zac}}$ and $W_2 \neq_S Z_0$.
 $\square$

### 8.2. Compositional Context Halting and Closed-Form Jump-Ahead

In line 179 of [70], Wolfram asks whether “jump-ahead” procedures—algorithms guaranteed to halt in bounded time—can determine halting or predict future configurations of $S$-terms without simulating reduction step by step. Theorems 6.2 and 6.6 provide exact $O(|M|)$ jump-ahead halting deciders for $\to_{\mathrm{lo}}$ and $\to_h$, and compositionality of $\mathcal{A}_{\mathrm{SN}}$ and $\mathcal{A}_{\mathrm{HN}}$ extends this to multi-hole contexts whose explicit substitution would blow up exponentially in tree size.

**Proposition 8.2 (Linear-time multi-hole context halting and closed-form jump-ahead).**

- (i) *(Compositional $k$-hole context halting)* Let $C[\square_1, \dots, \square_k]$ be an arbitrary $k$-hole $S$-context (allowing each hole $\square_i$ to appear arbitrarily many times at arbitrary depths) of syntactic size $|C|$, and let $M_1, \dots, M_k \in \mathcal{T}_S$ be closed arguments. Whether $C[M_1, \dots, M_k]$ halts under $\to_{\mathrm{lo}}$ (respectively $\to_h$) is decidable in $O\bigl(|C| + \sum_{i=1}^k |M_i|\bigr)$ time without constructing $C[M_1, \dots, M_k]$.
- (ii) *(Two-parameter jump-ahead on $D_{\mathrm{seed}}$)* On the $10$-leaf seed $D_{\mathrm{seed}} \equiv S(S(S S))(S(S S))(S S)S$, setting $C_0 \equiv S T T$ and $C_{m+1} \equiv T C_m$ ($T \equiv S S$), for every $n \ge 1$ and $0 \le r \le n$, step $(2n^2 - n + 1) + 4r$ under $\to_{\mathrm{lo}}$ places $D_{\mathrm{seed}}$ at active counter focus $C_{n-r} C_n S$ beneath $\frac{1}{2}n(n-1) + r$ left-active head-normal shells (reaching $C_0 C_n S$ at step $2n^2 + 3n + 1$ when $r = n$).
- (iii) *(Exact quarter-square normal-form step count on left spines)* Define the left-associated spine $P_0 \equiv S$, $P_{m+1} \equiv P_m S$ ($m + 1$ leaves, arity $m \ge 0$). Then $P_m$ reaches its normal form under $\to_{\mathrm{lo}}$ in exact step count 
$$
s(m) \;=\; \Bigl\lfloor \frac{m-1}{2} \Bigr\rfloor \cdot \Bigl\lfloor \frac{m}{2} \Bigr\rfloor
\qquad (m \in \mathbb{N}), \tag{8.1}
$$
 whereas the right-associated tower $R_m$ ($R_0 \equiv S$, $R_{m+1} \equiv S R_m$) is already in normal form ($0$ steps).

*Proof.* 
For (i), evaluate $q_i = \llbracket M_i \rrbracket_{\mathrm{SN}} \in Q_{\mathrm{SN}}$ (or $\llbracket M_i \rrbracket_{\mathrm{HN}} \in Q_{\mathrm{HN}}$) in $2|M_i| - 1$ lookups for $1 \le i \le k$, then evaluate $C$ bottom-up in $|C|$ lookups by assigning state $q_i$ to every occurrence of $\square_i$ and $q_0$ to $S$. By homomorphic compositionality of $\llbracket \cdot \rrbracket_{\mathcal{A}}$, the root state equals $\llbracket C[M_1, \dots, M_k] \rrbracket_{\mathcal{A}}$, deciding $\mathrm{SN}$ (hence $\to_{\mathrm{lo}}$ halting by standardization and Proposition 2.2) and $\mathrm{HN}$ ($\to_h$ halting) in $O(|C| + \sum |M_i|)$ time.

For (ii), two initial contractions reduce $D_{\mathrm{seed}} \equiv S(S T)(S T)T S \to_{\mathrm{lo}} (S T T)(S T T) S \equiv C_0 C_0 S \to_{\mathrm{lo}} (T C_0)(T C_0) S \equiv C_1 C_1 S$, reaching $(1, 1)$ at step $2 = 2(1)^2 - 1 + 1$ with $0$ shells. From any counter state $C_{m+1} C_p S \equiv (S S C_m) C_p S$ ($p \ge 1$), four $\to_{\mathrm{lo}}$ contractions via $((S C_p)(C_m C_p)) S \to_{\mathrm{lo}} (C_p S)(C_m C_p S) \equiv (S S (C_{p-1} S))(C_m C_p S)$ produce $S\,(C_m C_p S)\,\bigl((C_{p-1} S)(C_m C_p S)\bigr)$, adding one left-active Spine-$2$ shell around $C_m C_p S$; at $m = 0$, a single contraction resets $C_0 C_p S \equiv S T T C_p S \to_{\mathrm{lo}} (T C_p)(T C_p) S \equiv C_{p+1} C_{p+1} S$ with $0$ additional shells. Induction over $n \ge 1$ sums $2 + \sum_{j=1}^{n-1} (4j + 1) = 2n^2 - n + 1$ steps and $\sum_{j=1}^{n-1} j = \frac{1}{2}n(n-1)$ shells to reach $C_n C_n S$, after which $r$ further countdown transitions ($0 \le r \le n$) add $4r$ steps and $r$ shells to reach $C_{n-r} C_n S$.

For (iii), $P_0 \equiv S$, $P_1 \equiv S S$, and $P_2 \equiv S S S$ lie in $\mathcal{N}$, matching $s(0) = s(1) = s(2) = 0$. For $m = d + 3$ ($d \ge 0$), $P_{d+3} \equiv S S S S S^d \to_{\mathrm{lo}} (S S)(S S) S^d$, which peels in $d$ further $\to_{\mathrm{lo}}$ steps via $(S S) U S \to_{\mathrm{lo}} S S (U S)$ to $(S S)\,P_{d+1} \equiv T\,P_{d+1}$, giving $P_{d+3} \to_{\mathrm{lo}}^{d+1} T\,P_{d+1}$ with spine arity at least $3$ at all $j < d + 1$ steps. Because $T\,U \equiv S S U$ is a Spine-$2$ right-hole shell $S\,S\,\square$ with $S \in \mathcal{N}$, subsequent $\to_{\mathrm{lo}}$ steps act strictly inside $P_{d+1}$, yielding the recurrence $s(d + 3) = (d + 1) + s(d + 1)$. Since $\lfloor \frac{d+2}{2} \rfloor \lfloor \frac{d+3}{2} \rfloor - \lfloor \frac{d}{2} \rfloor \lfloor \frac{d+1}{2} \rfloor = (\lfloor \frac{d}{2} \rfloor + 1)(\lfloor \frac{d+1}{2} \rfloor + 1) - \lfloor \frac{d}{2} \rfloor \lfloor \frac{d+1}{2} \rfloor = \lfloor \frac{d}{2} \rfloor + \lfloor \frac{d+1}{2} \rfloor + 1 = d + 1$, induction on $m$ establishes (8.1).
 $\square$

### 8.3. Small-Term Catalan Census and Sharp Minimality Thresholds

By Section 2.1, the closed $S$-terms of leaf size $n \ge 1$ have cardinality $C_{n-1} = \frac{1}{n}\binom{2n-2}{n-1}$. Table 7 reports the exact cardinalities of normal forms ($\mathcal{N}$, enumerated by the Motzkin numbers $M_{n-1}$), strongly normalizing terms ($\mathrm{SN}$), productive terms ($\mathrm{Prod}$), productive non-normalizing terms ($\mathrm{Prod} \setminus \mathrm{SN}$), solvable terms ($\mathrm{HN}$), and unsolvable terms ($\overline{\mathrm{HN}}$) for $1 \le n \le 11$ (a cumulative total of $23{,}714$ trees, extended by dynamic programming to $n = 150$).

**Table 7.** Exact Catalan phase census of closed $S$-terms for leaf sizes $1 \le n \le 11$ and sharp onset thresholds.

| $n$ | $C_{n-1}$ | $\#\mathcal{N}$ | $\#\mathrm{SN}$ | $\#\mathrm{Prod}$ | $\#(\mathrm{Prod}\setminus\mathrm{SN})$ | $\#\mathrm{HN}$ | $\#\overline{\mathrm{HN}}$ | Sharp Structural Threshold |
| —: | —: | —: | —: | —: | —: | —: | —: | :— |
| $1$ | $1$ | $1$ | $1$ | $1$ | $0$ | $1$ | $0$ | Unique atom $S$ |
| $2$ | $1$ | $1$ | $1$ | $1$ | $0$ | $1$ | $0$ | Unique Spine-$1$ atom $S S$ |
| $3$ | $2$ | $2$ | $2$ | $2$ | $0$ | $2$ | $0$ | All terms in $\mathcal{N}$ for $n \le 3$ |
| $4$ | $5$ | $4$ | $5$ | $5$ | $0$ | $5$ | $0$ | Unique minimal redex $S S S S$ |
| $5$ | $14$ | $9$ | $14$ | $14$ | $0$ | $14$ | $0$ | Max reduction length $2$ |
| $6$ | $42$ | $21$ | $42$ | $42$ | $0$ | $42$ | $0$ | Universal $\mathrm{SN}$ & deterministic $\to_S$ ($n \le 6$) |
| $7$ | $132$ | $51$ | $130$ | $130$ | $0$ | $132$ | $0$ | Minimal $\overline{\mathrm{SN}}$ ($X_1, X_2$); $1$-step diamond break |
| $8$ | $429$ | $127$ | $388$ | $388$ | $0$ | $414$ | $15$ | Minimal $\overline{\mathrm{HN}}$ ($15$ terms); $\mathrm{Prod} = \mathrm{SN}$ ($n \le 8$) |
| $9$ | $1{,}430$ | $323$ | $1{,}154$ | $1{,}155$ | $1$ | $1{,}294$ | $136$ | Unique minimal $\mathrm{Prod} \setminus \mathrm{SN}$ ($Z_0$); $15$ in $\mathrm{RNF}\setminus\mathrm{HN}$ |
| $10$ | $4{,}862$ | $835$ | $3{,}381$ | $3{,}383$ | $2$ | $4{,}121$ | $741$ | $S Z_0$ and Zachos's $Z_{\mathrm{Zac}} \equiv G_0 G_0$ appear |
| $11$ | $16{,}796$ | $2{,}188$ | $9{,}967$ | $9{,}972$ | $5$ | $13{,}596$ | $3{,}200$ | Normalizing fraction $\#\mathrm{SN}/C_{10} \approx 59.34\%$ |

**Theorem 8.3 (Sharp small-term minimality and confluence thresholds).** 
Across all closed $S$-terms $M \in \mathcal{T}_S$:

- (i) *(Universal $\mathrm{SN}$ and determinism up to size $6$)* Every closed $S$-term with $|M| \le 6$ ($65$ terms in total) is strongly normalizing and satisfies $\#\mathrm{Redex}(M) \le 1$, so one-step multiway reduction $M \to_S N$ is deterministic for $|M| \le 6$.
- (ii) *(Size-$7$ non-halting and strict diamond thresholds)* Among the $132$ closed $S$-terms with $|M| = 7$, all $132$ lie in $\mathrm{HN}$, $130$ lie in $\mathrm{SN}$, and exclusively $X_1 \equiv S(S S)S S S S$ and $X_2 \equiv S S S (S S) S S$ fail to normalize. Exactly $3$ terms of size $7$ admit multiway branching ($\#\mathrm{Redex}(M) = 2$): $S S S (S S S S)$, $S S (S S S S) S$, and $S(S S S S) S S$. Among all $197$ terms with $|M| \le 7$, $S S S (S S S S)$ is the unique counterexample to the strict one-step $\to_S$ diamond property (joining instead in one parallel step at $\mathrm{gk}(S S S (S S S S))$).
- (iii) *(Size-$8$ unsolvability threshold and $\mathrm{Prod} = \mathrm{SN}$)* Every closed $S$-term with $|M| \le 7$ is solvable; at $|M| = 8$ ($429$ terms), $15$ terms lie in $\overline{\mathrm{HN}}$ (all evaluating to $q_{34}$ in $\mathcal{A}_{36}$, such as $S A S A$ and $S(S S)S S S S S$). Moreover, $M \in \mathrm{Prod}$ if and only if $M \in \mathrm{SN}$ for all $626$ closed $S$-terms with $|M| \le 8$.
- (iv) *(Unique size-$9$ productive non-$\mathrm{SN}$ combinator and minimal $\mathrm{RNF} \setminus \mathrm{HN}$)* Out of all $2{,}056$ closed $S$-terms with $|M| \le 9$, $Z_0 \equiv S(S(S S))(S(S S))(S S)$ ($9$ leaves, reducing in one step to $Z_{\mathrm{Zac}}$) is the *unique* productive non-normalizing $S$-term. Size $9$ is also the minimal leaf size of $\mathrm{RNF} \setminus \mathrm{HN}$, inhabited by the $15$ terms $U S$ ($q_{35}$ in $\mathcal{A}_{36}$) obtained by applying the $15$ size-$8$ unsolvable terms $U$ to $S$.

*Proof.* 
Constructive tree enumeration generates for each $n \ge 1$ the duplicate-free list $\mathcal{L}_n$ of all $C_{n-1}$ closed $S$-trees via binary splits $n = n_1 + n_2$ ($n_1, n_2 \ge 1$). Applying the sound and complete algebraic characterizations of Theorems 6.2, 6.6, and 6.12 across $\mathcal{L}_1, \dots, \mathcal{L}_9$ establishes all $\mathrm{SN}$, $\mathrm{HN}$, $\mathrm{Prod}$, and $\mathrm{RNF} \setminus \mathrm{HN}$ counts and isolates $\{X_1, X_2\}$ at $n = 7$, the $15$ unsolvable witnesses at $n = 8$ (notice that by (6.10), any $M \equiv P Q \in \mathrm{RNF} \setminus \mathrm{HN}$ requires $P \in \overline{\mathrm{HN}}$, hence $|P| \ge 8$ and $|P Q| = |P| + |Q| \ge 8 + 1 = 9$, with equality if and only if $|P| = 8$ and $Q \equiv S$), and the unique inhabitant $Z_0$ of $\mathrm{Prod} \setminus \mathrm{SN}$ at $n \le 9$.

For the multiway branching and diamond claims in (i)–(ii), every redex $S X Y Z$ has at least $4$ leaves; hence a tree with $\#\mathrm{Redex}(M) \ge 2$ either contains two disjoint redexes (requiring at least $4 + 4 = 8$ leaves) or nests one redex strictly inside an argument of another (requiring at least $3 + 4 = 7$ leaves, achieved exclusively by placing $S S S S$ in one of the three argument slots of $S \square_1 \square_2 \square_3$ with the remaining two slots equal to $S$). Thus $\#\mathrm{Redex}(M) \le 1$ for $|M| \le 6$. At $|M| = 7$, both $S(S S S S)S S$ and $S S (S S S S) S$ satisfy the strict one-step diamond property because $S S S S$ occurs linearly ($1$ copy) after root contraction, whereas $S S S (S S S S)$ duplicates its third argument:

$$
S S S (S S S S) \;\longrightarrow_S\; S(S S S S)\bigl(S(S S S S)\bigr) \;\equiv\; N_L,
\qquad
S S S (S S S S) \;\longrightarrow_S\; S S S \bigl(S S (S S)\bigr) \;\equiv\; N_R.
$$

Contracting the outer root of $N_R$ yields $S(S S (S S))\bigl(S(S S (S S))\bigr) \equiv \mathrm{gk}(S S S (S S S S))$, which requires *two* sequential $\to_S$ steps from $N_L$ (one in each duplicated copy of $S S S S$), refuting a $1$-step $\to_S$ join while confirming a $1$-step parallel $\Rightarrow_p$ join.
 $\square$

### 8.4. Analytic Combinatorics and Constructive Catalan Phase Transitions

We conclude our technical analysis by determining the asymptotic behavior of a uniformly random closed $S$-term of $n$ leaves as $n \to \infty$. In quantitative studies of untyped $\lambda$-calculus [10, 32, 11, 20], David et al. [20] proved that almost all $\lambda$-terms are strongly normalizing, whereas in combinatory logic $\mathrm{CL}(S, K)$ Bendkowski, Grygiel, Lescanne, and Zaionc [6, 7, 5] showed via Woods-type subgraph containment [72] that almost no $\{S, K\}$-combinators normalize. For $\mathrm{CL}(S)$, where $\mathrm{SN}$, $\mathrm{Prod}$, and $\mathrm{HN}$ are all recognized by explicit finite deterministic $S$-algebras, we obtain an exact four-phase asymptotic partition governed by algebraic generating functions [23, 28], paired with elementary all-$n$ rational majorants proved constructively over $\mathbb{N}$ without complex analysis.

First, forming the reachable product of $\mathcal{A}_{\mathrm{SN}} \times \mathcal{A}_P \times \mathcal{A}_{\mathrm{HN}}$ from $(q_0, q_0, q_0)$ yields $146$ reachable state triples: $98$ in $\mathrm{SN}$, $30$ in $\mathrm{Prod} \setminus \mathrm{SN}$, $17$ in $\mathrm{HN} \setminus \mathrm{Prod}$, and $1$ in $\overline{\mathrm{HN}}$, establishing the strict global inclusions $\mathrm{SN} \subsetneq \mathrm{Prod} \subsetneq \mathrm{HN} \subsetneq \mathcal{T}_S$ and the counting hierarchy $\#\mathrm{SN}(n) \le \#\mathrm{Prod}(n) \le \#\mathrm{HN}(n) \le C_{n-1}$ for every $n \ge 1$.

For any finite $S$-algebra $\mathcal{A} = (Q, q_0, \odot)$, let $L_q(z) = \sum_{n=1}^{\infty} a_q(n)\,z^n$ denote the ordinary generating function (OGF) in which $z$ marks $S$-leaves and $a_q(n) = \#\{ M \in \mathcal{T}_S : |M| = n,\; \llbracket M \rrbracket_{\mathcal{A}} = q \}$. Decomposition at the root of each tree translates directly into the positive quadratic polynomial system

$$
L_q(z) \;=\; \delta_{q, q_0}\,z \;+\; \sum_{\substack{(r, s) \in Q^2 \\ r \odot s = q}} L_r(z)\,L_s(z)
\qquad (q \in Q), \tag{8.2}
$$

whose sum across all $q \in Q$ satisfies $\sum_{q \in Q} L_q(z) = T(z) = \sum_{n=1}^{\infty} C_{n-1} z^n = \frac{1 - \sqrt{1 - 4z}}{2}$, singular at the Catalan radius $z = \frac{1}{4}$ where $[z^n] T(z) = C_{n-1} \sim \frac{4^{n-1}}{\sqrt{\pi}\,n^{3/2}}$.

**Theorem 8.4 (Asymptotic phase diagram and constructive majorants for $\mathrm{CL}(S)$).** 
Let $\#\mathrm{SN}(n)$, $\#\mathrm{Prod}(n)$, and $\#\mathrm{HN}(n)$ denote the numbers of closed $S$-terms of leaf size $n \ge 1$ in $\mathrm{SN}$, $\mathrm{Prod}$, and $\mathrm{HN}$, respectively.

- (i) *(Exact dyadic-ternary rational density of solvable $S$-terms)* In $\mathcal{A}_{\mathrm{HN}}$, the quadratic system (8.2) over $F_{\mathrm{HN}} = \{q_0, \dots, q_{33}\}$ decomposes along strongly connected components so that at the Catalan singularity $z = \frac{1}{4}$ ($u = \sqrt{1 - 4z} = 0$), every coordinate $L_q(\frac{1}{4}) \in \mathbb{Q}$ is rational and the singular Puiseux expansion $L_q(z) = L_q(\frac{1}{4}) - b_q\sqrt{1 - 4z} + O(1 - 4z)$ solves a triangular rational linear system, yielding the exact limiting solvable density 
$$
c_{\mathrm{HN}} \;:=\; \lim_{n \to \infty} \frac{\#\mathrm{HN}(n)}{C_{n-1}}
\;=\; 2 \sum_{q \in F_{\mathrm{HN}}} b_q
\;=\; \frac{4{,}429{,}673}{7{,}077{,}888}
\;=\; \frac{4{,}429{,}673}{2^{18} \cdot 3^3}
\;\approx\; 0.6258467215, \tag{8.3}
$$
 and complementary unsolvable density $1 - c_{\mathrm{HN}} = \frac{2{,}648{,}215}{7{,}077{,}888} \approx 0.3741532785$. Moreover, elementary constructive tree injections prove unconditionally for all $n$: 
$$
2\,C_{n-2} \;\le\; \#\mathrm{HN}(n) \quad (n \ge 3)
\qquad\text{and}\qquad
\#\mathrm{HN}(n) + C_{n-9} \;\le\; C_{n-1} \quad (n \ge 9), \tag{8.4}
$$
 so $\frac{1}{2} < \frac{\#\mathrm{HN}(n)}{C_{n-1}} \le 1 - \frac{C_{n-9}}{C_{n-1}}$ holds for every $n \ge 9$.
- (ii) *(Algebraic singularities and exponential decay of $\mathrm{SN}$ and $\mathrm{Prod}$)* Because $\infty_{\mathrm{SN}}$ in $\mathcal{A}_{\mathrm{SN}}$ and $\infty_P$ in $\mathcal{A}_P$ are two-sided absorbing sinks coupled into top $4$-state strongly connected components ($\{q_6, q_{25}, q_{29}, q_{30}\}$ with pivot $q_{30}$ in $\mathcal{A}_{\mathrm{SN}}$; $\{q_{18}, q_{24}, q_{29}, q_{33}\}$ with pivot $q_{29}$ in $\mathcal{A}_P$), the generating functions $\sum_{q \in F_{\mathrm{SN}}} L_q(z)$ and $\sum_{q \in F_P} L_q(z)$ have dominant square-root singularities $r_{\mathrm{SN}} < \frac{1}{3}$ and $r_P < r_{\mathrm{SN}}$ strictly larger than $\frac{1}{4}$, governed by irreducible degree-$35$ minimal polynomials $P_{\mathrm{SN}}(z), P_P(z) \in \mathbb{Z}[z]$: 
$$
\begin{aligned}
P_{\mathrm{SN}}(z) &\;=\; 8 z^{35} + 28 z^{34} - 76 z^{33} - 384 z^{32} + \cdots - 5550 z^{10} + 3898 z^9 + \cdots - 73 z^3 - 3 z^2 + 7 z - 1, \\
P_P(z) &\;=\; 12 z^{35} + 48 z^{34} - 88 z^{33} - 584 z^{32} - \cdots - 5546 z^{10} + 3898 z^9 + \cdots - 73 z^3 - 3 z^2 + 7 z - 1,
\end{aligned}
$$
 with exponential growth rates $\gamma_{\mathrm{SN}} = r_{\mathrm{SN}}^{-1} \approx 3.3699195015 < \gamma_P = r_P^{-1} \approx 3.3699837893 < 4$. Constructively over $\mathbb{N}$ (at rational test point $z_0 = \frac{37}{125} = 0.296 < r_P < r_{\mathrm{SN}}$, where $\frac{1}{4 z_0} = \frac{125}{148}$ and certified majorants yield base $\frac{250}{259} < 1$), for every $n \ge 1$: 
$$
\frac{\#\mathrm{SN}(n)}{C_{n-1}} \;\le\; 51.39438 \cdot \Bigl(\frac{250}{259}\Bigr)^n,
\qquad
\frac{\#\mathrm{Prod}(n)}{C_{n-1}} \;\le\; 51.42860 \cdot \Bigl(\frac{250}{259}\Bigr)^n. \tag{8.5}
$$
 Consequently, almost all closed $S$-terms as $n \to \infty$—a proportion tending to $1$—neither halt nor generate a $\bot$-free Böhm tree, partitioning in the limit into proportions $c_{\mathrm{HN}} \approx 0.625847$ in $\mathrm{HN} \setminus \mathrm{Prod}$ and $1 - c_{\mathrm{HN}} \approx 0.374153$ of unsolvable terms in $\overline{\mathrm{HN}}$.

*Proof.* 
For (i), in $\mathcal{A}_{\mathrm{HN}}$, because $\infty_{\mathrm{HN}}$ is a left sink ($L_{\infty_{\mathrm{HN}}}(z)$ appears only on the right of $\odot_{\mathrm{HN}}$, where $q_0 \odot_{\mathrm{HN}} \infty_{\mathrm{HN}} = q_{10}$ and $(q_0 \odot_{\mathrm{HN}} x) \odot_{\mathrm{HN}} \infty_{\mathrm{HN}}$ feed back using total tree sum $\sum_{s \in Q_{\mathrm{HN}}} L_s(z) = T(z)$), substituting $\sum_{s \in Q_{\mathrm{HN}}} L_s(z) = T(z) = \frac{1 - u}{2}$ ($u = \sqrt{1 - 4z}$, $z = \frac{1 - u^2}{4}$) eliminates $L_{\infty_{\mathrm{HN}}}(z)$ and expresses the $34$-variable system over $F_{\mathrm{HN}}$ in a lower-triangular block hierarchy whose diagonal equations are at most quadratic with rational square roots at $u = 0$: specifically, $L_{q_0}(\frac{1}{4}) = \frac{1}{4}$, $L_{q_1}(\frac{1}{4}) = \frac{1}{16}$, $\dots$, down to exact dyadic-ternary rationals $a_q = L_q(\frac{1}{4}) \in \mathbb{Z}[\frac{1}{6}]$ summing on $\infty_{\mathrm{HN}}$ to $L_{\infty_{\mathrm{HN}}}(\frac{1}{4}) = \frac{3{,}366{,}067}{113{,}246{,}208}$. Differentiating (8.2) with respect to $u$ at $u = 0$ yields a non-singular linear system $(I - 2 M(a))\,b = \tilde{e}$ over $\mathbb{Q}$ (since the Jacobian $2 M(a)$ over $F_{\mathrm{HN}}$ has spectral radius strictly below $1$, reflecting that a positive fraction of applications leak into $\infty_{\mathrm{HN}}$), whose unique rational solution satisfies $2 \sum_{q \in F_{\mathrm{HN}}} b_q = \frac{4{,}429{,}673}{7{,}077{,}888}$. Because $L_q(z)$ are algebraic power series with non-negative coefficients dominated coefficientwise by $T(z)$ (hence analytic in a $\Delta$-domain around $z = \frac{1}{4}$ with no other singularities on $|z| = \frac{1}{4}$, as $L_q(z) = \delta_{q,0} z + O(z^2)$ is aperiodic), Flajolet and Sedgewick's Transfer Theorem [28, Theorem VI.1 and Section VII.6] yields $[z^n] \sum_{q \in F_{\mathrm{HN}}} L_q(z) = \bigl(2 \sum_{q \in F_{\mathrm{HN}}} b_q\bigr) [z^n] T(z) \cdot (1 + O(n^{-1}))$, proving (8.3).

To establish the elementary all-$n$ inequalities (8.4) constructively, for $n \ge 3$ every tree $U$ of size $n - 1 \ge 2$ ($C_{n-2}$ trees in total) is a binary application $U \equiv L R$; the two disjoint maps $U \mapsto S U \in \mathrm{HNF}_1$ and $(L, R) \mapsto S L R \in \mathrm{HNF}_2$ inject $\mathcal{T}_{S, n-1}$ onto Spine-$1$ and Spine-$2$ head normal forms of size $n$, yielding $\#\mathrm{HN}(n) \ge C_{n-2} + C_{n-2} = 2 C_{n-2}$. Conversely, for $n \ge 9$, fix an $8$-leaf unsolvable witness $U_8 \in \overline{\mathrm{HN}}$ (such as $S A S A$); for every tree $W$ of size $n - 8$ ($C_{n-9}$ trees), Left $\bot$-Propagation at $d = 0$ ($\infty_{\mathrm{HN}} \odot_{\mathrm{HN}} y = \infty_{\mathrm{HN}}$) places $U_8 W \in \overline{\mathrm{HN}}$, and $(U_8, W) \mapsto U_8 W$ is injective, giving $\#\overline{\mathrm{HN}}(n) \ge C_{n-9}$ and $\#\mathrm{HN}(n) + C_{n-9} \le C_{n-1}$.

For (ii), eliminating the $34$ lower transient and acyclic states of $F_{\mathrm{SN}}$ (respectively $F_P$) in (8.2) reduces the top $4$-state strongly connected component to a single quadratic equation $A_2(z)\,Y^2 - B_1(z)\,Y + C_0(z) = 0$ ($\deg A_2 = 30, \deg B_1 = 34, \deg C_0 = 38$) for the pivot generating function $Y = L_{q_{30}}(z)$ (respectively $L_{q_{29}}(z)$), whose discriminant $B_1(z)^2 - 4 A_2(z) C_0(z)$ factors over $\mathbb{Z}[z]$ with minimal root $r_{\mathrm{SN}}$ of $P_{\mathrm{SN}}(z)$ (respectively $r_P$ of $P_P(z)$, sharing identical coefficients up to $z^9$ because $\mathrm{Prod}$ and $\mathrm{SN}$ agree for all $n \le 8$ by Theorem 8.3(iii)). By the Drmota–Lalley–Woods Theorem [23, 72], [28, Theorem VII.6], $[z^n] \sum_{q \in F_{\mathrm{SN}}} L_q(z) \sim \alpha_{\mathrm{SN}}\,\gamma_{\mathrm{SN}}^n n^{-3/2}$ and $[z^n] \sum_{q \in F_P} L_q(z) \sim \alpha_P\,\gamma_P^n n^{-3/2}$. Finally, to prove (8.5) constructively over $\mathbb{N}$ without complex analysis, choose positive rational upper-envelope vectors $\mathbf{v}_{\mathrm{SN}} \in \mathbb{Q}_{>0}^{38}$ and $\mathbf{v}_P \in \mathbb{Q}_{>0}^{38}$ satisfying quadratic sub-invariance $\delta_{q, q_0}\,z_0 + \sum_{r \odot s = q} v_r v_s \le v_q$ at $z_0 = \frac{37}{125}$. Defining truncated partial sums $S_{q, N}(z_0) = \sum_{n=1}^N a_q(n)\,z_0^n$, induction on $N \ge 1$ shows $S_{q, N+1}(z_0) \le \delta_{q, q_0}\,z_0 + \sum_{r \odot s = q} S_{r, N}(z_0)\,S_{s, N}(z_0) \le v_q$, whence $a_q(n) \le v_q\,z_0^{-n} = v_q (\frac{125}{37})^n$ for every $n \ge 1$. Pairing this upper bound with the elementary inductive Catalan lower bound $C_{n-1} \ge c_0 (\frac{7}{2})^n$ (since $\frac{C_n}{C_{n-1}} = \frac{4n-2}{n+1} \ge \frac{7}{2}$ for all $n \ge 11$, with $1 \le n \le 11$ verified directly) and simplifying the ratio

$$
\frac{(125 / 37)^n}{(7 / 2)^n} \;=\; \Bigl(\frac{250}{259}\Bigr)^n
$$

yields the exact constructive integer inequalities $100{,}000 \cdot 259^n \cdot \#\mathrm{SN}(n) \le 5{,}139{,}438 \cdot 250^n \cdot C_{n-1}$ and $100{,}000 \cdot 259^n \cdot \#\mathrm{Prod}(n) \le 5{,}142{,}860 \cdot 250^n \cdot C_{n-1}$ for all $n \ge 1$.
 $\square$

## 9. Constructive Formalization in Lean 4 and Cross-Language Verification

Following the methodology established in large-scale mechanized mathematics and theoretical computer science—such as Gonthier's formalizations of the Four-Color and Odd Order Theorems [30, 31], the Flyspeck verification of the Kepler conjecture by Hales et al. [33], and Forster, Kunze, and Roth's mechanized computability theory [29]—every definition, compiler stage, finite $S$-algebra, and theorem in Sections 2–8 has been formalized and kernel-checked in Lean 4 (version 4.33.1), unified in the master module `s_challenge_master_headline.lean` across its transitive dependency graph of $153$ self-contained formal modules without external library dependencies. In this closing section we document the logical axiom footprint, kernel-reduction engineering, and cross-language verification architecture that connect the human-readable proofs of this monograph to the formal artifacts.

### 9.1. Axiom Footprint and Constructive Elimination of Non-Constructive Principles

In Lean 4's Calculus of Inductive Constructions, standard library reasoning may invoke three foundational axioms: propositional extensionality (`propext`), quotient soundness (`Quot.sound`, used internally by Lean's linear arithmetic decision procedure `omega` on `Nat` and `Int`), and Hilbert's choice principle (`Classical.choice`). Across the entire formalization—verified programmatically via `#print axioms` in `adversarial_referee_audit/axiom_deep_audit.lean`—there are no occurrences of `sorry`, `admit`, user-declared `axiom`s, `partial`, `unsafe`, or `extern` declarations, and every exported theorem in `SChallengeMaster` depends solely on a subset of `[propext, Quot.sound]`, without relying on `Classical.choice`.

Achieving `Classical.choice`-free proofs for infinitary rewriting properties required replacing three classical idioms standard in paper rewriting theory by explicit constructive witnesses:

1. *Eliminating König's lemma in normalization and solvability:* Classical local-termination proofs [24] infer termination from absence of infinite paths in finitely branching trees via König's lemma. We replaced this in Section 6.1 by the rank-$6$ canonical normalizer $\mathrm{app}_{\mathcal{N}}$ (`FormalAlgebra.waldmann_theorem_9`), in Section 6.2 by the $(A, B)$ integer potential $\mu_{\mathrm{HN}}$ decreasing by at least $2$ per head step (`FormalAlgebra.barendregt_open_problem_10`), and in Section 6.3 by well-founded recursion (`Acc.rec`) on $\nu_{\mathrm{HN}}$ and right-spine strata (`FormalTopTermination.waldmann_theorem_29_top_termination`).
2. *Constructive $\bot$-extraction for Böhm-tree productivity:* On closed $S$-terms, productivity $\mathrm{Prod}(M) \equiv \forall d,\, \neg\bot_d(M)$ is a $\Pi_1^0$ predicate whose classical negation $\neg\mathrm{Prod}(M) \implies \exists d,\, \bot_d(M)$ is Markov's principle. In `FormalQ5Final.q5_completeness`, parity-stratified induction over the $113$-state joint algebra $\mathrm{PH}$ at maximum rank $17$ constructs an explicit depth $d \in \mathbb{N}$ witnessing $\bot_d(M)$ whenever $\llbracket M \rrbracket_P = \infty_P$, yielding the constructive disjunction $\mathrm{Prod}(M) \vee \exists d,\, \bot_d(M)$ (`productive_or_hasBot_closed`).
3. *Step-indexed deterministic traces:* In the universal Turing machine and Cyclic Tag System simulations (`constructive_fixed_u_to_s_halting`, `FormalProgramFree.program_free_cts_halting_iff_automaton`), existential step witnesses are carried by explicit fuel-indexed evaluators (`uRun`, `InvokeTrace`, `pfIter`), avoiding non-constructive witness extraction from transitive closures.

### 9.2. Kernel Reduction Without `native_decide`

Lean 4 provides a tactic `native_decide` that compiles decidable propositions to native machine code, adding the compiler and runtime to the trusted computing base. To keep the trusted computing base strictly confined to Lean 4's small logical kernel, every finite algebraic verification reduces directly inside the kernel's definitional equality checker (`rfl` / `decide`), making no appeal to `native_decide`.

Checking $39^3 = 59{,}319$ $S$-law triples for $\mathcal{A}_{\mathrm{SN}}$ and $\mathcal{A}_P$, $42{,}875$ triples for $\mathcal{A}_{\mathrm{HN}}$, and the $5{,}072$ critical-pair and $10{,}067$ joint-transition rank entries in Question 5 inside Lean's kernel without stack overflow or quadratic pattern-compilation overhead uses two standard reflection techniques [30]:

1. *Balanced binary tree quantifiers and row factoring:* Universal quantification over finite inductive state types ($35$ to $39$ constructors) is expressed as balanced depth-$6$ Boolean conjunction trees (`checkAll1`, `checkAll2`) accompanied by projection soundness lemmas, and three-variable checks $(x, y, z) \in Q^3$ are factored into $|Q|$ separate two-variable row theorems (`s_row_0`, …, `s_row_38`) each proved by `rfl`.
2. *Depth-$7$ binary Patricia lookup trees (`PTree`):* In `formal_q5_final/ph_tables.lean` and `q5_completeness.lean`, transition matrices and rank tables over the $113$-state joint algebra $\mathrm{PH}$ are stored as balanced binary trees of depth $7$, reducing every state-pair or rank lookup in $7$ pointer steps rather than $113$ sequential linear comparisons.

Similarly, for the root-restarted finite-state tree-walking zipper controller `invoke` (`formal_controller/finite_tree_walker.lean`), whose nested control type `Control` has cardinality $4{,}376{,}490{,}905$, finiteness is proved symbolically via product-list membership (`mem_allControls`: $\forall c,\, c \in \mathrm{allControls}$) without ever materializing a four-billion-element list in memory.

### 9.3. Syntax Bijections and Cross-Language Parity

Because the formal modules were developed in modular namespaces (`FormalAlgebra`, `FormalTopTermination`, `IntrinsicTheorems`, `Q5SNStratifiedGame`, `FormalQ5Final`, `ZeroNavigatorFixedOrder`, `ZeroNavigatorMultiway`, `ZeroNavigatorCellular`, `FormalWolfram12`, `FormalMinimality`, and `FormalAsymptotics`), the master file `s_challenge_master_headline.lean` defines explicit recursive syntax translations (`toAlgebraTerm`, `ofAlgebraTerm`, …) and proves bidirectional round-trip identities together with closedness preservation and one-step rewrite equivalence ($\mathrm{Step}\;M\;N \iff \mathrm{Step}_{\text{mod}}(\tau(M), \tau(N))$) across all subsystems. Thus no discrepancy in associativity, variable indexing, or redex semantics can arise between modules.

In parallel with the Lean 4 development, all compilers, selectors, halting automata, finite $S$-algebras, Rule 110 normal-form iterators, benchmark classifications, and Catalan generating-function constants are implemented in the standalone Wolfram Language package `PureSUniversality.wl` (accompanied by the automated test script `VerifyPureSUniversality.wls`) and an independent $18$-check Python verification script (`verify_all_theorems.py` and `cross_validate_wl.py`). Automated comparison confirms exact entry-by-entry agreement across all shared transition matrices ($\mathcal{A}_{\mathrm{SN}}, \mathcal{A}_{\mathrm{HN}}, \mathcal{A}_P, \mathcal{A}_{36}, \mathcal{D}_4, \mathcal{B}_Z$, and the $11$-state halting automaton $\mathcal{H}_{11}$), the $32$-rule $U_{3,11}$ table and its $132$-state, $262$-rule binary compilation, initial compiled leaf counts ($1{,}996{,}921$ leaves on the minimal $1$-state halting machine and $7{,}477{,}337$ leaves on the $2$-state write-$1$ machine), $912$-contraction execution of the $2$-state Busy Beaver, and $130$-digit dynamic programming verification of the Catalan phase transitions through $n = 150$.

## Appendix A. Concordance of Mathematical Results and Formal Artifacts

Table 8 maps the principal theorems and propositions of Sections 2–8 to their corresponding Lean 4 source files, kernel-verified declaration identifiers, exact foundational axiom footprints reported by `#print axioms` (where $\emptyset$ denotes no axioms, $\mathsf{P}$ denotes `[propext]`, and $\mathsf{PQ}$ denotes `[propext, Quot.sound]`), and exported Wolfram Language symbols in `PureSUniversality.wl`.

**Table 8.** Concordance between monograph results (Sections 2–8), Lean 4 declarations, axiom footprints, and Wolfram Language symbols.

| Monograph Result | Lean 4 Module Path | Lean 4 Declaration Identifier | Axioms | Wolfram Language Symbol |
| :— | :— | :— | :—: | :— |
| Prop. 2.2, 2.3: CR & order $\le 3$ | `formal_algebra/s_structural_laws.lean` | `FormalAlgebra.church_rosser`, `visser_van_oostrom_order_le_3` | $\mathsf{P}$ | — |
| Prop. 3.3: $M(w) \leftrightarrow U_{3,11}$ sim. | `formal_utm/neary_u311_sim.lean`, `neary_encoder.lean` | `source_halts_iff_u_stops`, `encodeSourceInstance_poly_bound` | $\mathsf{PQ}$ | `EncodeNearyU311` |
| Prop. 3.8: $11$-state halt DTA $\mathcal{H}_{11}$ | `formal_controller/halt_tree_automaton.lean` | `haltAutomaton_accepts_eq_rootHalt` | $\mathsf{P}$ | `PureSHaltDetectorQ` |
| Thm. 3.9: Root-restarted UTM | `formal_controller/constructive_endpoint.lean`, `bare_output_and_invoke_trace.lean` | `constructive_fixed_u_to_s_halting`, `decodeBareSTermOutput_correct` | $\mathsf{PQ}$ | `CompileTuringMachineToPureS` |
| Lem. 3.7: Zipper walker bound | `formal_controller/bare_output_and_invoke_trace.lean` | `exists_microtick_le_node_bound` | $\mathsf{PQ}$ | `RootRestartedSelectAddress` |
| Prop. 4.4: Seed genesis $D_{\mathrm{seed}} \to_S^* t_0$ | `formal_program_free/program_free_cts.lean` | `FormalProgramFree.seed_reduces_to_encodeProgramFreeCTS` | $\mathsf{PQ}$ | `EncodeProgramFreeCTS` |
| Thm. 4.5: Program-free CTS univ. | `formal_program_free/program_free_cts.lean` | `FormalProgramFree.program_free_cts_halting_iff_automaton` | $\mathsf{PQ}$ | `ProgramFreePureSSelect` |
| Thm. 5.2: Unary leaf-split univ. | `formal_algebra/trivial_rule_separation.lean` | `FormalAlgebra.TrivialRuleSeparation.fixed_universal_trivial_rule_separation` | $\mathsf{PQ}$ | — |
| Prop. 5.4: $7$/$5$-step shortcuts | `zero_navigator_multiway/multiway_and_q30_theorems.lean` | `ZeroNavigatorMultiway.protected_trie_nonhalting_shortcut_7steps` | $\mathsf{P}$ | — |
| Thm. 5.5: No pure-$S$ Church gate | `zero_navigator_multiway/multiway_and_q30_theorems.lean` | `ZeroNavigatorMultiway.no_church_boolean_pair_in_pure_s` | $\mathsf{P}$ | — |
| Lem. 6.1: $\mathrm{WN} \iff \mathrm{SN}$ | `formal_algebra/s_structural_laws.lean` | `FormalAlgebra.wn_implies_sn` | $\emptyset$ | — |
| Thm. 6.2: $39$-state $\mathcal{A}_{\mathrm{SN}}$ | `formal_algebra/sn_hn_algebras.lean` | `FormalAlgebra.waldmann_theorem_9` | $\mathsf{P}$ | `EvalSNState` |
| Lem. 6.4: $3$-var head law | `zero_navigator_fixed_order/zero_nav_fixed_theorems.lean` | `ZeroNavigatorFixedOrder.three_var_hnf_head_in_xy` | $\mathsf{P}$ | — |
| Thm. 6.6(i): Question 10 ($\mathcal{A}_{\mathrm{HN}}$) | `formal_algebra/sn_hn_algebras.lean` | `FormalAlgebra.barendregt_open_problem_10` | $\mathsf{P}$ | `EvalHNState` |
| Thm. 6.6(ii–iv): Footnote 4 & ceiling | `formal_algebra/sn_hn_algebras.lean` | `FormalAlgebra.footnote4_rnf_iff`, `five_composite_args_rnf` | $\mathsf{P}$ | `IsRootNormalFormQ` |
| Thm. 6.7: Top-termination | `formal_top_termination/top_termination.lean` | `FormalTopTermination.waldmann_theorem_29_top_termination` | $\mathsf{PQ}$ | — |
| Lem. 6.8: Left/Right $\bot$ laws | `q5_sn_stratified_game/sn_stratified_game.lean` | `Q5SNStratifiedGame.hasBotWithin_app_left`, `_right` | $\mathsf{P}$ | — |
| Lem. 6.9: $(G_m G_n)U \notin \mathrm{Prod}$ | `formal_q5_final/pval_system.lean` | `FormalQ5Final.hasBot_zachos_app` | $\mathsf{P}$ | — |
| Prop. 6.10: $34$-of-$38$ $\mathrm{SN}$ strat. | `q5_sn_stratified_game/sn_stratified_game.lean` | `Q5SNStratifiedGame.unique_nonSN_productive_root_redex_state` | $\mathsf{P}$ | `EvalProductivityState` |
| Thm. 6.12: Question 5 ($\mathcal{A}_P$) | `formal_q5_final/q5_completeness.lean` | `FormalQ5Final.barendregt_open_question_5` | $\mathsf{PQ}$ | `IsProductivePureSQ` |
| Prop. 6.13: $8$-leaf $L_{\mathrm{loop}}$ game | `q5_sn_stratified_game/sn_stratified_game.lean` | `Q5SNStratifiedGame.bohm_game_asymmetry_size8` | $\mathsf{P}$ | — |
| Thm. 6.14: Question 7 & $\{q_1,q_8\}$ | `formal_algebra/question7_flipflop.lean` | `FormalAlgebra.barendregt_question_7_solution` | $\mathsf{P}$ | `Question7FlipFlopTerm` |
| Thm. 6.15: Question 31 ($\mathcal{A}_{36}$) | `intrinsic_research/intrinsic_theorems.lean` | `IntrinsicTheorems.aaa_not_conv_aaas` | $\mathsf{P}$ | `EvalQuestion31State` |
| Prop. 6.16: Question 30 & $\mathrm{gk}$ | `zero_navigator_multiway/multiway_and_q30_theorems.lean` | `ZeroNavigatorMultiway.decideConvClosedSN` | $\mathsf{PQ}$ | — |
| Prop. 7.1: $6$ strategies & $\mathcal{B}_Z$ | `zero_navigator_fixed_order/zero_nav_fixed_theorems.lean` | `ZeroNavigatorFixedOrder.zachos_unified_quadratic_trace` | $\mathsf{PQ}$ | `EvalBZachosState` |
| Thm. 7.2: $5$-step Case-$3$ ceiling | `zero_navigator_fixed_order/zero_nav_fixed_theorems.lean` | `ZeroNavigatorFixedOrder.no_six_consecutive_case3_li` | $\mathsf{PQ}$ | — |
| Thm. 7.3: Clone barrier & Rule 110 | `zero_navigator_cellular/cellular_and_clones.lean` | `ZeroNavigatorCellular.no_rule110_SN`, `dnand_rule110_correct` | $\mathsf{PQ}$ | `PureSRule110Term` |
| Thm. 8.1: $14$ benchmarks | `formal_wolfram12/wolfram_12_benchmarks.lean` | `FormalWolfram12.wolfram_14_dichotomy_master` | $\mathsf{P}$ | `WolframChallenge12Benchmarks` |
| Prop. 8.2: Jump-ahead laws | `formal_wolfram12/wolfram_12_benchmarks.lean` | `FormalWolfram12.decideContextHalts_exact`, `jump_ahead_sPrefix_exact` | $\mathsf{P}$ | `PureSJumpAheadOutcome` |
| Thm. 8.3: $n \le 9$ minimality | `formal_census_and_minimality/minimality_theorems.lean` | `FormalMinimality.theorem_A_universal_sn_le_6`–`theorem_F_confluence_and_diamond_thresholds` | $\mathsf{PQ}$ | `PureSCatalanPhaseCensus` |
| Thm. 8.4: Catalan asymptotics | `formal_asymptotics/asymptotic_laws.lean` | `FormalAsymptotics.sn_and_acceptP_exponential_decay_to_zero` | $\mathsf{PQ}$ | `PureSAsymptoticConstants` |

## References

1. Henk P. Barendregt, *The Lambda Calculus: Its Syntax and Semantics*, Revised edition, Studies in Logic and the Foundations of Mathematics, vol. 103, North-Holland, Amsterdam, 1984.
2. Henk P. Barendregt, Jan A. Bergstra, Jan Willem Klop, and Henri Volken, *Degrees, Reductions and Representability in the Lambda Calculus*, Preprint No. 22, Department of Mathematics, Utrecht University, 1976.
3. Henk P. Barendregt, Wil Dekkers, and Richard Statman, *Lambda Calculus with Types*, Perspectives in Logic, Cambridge University Press, Cambridge, 2013, `doi:10.1017/CBO9781139032636`.
4. Henk P. Barendregt, Jörg Endrullis, Jan Willem Klop, and Johannes Waldmann, “Dance of the Starlings,” in Melvin Fitting and Brian Rayman (eds.), *Raymond Smullyan on Self Reference*, Outstanding Contributions to Logic, vol. 14, Springer, Cham, 2017, pp. 67–111, `doi:10.1007/978-3-319-68732-2_5`.
5. Maciej Bendkowski, Katarzyna Grygiel, Pierre Lescanne, and Marek Zaionc, “Combinatorics of $\lambda$-terms: a natural approach,” *Journal of Logic and Computation* **27** (2017), no. 8, 2611–2630, `doi:10.1093/logcom/exx018`.
6. Maciej Bendkowski, Katarzyna Grygiel, and Marek Zaionc, “Asymptotic properties of combinatory logic,” in *Theory and Applications of Models of Computation (TAMC 2015)*, Lecture Notes in Computer Science, vol. 9076, Springer, Cham, 2015, pp. 62–72, `doi:10.1007/978-3-319-17142-5_7`.
7. Maciej Bendkowski, Katarzyna Grygiel, and Marek Zaionc, “On the likelihood of normalisation in combinatory logic,” *Journal of Logic and Computation* **27** (2017), no. 7, 2251–2269, `doi:10.1093/logcom/exx005`.
8. Alessandro Berarducci, “Infinite $\lambda$-calculus and non-sensible models,” in Aldo Ursini and Paolo Aglianò (eds.), *Logic and Algebra*, Lecture Notes in Pure and Applied Mathematics, vol. 180, Marcel Dekker, New York, 1996, pp. 339–377, `doi:10.1201/9780203748671-17`.
9. Alessandro Berarducci and Corrado Böhm, “A self-interpreter of lambda calculus having a normal form,” in *Computer Science Logic (CSL '92)*, Lecture Notes in Computer Science, vol. 702, Springer, Berlin, 1993, pp. 85–99, `doi:10.1007/3-540-57182-5_7`.
10. Olivier Bodini, Danièle Gardy, and Bernhard Gittenberger, “Lambda-terms of bounded unary height,” in *Proceedings of the Eighth Workshop on Analytic Algorithmics and Combinatorics (ANALCO 2011)*, SIAM, 2011, pp. 23–32, `doi:10.1137/1.9781611973013.3`.
11. Olivier Bodini, Danièle Gardy, Bernhard Gittenberger, and Alice Jacquot, “Enumeration of generalized $BCI$ lambda-terms,” *The Electronic Journal of Combinatorics* **20** (2013), no. 4, Paper P30, `doi:10.37236/3051`.
12. Mikołaj Bojańczyk and Thomas Colcombet, “Tree-walking automata do not recognize all regular languages,” *SIAM Journal on Computing* **38** (2008), no. 2, 658–701, `doi:10.1137/050645427`.
13. Corrado Böhm, “Alcune proprietà delle forme $\beta$-$\eta$-normali nel $\lambda$-$K$-calcolo,” Pubblicazioni dell'Istituto per le Applicazioni del Calcolo, no. 696, Rome, 1968, pp. 1–19.
14. Richard Canal, “Complexité de la réduction en logique combinatoire,” *RAIRO – Informatique théorique* **12** (1978), no. 4, 339–367, `doi:10.1051/ita/1978120403391`.
15. Panagiotis Cheilaris, John Ramirez, and Stathis Zachos, “Checking in linear time if an $S$-term normalizes,” in *8th Panhellenic Logic Symposium*, Ioannina, Greece, July 2011.
16. John Cocke and Marvin L. Minsky, “Universality of tag systems with $P = 2$,” *Journal of the ACM* **11** (1964), no. 1, 15–20, `doi:10.1145/321203.321206`.
17. Matthew Cook, “Universality in elementary cellular automata,” *Complex Systems* **15** (2004), no. 1, 1–40, `doi:10.25088/ComplexSystems.15.1.1`.
18. Haskell B. Curry, “Grundlagen der kombinatorischen Logik,” *American Journal of Mathematics* **52** (1930), no. 3–4, 509–536, 789–834, `doi:10.2307/2370619`.
19. Haskell B. Curry and Robert Feys, *Combinatory Logic, Volume I*, Studies in Logic and the Foundations of Mathematics, North-Holland, Amsterdam, 1958.
20. René David, Katarzyna Grygiel, Jakub Kozik, Christophe Raffalli, Guillaume Theyssier, and Marek Zaionc, “Asymptotically almost all $\lambda$-terms are strongly normalizing,” *Logical Methods in Computer Science* **9** (2013), no. 1:2, 1–30, `doi:10.2168/LMCS-9(1:2)2013`.
21. Martin Davis, “A note on universal Turing machines,” in Claude E. Shannon and John McCarthy (eds.), *Automata Studies*, Annals of Mathematics Studies, vol. 34, Princeton University Press, Princeton, NJ, 1956, pp. 167–175.
22. Martin Davis, “The definition of universal Turing machine,” *Proceedings of the American Mathematical Society* **8** (1957), no. 6, 1125–1126, `doi:10.1090/S0002-9939-1957-0095781-8`.
23. Michael Drmota, “Systems of functional equations,” *Random Structures & Algorithms* **10** (1997), no. 1–2, 103–124, `doi:10.1002/(SICI)1098-2418(199701/03)10:1/2<103::AID-RSA5>3.0.CO;2-Z`.
24. Jörg Endrullis, Roel C. de Vrijer, and Johannes Waldmann, “Local termination: theory and practice,” *Logical Methods in Computer Science* **6** (2010), no. 3:20, 1–37, `doi:10.2168/LMCS-6(3:20)2010`.
25. Jörg Endrullis, Clemens Grabmayer, Dimitri Hendriks, Ariya Isihara, and Jan Willem Klop, “Productivity of stream definitions,” *Theoretical Computer Science* **411** (2010), no. 4–5, 765–782, `doi:10.1016/j.tcs.2009.10.014`.
26. Alexander Filin, *Pure S Is Computationally Universal Under a Fixed Root-Restarted Finite Controller*, Technical manuscript, Predictive Universe Project, September 14, 2026.
27. Patrick C. Fischer, “On formalisms for Turing machines,” *Journal of the ACM* **12** (1965), no. 4, 570–580, `doi:10.1145/321296.321308`.
28. Philippe Flajolet and Robert Sedgewick, *Analytic Combinatorics*, Cambridge University Press, Cambridge, 2009, `doi:10.1017/CBO9780511801655`.
29. Yannick Forster, Fabian Kunze, and Marc Roth, “The weak call-by-value $\lambda$-calculus is reasonable for both time and space,” *Proceedings of the ACM on Programming Languages* **4** (POPL, 2020), Article 27, 27:1–27:23, `doi:10.1145/3371095`.
30. Georges Gonthier, “Formal proof—the Four-Color Theorem,” *Notices of the American Mathematical Society* **55** (2008), no. 11, 1382–1393.
31. Georges Gonthier, Andrea Asperti, Jeremy Avigad, Yves Bertot, Cyril Cohen, François Garillot, Stéphane Le Roux, Assia Mahboubi, Russell O'Connor, Sidi Ould Biha, Ioana Pasca, Laurence Rideau, Alexey Solovyev, Enrico Tassi, and Laurent Théry, “A machine-checked proof of the Odd Order Theorem,” in *Interactive Theorem Proving (ITP 2013)*, Lecture Notes in Computer Science, vol. 7998, Springer, Berlin, 2013, pp. 163–179, `doi:10.1007/978-3-642-39634-2_14`.
32. Katarzyna Grygiel and Pierre Lescanne, “Counting and generating lambda terms,” *Journal of Functional Programming* **23** (2013), no. 5, 594–628, `doi:10.1017/S0956796813000157`.
33. Thomas Hales, Mark Adams, Gertrud Bauer, Tat Dat Dang, John Harrison, Le Truong Hoang, Cezary Kaliszyk, Victor Magron, Sean McLaughlin, Tat Thang Nguyen, Quang Truong Nguyen, Tobias Nipkow, Steven Obua, Joseph Pleso, Jason Rute, Alexey Solovyev, Ta Thi Hoai An, Tran Nam Trung, Thi Diep Trieu, Josef Urban, Ky Vu, and Roland Zumkeller, “A formal proof of the Kepler conjecture,” *Forum of Mathematics, Pi* **5** (2017), e2, 1–29, `doi:10.1017/fmp.2017.1`.
34. Gabor T. Herman, “Simulation of one abstract computing machine by another,” *Communications of the ACM* **11** (1968), no. 12, 802, 813, `doi:10.1145/364175.364181`.
35. J. Roger Hindley and Jonathan P. Seldin, *Lambda-Calculus and Combinators: An Introduction*, 2nd edition, Cambridge University Press, Cambridge, 2008, `doi:10.1017/CBO9780511809835`.
36. Gérard Huet, “The Zipper,” *Journal of Functional Programming* **7** (1997), no. 5, 549–554, `doi:10.1017/S0956796897002864`.
37. Jan Willem Klop, Vincent van Oostrom, and Femke van Raamsdonk, “Reduction strategies and acyclicity,” in *Rewriting, Computation and Proof*, Lecture Notes in Computer Science, vol. 4600, Springer, Berlin, 2007, pp. 89–112, `doi:10.1007/978-3-540-73147-4_5`.
38. Manfred Kudlek and Yurii Rogozhin, “A universal Turing machine with $3$ states and $9$ symbols,” in *Developments in Language Theory (DLT 2001)*, Lecture Notes in Computer Science, vol. 2295, Springer, Berlin, 2002, pp. 311–318, `doi:10.1007/3-540-46011-X_25`.
39. Martin Kutrib and Uwe Meyer, “Deterministic real-time tree-walking-storage automata,” in *Proceedings of the 13th International Workshop on Non-Classical Models of Automata and Applications (NCMA 2023)*, Electronic Proceedings in Theoretical Computer Science (EPTCS), vol. 388, 2023, pp. 48–62, `doi:10.4204/EPTCS.388.6`.
40. Martin Kutrib and Uwe Meyer, “Deterministic tree-walking-storage automata,” *Acta Informatica* **63** (2026), no. 1, Article 9, `doi:10.1007/s00236-026-00522-5`.
41. Marvin L. Minsky, “Recursive unsolvability of Post's problem of `Tag' and other topics in theory of Turing machines,” *Annals of Mathematics* (2) **74** (1961), no. 3, 437–455, `doi:10.2307/1970290`.
42. Marvin L. Minsky, *Computation: Finite and Infinite Machines*, Prentice-Hall, Englewood Cliffs, NJ, 1967.
43. Turlough Neary, *Small Universal Turing Machines*, Ph.D. thesis, Department of Computer Science, National University of Ireland, Maynooth, October 2008.
44. Turlough Neary and Damien Woods, “Small fast universal Turing machines,” *Theoretical Computer Science* **362** (2006), no. 1–3, 171–195, `doi:10.1016/j.tcs.2006.06.002`.
45. Turlough Neary and Damien Woods, “$\mathrm{P}$-completeness of cellular automaton Rule 110,” in *Automata, Languages and Programming (ICALP 2006), Part I*, Lecture Notes in Computer Science, vol. 4051, Springer, Berlin, 2006, pp. 132–143, `doi:10.1007/11786986_13`.
46. Rohit J. Parikh, “On context-free languages,” *Journal of the ACM* **13** (1966), no. 4, 570–581, `doi:10.1145/321356.321364`.
47. Emil L. Post, “Finite combinatory processes—Formulation 1,” *The Journal of Symbolic Logic* **1** (1936), no. 3, 103–105, `doi:10.2307/2269031`.
48. Emil L. Post, *The Two-Valued Iterative Systems of Mathematical Logic*, Annals of Mathematics Studies, no. 5, Princeton University Press, Princeton, NJ, 1941.
49. Emil L. Post, “Formal reductions of the general combinatorial decision problem,” *American Journal of Mathematics* **65** (1943), no. 2, 197–215, `doi:10.2307/2371809`.
50. Lutz Priese, “Towards a precise characterization of the complexity of universal and nonuniversal Turing machines,” *SIAM Journal on Computing* **8** (1979), no. 4, 508–523, `doi:10.1137/0208039`.
51. Yurii Rogozhin, “Small universal Turing machines,” *Theoretical Computer Science* **168** (1996), no. 2, 215–240, `doi:10.1016/S0304-3975(96)00077-1`.
52. Yurii Rogozhin, “A universal Turing machine with $22$ states and $2$ symbols,” *Romanian Journal of Information Science and Technology* **1** (1998), no. 3, 259–265.
53. Moses Schönfinkel, “Über die Bausteine der mathematischen Logik,” *Mathematische Annalen* **92** (1924), no. 3–4, 305–316, `doi:10.1007/BF01448013`.
54. Dana S. Scott, “Open problem,” in Corrado Böhm (ed.), *$\lambda$-Calculus and Computer Science Theory*, Lecture Notes in Computer Science, vol. 37, Springer, Berlin, 1975, p. 368.
55. Alex Smith, “Universality of Wolfram's $2, 3$ Turing machine,” *Complex Systems* **29** (2020), no. 1, 1–44, `doi:10.25088/ComplexSystems.29.1.1`.
56. Richard Statman, “On translating lambda terms into combinators; the basis problem,” in *Proceedings of the First Annual IEEE Symposium on Logic in Computer Science (LICS 1986)*, IEEE Computer Society Press, 1986, pp. 378–382.
57. Richard Statman, “The word problem for Smullyan's lark combinator is decidable,” *Journal of Symbolic Computation* **7** (1989), no. 2, 103–112, `doi:10.1016/S0747-7171(89)80044-6`.
58. Masako Takahashi, “Parallel reductions in $\lambda$-calculus,” *Information and Computation* **118** (1995), no. 1, 120–127, `doi:10.1006/inco.1995.1057`.
59. TeReSe, *Term Rewriting Systems*, Cambridge Tracts in Theoretical Computer Science, vol. 55, Cambridge University Press, Cambridge, 2003.
60. Alan M. Turing, “On computable numbers, with an application to the Entscheidungsproblem,” *Proceedings of the London Mathematical Society* (2) **42** (1937), 230–265, `doi:10.1112/plms/s2-42.1.230`; correction, ibid. **43** (1937), 544–546.
61. Peter van Emde Boas, “Machine models and simulations,” in Jan van Leeuwen (ed.), *Handbook of Theoretical Computer Science, Volume A: Algorithms and Complexity*, Elsevier / MIT Press, 1990, pp. 1–66.
62. Johannes Waldmann, *Nimm Zwei*, Technical Report IR-432, Vrije Universiteit Amsterdam, 1997.
63. Johannes Waldmann, “Normalization of $S$-terms is decidable,” in Tobias Nipkow (ed.), *Rewriting Techniques and Applications (RTA '98)*, Lecture Notes in Computer Science, vol. 1379, Springer, Berlin, 1998, pp. 138–150, `doi:10.1007/BFb0052367`.
64. Johannes Waldmann, *The Combinator S*, Ph.D. thesis, Fakultät für Mathematik und Informatik, Friedrich-Schiller-Universität Jena, 1998.
65. Johannes Waldmann, “The combinator $S$,” *Information and Computation* **159** (2000), no. 1–2, 2–21, `doi:10.1006/inco.2000.2874`.
66. Shigeru Watanabe, “$5$-symbol $8$-state and $5$-symbol $6$-state universal Turing machines,” *Journal of the ACM* **8** (1961), no. 4, 476–483, `doi:10.1145/321088.321090`.
67. Stephen Wolfram, *A New Kind of Science*, Wolfram Media, Champaign, IL, 2002.
68. Stephen Wolfram, “The prize is won; the simplest universal Turing machine is proved,” *Stephen Wolfram Writings*, October 24, 2007, `https://writings.stephenwolfram.com/2007/10/the-prize-is-won-the-simplest-universal-turing-machine-is-proved/`.
69. Stephen Wolfram, “Combinators and the story of computation,” *Stephen Wolfram Writings*, December 2020, `arXiv:2102.09658`.
70. Stephen Wolfram, “1920, 2020 and a \$20,000 prize: announcing the $S$ Combinator Challenge,” *Stephen Wolfram Writings*, June 8, 2021, `doi:10.31855/7709b85c-8e6`, official rules at `https://www.combinatorprize.org/`.
71. Stephen Wolfram, *Combinators: A Centennial View*, Wolfram Media, Champaign, IL, 2021, `arXiv:2103.12811`.
72. Alan R. Woods, “Colouring rules for finite trees, and probabilities of monadic second order sentences,” *Random Structures & Algorithms* **13** (1998), no. 3–4, 307–334.
73. Damien Woods and Turlough Neary, “On the time complexity of $2$-tag systems and small universal Turing machines,” in *Proceedings of the 47th Annual IEEE Symposium on Foundations of Computer Science (FOCS 2006)*, IEEE, 2006, pp. 439–446, `doi:10.1109/FOCS.2006.57`.
74. Damien Woods and Turlough Neary, “The complexity of small universal Turing machines: a survey,” *Theoretical Computer Science* **410** (2009), no. 4–5, 443–450, `doi:10.1016/j.tcs.2008.09.051`.
75. Efstathios Zachos, *Kombinatorische Logik und S-Terme*, Dissertation ETH Nr. 6214 (Berichte des Instituts für Informatik, Nr. 26), Eidgenössische Technische Hochschule Zürich, 1978, `doi:10.3929/ethz-a-000136021`.
76. Hans Zantema, “Termination of term rewriting by semantic labelling,” *Fundamenta Informaticae* **24** (1995), no. 1–2, 89–105, `doi:10.3233/FI-1995-24124`.
