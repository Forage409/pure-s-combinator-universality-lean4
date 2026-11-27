# Computational Universality, Finite Tree Algebras, and Asymptotic Phase Transitions of the Pure $S$ Combinator

**Wolfram $S$ Combinator Challenge Submission**

## Abstract

Schönfinkel's combinator $S$, defined by $S x y z \to_S (x z)(y z)$, generates a non-erasing subsystem $\mathrm{CL}(S)$ of combinatory logic whose normalizing closed terms $\mathcal{T}_S \cap \mathrm{SN}$ form a regular tree language (Waldmann, 2000). Universal computation in $\mathrm{CL}(S)$ therefore requires sub-universal encoding, halting recognition, and output readback along non-terminating reductions (Wolfram, 2021).

We show that universality in $\mathrm{CL}(S)$ depends sharply on evaluation-order control. Under stateless root-restarted tree-walking selection, closed $S$-terms simulate Turing machines via $U_{3,11}$ in initial size $O((|Q|^2 + |w|)^2)$ with a minimal $11$-state halting automaton $\mathcal{H}_{11}$ and linear-time output readback; from a $10$-leaf seed $D_{\mathrm{seed}}$, program-free cyclic-tag simulation compresses to a two-pass $(25, 23, 136)$ pocket tree transducer halting in at most $2|M| - 1 + \mathrm{depth}(M)$ transitions per contraction. Conversely, root-restarted selection is already universal over $\mathsf{Leaf} \to \mathsf{Node}(\mathsf{Leaf},\mathsf{Leaf})$, whereas unrestricted reduction admits constant-step halting shortcuts and forbids asymmetric branch gating.

For unguided rewriting, we establish a $\Delta L = -2$ leaf-preserving conservation law and dependency-pair non-spiralling obstructions toward Conjecture 17; construct conversion-invariant finite $S$-algebras ($35, 39, 39, 36$ states), automaton-free proofs, and productive Böhm faithfulness resolving Questions 5, 7, 10, 30 (on $\mathrm{Prod} \times \mathcal{T}_S$), and 31 of Barendregt et al. (2017); and analyze the $\lambda\mathrm{I}$-translation, proving Conjecture 40, refuting Conjectures 42 and 43 at $14$ and $15$ leaves with a hereditary saturation repair, answering Question 32 negatively, and establishing single-constant collapse and congruence incomparability for Question 34. Finally, we derive all-step $\to_{\mathrm{lo}}$ cubic jump-ahead formulas, characterize Garden-of-Eden normal forms, and determine exact rational Catalan densities $c_{\mathrm{HN}} = 4\,429\,673/7\,077\,888$ and $(c_0, c_1, c_2, c_3) = (2\,648\,215/7\,077\,888,\, 1\,864\,553/7\,077\,888,\, 835/2\,304,\, 0)$. All results are constructively verified in Lean 4 and cross-checked in Wolfram Language.

*2020 Mathematics Subject Classification:* Primary 03B40, 68Q05; Secondary 68Q42, 05A16, 68V20  
*Keywords:* combinatory logic, $S$ combinator, $\lambda\mathrm{I}$-calculus, universal Turing machine, cyclic tag system, finite-state tree transducer, tree automaton, Böhm tree, productivity, analytic combinatorics, constructive formalization

---

## 1. Introduction

### 1.1. Historical Context and the Pure $S$ Problem

In a lecture delivered to the Göttingen Mathematical Society on December 7, 1920 and published in 1924, Moses Schönfinkel showed that bound variables can be eliminated from mathematical logic by reducing all operations to binary application and two primitive combinators: the cancellation operator $K$ (written $C$ by Schönfinkel), satisfying $K x y \to x$, and the fusion operator $S$, satisfying $S x y z \to (x z)(y z)$ [54]. Together with Haskell Curry's axiomatization [19, 20], the system $\mathrm{CL}(S,K)$ became one of the standard foundations of computability theory, matching the expressive power of Church's untyped $\lambda$-calculus and Turing machines [61, 1, 36].

In $\mathrm{CL}(S,K)$, computational universality relies simultaneously on duplication by $S$ and erasure by $K$. Restricting the basis to $S$ alone yields the subsystem $\mathrm{CL}(S)$, whose closed (or ground) terms $\mathcal{T}_S$ are finite full binary application trees with every leaf labeled $S$, rewritten under the contextual closure of

$$
S X Y Z \;\to_S\; (X Z)(Y Z). \tag{1.1}
$$

Because every argument $X, Y, Z$ reappears on the right-hand side of (1.1), the leaf count $|M|$ never decreases under reduction: $|(X Z)(Y Z)| - |S X Y Z| = |Z| - 1 \ge 0$. By Church's conservation principle for orthogonal non-erasing rewrite systems, weak normalization ($\mathrm{WN}$) and strong normalization ($\mathrm{SN}$) coincide on $\mathrm{CL}(S)$ [16, 76, 4]. For five decades after Schönfinkel's lecture, it was not even clear whether every closed $S$-term normalizes. That question was settled in the negative in the mid-1970s through Barendregt's $9$-leaf term $A A A$ (where $A \equiv S S S$), Duboué's two minimal $7$-leaf non-normalizing terms $X_1 \equiv S(S S)S S S S$ and $X_2 \equiv S S S(S S)S S$ [2, 1], and Zachos's $10$-leaf single-redex term $Z_{\mathrm{Zac}} \equiv S T T(S T T)$ (where $T \equiv S S$) [76].

Two decades later, Johannes Waldmann proved through an algebraic analysis of pure-$S$ rewriting that the set $\mathcal{T}_S \cap \mathrm{SN}$ of normalizing closed $S$-terms is a regular tree language, recognizable in linear time $O(|M|)$ by a finite tree automaton [63, 64, 65, 66] whose minimal deterministic bottom-up realization has $39$ states ($38$ accepting states and one absorbing sink) [25, 4]; see also Cheilaris, Ramirez, and Zachos [15] for a manual grammar derivation, and Barendregt, Dekkers, and Statman [3] for broader typed and combinatory decision boundaries. Waldmann's theorem immediately rules out direct normal-form universality in the classical sense of Davis [23]: if halting of a universal machine $U$ on input $w$ were encoded as normal-form reachability $\mathcal{E}(w) \in \mathrm{WN}$, any computable encoder $\mathcal{E}$ would compose with the $39$-state tree automaton to decide the halting problem.

Yet normalizing reductions represent an exponentially vanishing fraction of $\mathrm{CL}(S)$ dynamics [7], and non-normalizing $S$-terms display unbounded growth and tree-unfolding behavior [72]. In their survey *"Dance of the Starlings"*, Barendregt, Endrullis, Klop, and Waldmann [4] formulated a program of open problems and conjectures governing unguided $\mathrm{CL}(S)$ rewriting, Böhm-tree semantics, and the canonical translation of $\mathrm{CL}(S)$ into Church's $\lambda\mathrm{I}$-calculus [16]. On June 8, 2021, commemorating the centenary of Schönfinkel's lecture [70, 72], Stephen Wolfram posed *The Wolfram $S$ Combinator Challenge*, asking whether $\mathrm{CL}(S)$ can support universal computation along non-terminating evolutions [71]. Following the ongoing-computation framework established by Priese [51] and employed in the universality proofs for elementary cellular automaton Rule 110 by Cook [18] and for the $(2,3)$ Turing machine prize by Smith [56, 69], Wolfram formulated ongoing pure-$S$ computation via an encoder $\mathcal{E}$, a halting detector $\mathcal{H}$, and an output decoder $\mathcal{D}$, each required to operate within strict sub-universal resource bounds so that no universal simulation occurs outside $\mathrm{CL}(S)$ itself [71, 62]. Wolfram also observed that once reductions do not terminate in a unique normal form, confluence no longer collapses distinct evaluation orders: computational behavior depends on whether one considers fixed canonical strategies (such as normal-order reduction $\to_{\mathrm{lo}}$), unrestricted multiway conversion $=_S$, or a specified single-step selection discipline.

### 1.2. Computation Regimes and Summary of Main Results

The central thesis of this monograph is that the computational power and semantic decidability of $\mathrm{CL}(S)$ admit an exact classification governed by the locus of evaluation-order control and binder discipline. Instead of treating "universality of $S$" as an undifferentiated yes-or-no predicate, we analyze all six operational and translational regimes posed in [71, 4] within a single mathematical and mechanized framework. Table 1 summarizes the resulting taxonomy.

**Table 1.** Taxonomy of computational regimes and decidability boundaries in $\mathrm{CL}(S)$.

| Regime | Step relation | Halting / event problem | Expressive / algebraic law | Reference |
| :--- | :--- | :--- | :--- | :--- |
| Normal-form halting | $M \to_S^* N \in \mathrm{NF}$ | Regular ($39$-state $\mathcal{A}_{\mathrm{SN}}$) | Subcritical ($\gamma_{\mathrm{SN}} \approx 3.36992$); $\Delta L = -2$ | Thms. 2.3, 6.2, 9.10 |
| Canonical fixed order | $\to_h, \to_{\mathrm{lo}}, \to_{\mathrm{li}}$ | $\mathrm{HN}$ ($35$), $\mathrm{Prod}$ ($39$) regular | Cubic $\to_{\mathrm{lo}}$ jump; monotone clones | Thms. 6.8, 6.14, 8.3, 9.4 |
| Unrestricted multiway | $M \to_S^* N$, $M =_S N$ | $\to_S^*$ decidable; $=_S$ on $\mathrm{Prod} \times \mathcal{T}_S$ | $7$/$5$-step shortcuts; no branch gate | Prop. 5.4, Thms. 5.5, 6.21 |
| Root-restarted walker | $T_{k+1} = \sigma_{\mathrm{TM}}(T_k)$ | $\Sigma_1^0$-complete ($11$-state $\mathcal{H}_{11}$) | $O((\vert Q\vert^2+\vert w\vert)^2)$; sep. by $\to_{\mathrm{sp}}$ | Thms. 3.9, 5.2 |
| Program-free walker | $T_{k+1} = \sigma_{\mathrm{CTS}}(T_k)$ | $\Sigma_1^0$-complete ($11$-state $\mathcal{H}_{11}$) | $(25,23,136)$ $\mathcal{T}_{\mathrm{pocket}}$; $D_{\mathrm{seed}}$ genesis | Prop. 4.4, Thms. 4.5, 4.7 |
| $\lambda\mathrm{I}$-translation | $(M)_\lambda, \to_\beta^*, =_\beta$ | Conjecture 40 true; 42, 43, Q32 false | Single-constant Q34; $\infty_{34}$ sink | Thms. 7.3, 7.5, 7.9 |

Our contributions span five interconnected directions.

Sections 3 and 4 establish compact, polynomial-size universal simulations in $\mathrm{CL}(S)$ under stateless root-restarted finite-state selection. In an instructive recent development, Filin [27] demonstrated selected-path universality of $\mathrm{CL}(S)$ under a root-restarted finite controller by compiling Boolean-tape Turing machines through three-counter and $2$-tag systems [17, 43] to Rogozhin's $(4,6)$ universal Turing machine [52] and Cook's $912$-phase cyclic tag system [18]; because unary counter encoding incurs iterated exponential blowup, every source instance in that padded pipeline produces at least $8^{19069} = 2^{57207}$ seed bits before $114$-fold tag expansion, and source output recovery requires an $O(|T|^4)$ parser consulting the retained seed. In Section 3, we bypass tag systems altogether by compiling boundary-safe normalized binary Turing machines directly to Neary and Woods's quadratic-time $3$-state, $11$-symbol universal machine $U_{3,11}$ [45, 44] and its $132$-state, $262$-rule binary specialization $U_{\mathrm{bin}}$. Theorem 3.9 establishes that the resulting pure-$S$ compiler $\mathcal{E}_{\mathrm{TM}}(M,w)$ produces a closed $S$-term of quartic leaf size $|T_0| \le 125{,}000\,N(M,w)^2$ with $N(M,w) = 225|Q|^2 + 390|Q| + 4|w| + 173$, reducing the compiled size of a $1$-state machine from at least $2^{57207}$ seed bits to $1{,}996{,}921$ leaves; moreover, every macro-step of the zipper tree-walking selector $\sigma_{\mathrm{TM}}$ terminates in at most $3500(2|t|-1)$ cursor micro-ticks with no state retained between contractions, halting is recognized by a minimal $11$-state deterministic bottom-up tree automaton $\mathcal{H}_{11}$ (Proposition 3.8), and the bare halted term decodes to the exact output word $\operatorname{out}_M(w)$ in linear time $O(|T_k|)$. In Section 4, we remove the embedded universal transition table from the selector itself: Theorem 4.5 constructs a program-free selector $\sigma_{\mathrm{CTS}}$ over self-describing pure-$S$ cyclic-tag encodings $\mathcal{E}_{\mathrm{CTS}}(P,w)$ of quadratic leaf size at most $2500(\|(P,w)\|+1)^2$, recognized at halting by the identical $11$-state automaton $\mathcal{H}_{11}$, and Proposition 4.4 proves that every instance $\mathcal{E}_{\mathrm{CTS}}(P,w)$ is reachable via pure-$S$ reduction from a single fixed $10$-leaf combinator $D_{\mathrm{seed}} \equiv S(S(S S))(S(S S))(S S)S$. Theorem 4.7 further compresses $\sigma_{\mathrm{CTS}}$ to an explicit two-pass contextual finite-state pocket tree transducer $\mathcal{T}_{\mathrm{pocket}}$ with $25$ static structural roles, $23$ bottom-up states per node, and $136$ top-down pointer states, containing zero universal Turing or tag transition tables and executing each pure-$S$ contraction in at most $2|M| - 1 + \mathrm{depth}(M)$ elementary transitions.

Section 5 characterizes why external redex selection is necessary for Theorems 3.9, 4.5, and 4.7, sharpening the automata-theoretic perspective of Bojańczyk and Colcombet [12] and Kutrib and Meyer's deterministic tree-walking-storage automata [40, 41]. Theorem 5.2 proves a controller-complexity separation: a fixed root-restarted finite-state tree-walking selector coupled with a $3$-state bottom-up halting tree automaton is already Turing-complete over unlabeled binary trees governed solely by the unary leaf-splitting rule $\mathsf{Leaf} \to_{\mathrm{sp}} \mathsf{Node}(\mathsf{Leaf},\mathsf{Leaf})$, which performs neither subtree duplication nor arity-$3$ interaction. Within controlled rewriting, the distinctive contribution of $S$ is therefore in-tree subtree duplication, which powers the program-free self-description and $10$-leaf seed genesis of Section 4. Conversely, once the external selector is removed in favor of unrestricted pure-$S$ reduction $\to_S^*$, Proposition 5.4 exhibits explicit $7$-step and $5$-step multiway reductions that trigger spurious halting on arbitrary non-terminating payloads in both protected-frame counter hubs and tag-dispatcher encodings, while Theorem 5.5 proves unconditionally that no closed $S$-term can realize asymmetric Church-Boolean branch gating.

Sections 2, 6, and 8 develop the conservation laws, finite algebraic decidability theory, and fixed-order expressiveness of unguided $\mathrm{CL}(S)$ rewriting, resolving Questions 5, 7, 10, 30 (on $\mathrm{Prod} \times \mathcal{T}_S$), and 31 alongside structural obstructions toward Conjecture 17 of Barendregt, Endrullis, Klop, and Waldmann [4]. In Section 2, Theorem 2.3 shows that the left-subtree leaf sum $L(M)$ decreases by the exact constant $2$ on every leaf-preserving step $S X Y S \to_S (X S)(Y S)$, making leaf-preserving reduction confluent, strongly normalizing, and Jordan–Hölder ranked with sharp upper bound $\lfloor(|M|-1)(|M|-2)/4\rfloor$ (exponentially sharpening Bergstra's $O(2^{|M|})$ bound), accompanied by constructive proofs of closed non-spiralling and dependency-pair obstructions toward open Conjecture 17 showing that $M \to_S^+ C[M^\sigma]$ requires a variable $x$ occurring in $M$ whose image $\sigma(x)$ has rightmost leaf $x$ and $\operatorname{rs}(\sigma(x)) \ge 1$ under unbounded right-spine growth, complemented by the exact $8$-leaf open non-$\mathrm{SN}$ threshold and parametric $(4n+3)$-step near-miss (Proposition 2.11 and Theorems 2.12, 2.13, and 2.15). In Section 6, eliminating the additive offset table ($B \equiv 0$) via a pointwise minimal multiplier matrix $A \colon Q_{\mathrm{HN}}^2 \to \{0,\dots,30\}$ (Proposition 6.7) yields a pure-multiplier potential proving completeness of the $35$-state head-normalization $S$-algebra $\mathcal{A}_{\mathrm{HN}}$ and linear-time decidability of root normal forms, resolving Question 10 and Footnote 4 of [4] (Theorem 6.8), alongside constructive top-termination and absence of Berarducci mute $S$-terms [9, 8] (Theorem 6.9). Synthesizing a minimal $39$-state productivity $S$-algebra $\mathcal{A}_P$ via rank-$10$ critical-pair stratification over the Myhill–Nerode minimal $113$-state reachable subalgebra $\mathrm{PH} \subseteq Q_P \times Q_{\mathrm{HN}}$ (Proposition 6.15) resolves Question 5 in the affirmative (Theorem 6.14). Through the automaton-free three-constructor grammar $\mathcal{H} ::= A \mid S\mathcal{H} \mid \mathcal{H}\mathcal{H}$ and $\mathcal{U} = \mathcal{H}\mathcal{H}\mathcal{H}$, we give self-contained proofs of Question 7—including infinite $\mathrm{SN}/\overline{\mathrm{SN}}$ refinement alternation and the atomic $S \mapsto S S$ leaf-splitting law ($T_n \in \mathrm{SN} \iff n \not\equiv 9 \pmod{10}$; Theorem 6.19)—and Question 31 separating $\{A A A S^k\}_{k \ge 0}$ and $\mathcal{A}_{36}$ despite identical clocked Böhm trees $\bot$ (Theorem 6.20), while Theorem 6.21 and Proposition 6.22 establish a sharp dichotomy for Dana Scott's Question 30 [55]: Böhm-tree equality is faithful and constructively decidable for $=_S$ across $\mathrm{Prod} \times \mathcal{T}_S$ ($\mathrm{SN} \subsetneq \mathrm{Prod}$, while general convertibility on $(\mathcal{T}_S \setminus \mathrm{Prod})^2$ remains open), whereas even a single $\bot$ at any depth destroys clocked-Böhm faithfulness. Theorem 6.25 characterizes functional orders $\{0,1,2,3\}$ on open and closed $S$-terms via minimal $S$-algebras of $35$, $12$, and $3$ states and unique right-comb closed order-$3$ terms (clarifying the prose example $S S S$ versus $S(S S S)S$ in [4, p. 90]). Section 8 establishes deterministic strategy coincidence and quadratic trace languages on $Z_{\mathrm{Zac}}$ (Proposition 8.1), a $5$-step innermost Case-$3$ ceiling (Theorem 8.2), and Post-clone monotonicity barriers [49] versus a $4$-state algebra $\mathcal{D}_4$ realizing an $11$-leaf normal-form combinator for Rule 110 (Theorem 8.3).

Section 7 resolves the open problems and conjectures governing the canonical translation $(M)_\lambda$ of pure-$S$ terms into Church's non-erasing $\lambda\mathrm{I}$-calculus [16], where $(S)_\lambda \equiv \lambda x y z.\, x z (y z)$. Establishing constructive weak-head standardization and Church's conservation theorem ($\mathrm{WN}_\beta \iff \mathrm{SN}_\beta$ on $\lambda\mathrm{I}$), Theorem 7.3 proves Conjecture 40 of [4] in the affirmative: $\operatorname{ord}_{\mathrm{CL}}(M) = \operatorname{ord}_\lambda((M)_\lambda)$ holds for every combinatory term over $\{S, K, I\}$ and across $\mathrm{CL}(S)$. Normalization, however, diverges across $(-)_\lambda$ once $\beta$-redexes form beneath generated $\lambda$-binders. Improving Waldmann's $13$-leaf example, Proposition 7.4 identifies the global-minimum $9$-leaf closed $\mathrm{SN}$ term $W_9 \equiv S(S(A A))S$ and $10$-leaf normal form $N_{10} \equiv S(S(S A A))S$ with $(W_9)_\lambda, (N_{10})_\lambda \notin \mathrm{SN}_\beta$, and Theorem 7.5 constructs the global-minimum $14$-leaf closed term $M_{14} \equiv S A (S W_9)$ and $15$-leaf normal form $M_{15} \equiv S A (S N_{10})$ refuting both Conjectures 42 and 43 simultaneously, while proving the valid converse implication and establishing the repaired equivalence $\mathrm{DeepNorm}(M) \iff (M)_\lambda \in \mathrm{SN}_\beta$ via hereditary fresh-variable saturation in $\mathrm{CL}(S)$. For Question 34 (decidability and regularity of $L_{34} = \{M \in \mathcal{T}_S : (M)_\lambda \in \mathrm{SN}_\beta\}$), Theorem 7.6 reduces $\lambda\mathrm{I}$ strong normalization to single-constant combinatory saturation $\mathrm{DeepNorm}_1$ in left-linear $\mathrm{CL}(S, x_0)$, proves that universal $\lambda\mathrm{I}$ context non-erasure collapses all $\lambda\beta$-diverging closed $S$-terms into a single absorbing Myhill–Nerode sink $\infty_{34}$, demonstrates mutual congruence incomparability between $\equiv_{34}$ and $\equiv_{\mathrm{SN}}$ with four-way normal-form splitting inside $q_6$ (splitting even the shared joint fiber $(q_6, h_9, p_{18})$ of $\mathcal{A}_{\mathrm{SN}} \times \mathcal{A}_{\mathrm{HN}} \times \mathcal{A}_P$), and isolates finiteness of $\mathcal{T}_S / {\equiv_{34}}$ and decidability of $L_{34}$ as the sharpened single-constant open problem. Finally, Proposition 7.8 and Theorem 7.9 resolve Question 32 in the negative: despite small-term $\lambda\beta$-rigidity and uniqueness of Waldmann's $(8,11)$ closed $\beta$-convertible pair up to $11$ leaves, no finite set of $\lambda\beta$-sound pure-$S$ equations axiomatizes $=_\beta$ on $\mathrm{CL}(S)$.

Finally, Section 9 classifies all $14$ empirical pure-$S$ benchmarks studied in Wolfram's challenge announcement [71] (Theorem 9.1), derives exact all-step $\to_{\mathrm{lo}}$ state evolutions and cubic leaf-count closed forms for $Z_{\mathrm{Zac}}$, $W_2$ (together with its $=_S$-inconvertible $+14$-step twin $W_2^{\mathrm{twin}}$), $D_{\mathrm{seed}}$, and $A A A$ (Theorem 9.4), characterizes Garden-of-Eden (isolated) normal forms syntactically with a Mahler-type counting recurrence and sub-ternary growth rate $\gamma_{\mathrm{Iso}} \approx 2.9076221057 < 3$ (Theorem 9.7), establishes small-term Catalan minimality thresholds across $1 \le |M| \le 11$ (Theorem 9.8), and applies Flajolet–Sedgewick singularity analysis [29] to the polynomial generating-function systems of $\mathcal{A}_{\mathrm{HN}}$, $\mathcal{A}_{\mathrm{SN}}$, and $\mathcal{A}_P$, advancing the quantitative combinatory logic program of Bendkowski, Grygiel, and Zaionc [7] (Theorem 9.10). Because the unsolvable sink $\infty_{\mathrm{HN}}$ is a left ideal ($q \odot_{\mathrm{HN}} \infty_{\mathrm{HN}}$ need not equal $\infty_{\mathrm{HN}}$, as witnessed by $S(A A A) \in \mathrm{HNF}$), Puiseux expansion at the Catalan singularity $z = 1/4$ yields the exact dyadic-ternary rational head-normalizing density and its partition across functional orders $\{0, 1, 2, 3\}$:

$$
c_{\mathrm{HN}} \;=\; \lim_{n \to \infty} \frac{\#\mathrm{HN}(n)}{C_{n-1}} \;=\; \frac{4\,429\,673}{7\,077\,888},
\qquad
(c_0, c_1, c_2, c_3) \;=\; \Bigl(\frac{2\,648\,215}{7\,077\,888},\, \frac{1\,864\,553}{7\,077\,888},\, \frac{835}{2\,304},\, 0\Bigr),
$$

satisfying $c_0 + c_1 + c_2 + c_3 = 1$ and $c_1 + c_2 = c_{\mathrm{HN}} \approx 0.6258467215$, whereas the two-sided context sinks of $\mathcal{A}_{\mathrm{SN}}$ and $\mathcal{A}_P$ push their dominant singularities strictly past $1/4$ to distinct degree-$35$ algebraic branch points $\rho_{\mathrm{SN}} > \rho_P > 1/4$, forcing exponential rarity of both normalizing and productive closed $S$-terms with certified all-$n$ upper bounds proportional to $(250/259)^n$.

### 1.3. Technical Overview and Proof Architecture

Six structural mechanisms underlie the proofs across Sections 2–9.

Protected spine-$2$ storage frames $F(a,b,j) \equiv S a(S b j)$, building on local opening identities of Filin [27], isolate reductions inside their left slot $a$ and right slot $b$ while sequestering historical junk $j$ without erasure: because $\operatorname{ls}(F(a,b,j)) = 2$, the term $F(a,b,j)$ has no root redex. Unopened leaves of the addressable memory layout are represented by phase-indexed counter generators $G(m,n) \equiv \nu_m \nu_n S$, which open deterministically in $6$ or $7$ contractions into $F(G(m',n'), G(m',n'), j')$ with non-frame intermediate stages and non-$\mathrm{S}_2$ junk $j'$. Wrapping an append-only chain of $11$-bit cell records along the right spine of $F$-frames allows the stateless zipper selector $\sigma_{\mathrm{TM}}$ to execute $U_{\mathrm{bin}}$ via a two-pass priority scan (completing any pending neighbor move before initiating a new active transition) while reading only $6$ local cursor observations and resetting all control state at each contraction. For cyclic tag systems, factoring local structural recognition into $25$ static node roles, a $23$-state bottom-up summary pass, and a $136$-state top-down pointer pass compresses $\sigma_{\mathrm{CTS}}$ into the two-pass pocket tree transducer $\mathcal{T}_{\mathrm{pocket}}$ running in $2|M| - 1 + \mathrm{depth}(M)$ transitions without any embedded universal rule table.

In-tree self-description stands in sharp contrast to unguided multiway collapse and spine conservation. By encoding cyclic-tag appendant templates with $3$-bit versioned handshakes ($\mathsf{idle} \to \mathsf{armed} \to \mathsf{appending} \to \mathsf{idle}$) paired with staged queue allocation, $\sigma_{\mathrm{CTS}}$ copies arbitrarily long appendants onto the queue tail using pure-$S$ duplication alone, and every initial tree $\mathcal{E}_{\mathrm{CTS}}(P,w)$ unfolds directly from $D_{\mathrm{seed}}$ via a $5$-step bootstrap to $(\nu_1 S)\,G(2,2)$ followed by selective slot openings. Removing the selector destroys this discipline immediately: under unrestricted $\to_S^*$, any unopened halt-flag generator inside a protected hub opens in $7$ steps regardless of payload divergence, and any $D \cdot Q$ queue dispatcher contracts its live $1$-cell prematurely to a tombstone in $1$ step and executes the $0$-branch in $4$ further steps. More fundamentally, an inductive spine-grammar invariant ($\mathcal{W}_0$ and $\mathcal{O}$ in Section 5.3) shows that in any reduction of $M x_0 x_1 U_1 \cdots U_m$, every head $S$-redex capable of bringing $x_1$ into active function position must carry $x_0$ as one of its first two arguments, activating $x_0$ first. On size-preserving reductions $S X Y S \to_S (X S)(Y S)$, the left-subtree leaf sum $L(M)$ drops by $2$ at each step, while on open terms dependency-pair right-tail tracking forces any hypothetical open spiral $M \to_S^+ C[M^\sigma]$ to fix a variable $x$ as the rightmost leaf of $\sigma(x)$ along an unbounded right spine.

Pure-multiplier algebraic potentials and three-constructor syntactic grammars eliminate non-constructive appeals to König's lemma and large table searches in $\mathrm{CL}(S)$ solvability and convertibility proofs. For the $35$-state head-normalization algebra $\mathcal{A}_{\mathrm{HN}}$, setting $\mu_{\mathrm{HN}}(S) = 1$ and $\mu_{\mathrm{HN}}(M N) = \mu_{\mathrm{HN}}(M) + A(\llbracket M \rrbracket_{\mathrm{HN}}, \llbracket N \rrbracket_{\mathrm{HN}})\,\mu_{\mathrm{HN}}(N)$ with a pointwise minimal integer multiplier table $A \colon Q_{\mathrm{HN}}^2 \to \{0,\dots,30\}$ ($142$ entries exceeding $1$, and zero additive offset table $B \equiv 0$) yields strict decrease on every active head contraction outside $\infty_{\mathrm{HN}}$, constructively bounding head-reduction lengths. Independently of tree automata, closing $A \equiv S S S$ under $S \mathcal{H}$ and $\mathcal{H}\mathcal{H}$ isolates a self-propagating unsolvable locus $\mathcal{U} = \mathcal{H}\mathcal{H}\mathcal{H}$ that yields concise book proofs for Questions 7 and 31.

Canonical productive values and critical-pair stratification resolve Question 5 and govern Böhm-tree faithfulness on $\mathrm{Prod} \times \mathcal{T}_S$. On closed $S$-terms, left application preserves $\bot$ at the same Böhm depth while right application increases depth by at most $1$ because $\operatorname{ord}_{\mathrm{CL}}(M) \le 3$ prevents an argument from escaping a head spine without root consumption. Jointly analyzing $\mathcal{A}_P \times \mathcal{A}_{\mathrm{SN}}$ shows that $34$ of the $38$ accepting states of $\mathcal{A}_P$ consist solely of strongly normalizing terms, three further states reduce to $\mathrm{HNF}$ without root contractions, and $(q_{29}, \infty_{\mathrm{SN}})$ is the unique non-normalizing productive root-redex fiber, inhabited by the Zachos family $G_m G_n$ whose right applications $(G_m G_n) U$ always collapse to $\bot$. Compressing the $39^3$ transition cube via $35$ two-dimensional overrides over the $113$-state Myhill–Nerode minimal reachable subalgebra $\mathrm{PH} \subseteq Q_P \times Q_{\mathrm{HN}}$ yields a rank-$10$ stratification constructively witnessing $\bot_d(M)$ whenever $\llbracket M \rrbracket_P = \infty_P$, while root-normal-form conversion decomposition along $\bot$-free spines makes Böhm-tree equality faithful and decidable for $=_S$ on $\mathrm{Prod} \times \mathcal{T}_S$.

Constructive weak-head standardization in Church's $\lambda\mathrm{I}$-calculus [16], combined with hereditary combinatory saturation, governs the translation $(M)_\lambda$. Because weak and strong $\beta$-normalization coincide in $\lambda\mathrm{I}$, head steps of $(M)_\lambda$ track fresh-variable combinatory head reductions closely enough to preserve functional order across $\{S, K, I\}$ (Conjecture 40). Once head normal form is reached, however, $\beta$-reduction continues beneath generated $\lambda$-binders: in $M_{14} \equiv S A (S W_9)$, the $9$-leaf $\mathrm{SN}$ subterm $W_9 \equiv S(S(A A))S$ sits protected inside a spine-$2$ argument even after $M_{14}$ receives three fresh variables, yet $(W_9)_\lambda$ diverges inside a $\lambda$-body of $(M_{14})_\lambda$, refuting Conjectures 42 and 43. Enforcing fresh-variable normalizability hereditarily on every generated subterm defines the pure-$\mathrm{CL}(S)$ predicate $\mathrm{DeepNorm}(M)$ characterizing $(M)_\lambda \in \mathrm{SN}_\beta$, while universal variable retention in $\lambda\mathrm{I}$ contexts collapses all $\lambda\beta$-diverging closed $S$-terms into the single Myhill–Nerode sink $\infty_{34}$ and reduces Question 34 to single-constant saturation $\mathrm{DeepNorm}_1$ in left-linear $\mathrm{CL}(S, x_0)$. Conversely, bounding redex creation depth under any finite pure-$S$ axiom set leaves infinitely many $\lambda\beta$-identities unprovable, resolving Question 32.

Finally, macro-cycle recurrences, predecessor-free decompositions, and strongly connected component (SCC) singularity analysis govern the quantitative dynamics of $\mathrm{CL}(S)$. Indexing outer spine wrappers along $\to_{\mathrm{lo}}$ yields closed-form all-step state and cubic leaf formulas, while characterizing absence of $\to_S$-predecessors yields the Mahler recurrence for Garden-of-Eden normal forms. On $\mathcal{A}_{\mathrm{HN}}$ (and its open-term extension classifying orders $\{0,1,2,3\}$), evaluating the quadratic generating-function system at $z = 1/4$ produces exact rationals $L_q(1/4) \in \mathbb{Q}$ and reduces the Puiseux coefficients $b_q$ to a nonsingular rational linear system, whereas eliminating transient states of $\mathcal{A}_{\mathrm{SN}}$ and $\mathcal{A}_P$ isolates recurrent cores analytic strictly past $z = 1/4$, certified both by degree-$35$ resultant polynomials and by positive rational upper-envelope evaluations at $z = 37/125$ formalized directly over $\mathbb{N}$.

### 1.4. Constructive Mechanization and Organization

Every definition, construction, finite algebraic check, and theorem in this monograph has been constructively formalized and kernel-verified in the Lean 4 theorem prover (version 4.33.1). Throughout the development, all proofs rely solely on Lean's standard propositional extensionality and quotient soundness principles, avoiding classical choice, excluded middle on undecidable predicates, and external reflection or native-code evaluation oracles. In addition, all compilers, tree-walking selectors, pocket tree transducers, finite $S$-algebras, $\lambda\mathrm{I}$-translation analyzers, halting detectors, and output decoders are implemented in a standalone Wolfram Language package cross-checked on concrete Turing machine, Busy Beaver, cyclic tag, $\lambda\mathrm{I}$-divergence, and small-term census benchmarks.

The remainder of the monograph is organized into nine sections and an appendix. Section 2 establishes the rewriting syntax, confluence, leaf-preserving $\Delta L = -2$ conservation, constructive closed non-spiralling, dependency-pair open-spiral obstructions toward Conjecture 17, Böhm trees, finite $S$-algebras, and ongoing-simulation preliminaries. Section 3 presents the $U_{3,11}$ compiler, protected spine-$2$ encoding, stateless zipper tree-walking selector, minimal $11$-state halting automaton, and linear-time bare-term output decoder. Section 4 develops the program-free cyclic tag simulator, its genesis from the $10$-leaf seed $D_{\mathrm{seed}}$, and its compression to the two-pass $(25, 23, 136)$ pocket tree transducer $\mathcal{T}_{\mathrm{pocket}}$. Section 5 proves the leaf-splitting controller-separation theorem, the $7$-step and $5$-step multiway halting shortcuts, and the impossibility of asymmetric branch gating. Section 6 constructs the finite $S$-algebras $\mathcal{A}_{\mathrm{SN}}, \mathcal{A}_{\mathrm{HN}}, \mathcal{A}_P, \mathcal{A}_{36}$, establishes pure-multiplier head potentials, $113$-state $\mathrm{PH}$ minimality, automaton-free book proofs, productive Böhm faithfulness, and the functional order $\{0,1,2,3\}$ minimal-algebra hierarchy, resolving Questions 5, 7, 10, 30 (on $\mathrm{Prod} \times \mathcal{T}_S$), and 31 of [4] together with constructive top-termination. Section 7 develops the constructive $\lambda\mathrm{I}$-translation theory, proving Conjecture 40, refuting Conjectures 42 and 43 with $14$- and $15$-leaf minimal counterexamples and a hereditary saturation repair, establishing single-constant collapse and congruence incomparability for Question 34, and resolving Question 32 in the negative. Section 8 analyzes deterministic strategy coincidence, quadratic trace languages, innermost right-step bounds, and Post-clone barriers versus minimal normal-form Rule 110. Section 9 classifies Wolfram's $14$ benchmark terms, proves the all-step $\to_{\mathrm{lo}}$ cubic jump-ahead formulas, characterizes Garden-of-Eden normal forms, establishes small-term minimality thresholds up to $11$ leaves, and proves the Catalan asymptotic phase-transition and exact order-density theorems. Section 10 discusses the constructive formalization architecture, and Appendix A provides a complete concordance mapping every numbered result to its machine-checked declaration.

## 2. Preliminaries: Rewriting Semantics, Leaf-Preserving Conservation, Non-Spiralling, and Open-Spiral Obstructions

### 2.1. Syntax, Spine Geometry, and Leaf-Preserving Conservation Laws

We begin by fixing the syntax, structural measures, substitutions, and reduction relations of $\mathrm{CL}(S)$, following the conventions of Barendregt [1], Waldmann [66], and Barendregt, Endrullis, Klop, and Waldmann [4].

**Definition 2.1 (Syntax, spine measures, and reduction in $\mathrm{CL}(S)$).** 
Let $\mathcal{V} = \{x_0, x_1, x_2, \dots\}$ be a countably infinite set of variables. The set $\mathcal{T}_S(\mathcal{V})$ of *open $S$-terms* is generated inductively by the grammar

$$
M, N \;::=\; S \;\mid\; x \;\mid\; (M\,N) \qquad (x \in \mathcal{V}),
$$

and the subset $\mathcal{T}_S \subset \mathcal{T}_S(\mathcal{V})$ of *closed* (or *ground*) *$S$-terms*—also called *pure-$S$ combinators*—consists of all variable-free terms generated by $M, N ::= S \mid (M\,N)$. Binary application associates to the left, so $M N P \equiv ((M N) P)$, and $M \equiv N$ denotes literal syntactic identity of finite binary trees. Throughout the paper we write the standard closed abbreviations

$$
T \;\equiv\; S S, \qquad B \;\equiv\; S(S S) \;\equiv\; S T, \qquad A \;\equiv\; S S S \;\equiv\; T S, \qquad G_0 \;\equiv\; S T T, \qquad V \;\equiv\; S G_0,
$$

together with $G_{k+1} \equiv T G_k$ ($k \ge 0$), Zachos's $10$-leaf combinator $Z_{\mathrm{Zac}} \equiv G_0 G_0$, and the $10$-leaf seed $D_{\mathrm{seed}} \equiv S B B T S$. For each $n \ge 1$, the closed *left comb* $L_n \in \mathcal{T}_S$ and *right comb* $R_n \in \mathcal{T}_S$ of leaf size $n$ are defined recursively by $L_1 \equiv R_1 \equiv S$, $L_{n+1} \equiv L_n S$, and $R_{n+1} \equiv S R_n$.

For atoms $a \in \{S\} \cup \mathcal{V}$ and terms $M, N \in \mathcal{T}_S(\mathcal{V})$, the *leaf size* $|M| \ge 1$, binary-tree *node count* $\operatorname{nodes}(M)$, *left-spine length* $\operatorname{ls}(M)$, *right-spine length* $\operatorname{rs}(M)$, *head atom* $\mathrm{hd}(M) \in \{S\} \cup \mathcal{V}$, and *rightmost atom* $\mathrm{rt}(M) \in \{S\} \cup \mathcal{V}$ are defined recursively by

$$
\begin{aligned}
  |a| &= 1, & |M N| &= |M| + |N|, & \operatorname{nodes}(M) &= 2|M| - 1, \\
  \operatorname{ls}(a) &= 0, & \operatorname{ls}(M N) &= 1 + \operatorname{ls}(M), & \operatorname{rs}(a) &= 0,\quad \operatorname{rs}(M N) = 1 + \operatorname{rs}(N), \\
  \mathrm{hd}(a) &\equiv a, & \mathrm{hd}(M N) &\equiv \mathrm{hd}(M), & \mathrm{rt}(a) &\equiv a,\quad \mathrm{rt}(M N) \equiv \mathrm{rt}(N).
\end{aligned}
$$

We write $\mathrm{Vars}(M) \subset \mathcal{V}$ for the finite set of variables occurring in $M$, and $\#_x(M) \in \mathbb{N}$ for the number of leaf occurrences of $x \in \mathcal{V}$ in $M$. Given a substitution $\sigma \colon \mathcal{V} \to \mathcal{T}_S(\mathcal{V})$, the simultaneous substitution instance $M^\sigma \in \mathcal{T}_S(\mathcal{V})$ is defined by $S^\sigma \equiv S$, $x^\sigma \equiv \sigma(x)$, and $(M N)^\sigma \equiv M^\sigma N^\sigma$.

A *one-hole context* is generated by $C[\,] ::= \square \mid (C[\,]\,N) \mid (M\,C[\,])$, with $C[M]$ denoting replacement of the unique hole $\square$ by $M$, context composition written $(C_1 \circ C_2)[M] \equiv C_1[C_2[M]]$, and substitution extended to contexts via $\square^\sigma \equiv \square$, $(C[\,]\,N)^\sigma \equiv (C^\sigma[\,]\,N^\sigma)$, and $(M\,C[\,])^\sigma \equiv (M^\sigma\,C^\sigma[\,])$, so that $(C[M])^\sigma \equiv C^\sigma[M^\sigma]$. The *left-branching depth* $d_{\mathrm{L}}(C) \in \mathbb{N}$ and variable count $\#_x(C) \in \mathbb{N}$ of a context are given by $d_{\mathrm{L}}(\square) = 0$, $d_{\mathrm{L}}(C[\,]\,N) = 1 + d_{\mathrm{L}}(C)$, $d_{\mathrm{L}}(M\,C[\,]) = d_{\mathrm{L}}(C)$, and $\#_x(C[M]) = \#_x(C) + \#_x(M)$. We write $U \trianglelefteq M$ (respectively $U \triangleleft M$) if $M \equiv C[U]$ for some context $C[\,]$ (respectively some $C[\,] \not\equiv \square$).

An *$S$-redex* is any term of the form $S X Y Z$, with *contractum* $(X Z)(Y Z)$. *One-step reduction* $\to_S$ is the contextual closure of root contraction: $C[S X Y Z] \to_S C[(X Z)(Y Z)]$. We write $\to_r$ for contraction at the root ($C[\,] \equiv \square$), $\to_{\mathrm{nr}}$ for a non-root step ($C[\,] \not\equiv \square$), $\to_S^+$ for the transitive closure of $\to_S$, $\to_S^*$ for its reflexive-transitive closure, $\to_S^k$ for $k$-fold composition, and $=_S$ for the equivalence relation (convertibility) generated by $\to_S$. A step $M \to_S N$ is *leaf-preserving*, written $M \to_{S,\mathrm{lp}} N$, if $|M| = |N|$. A term $M \in \mathcal{T}_S(\mathcal{V})$ is in *normal form* ($M \in \mathrm{NF}$) if there is no $N$ with $M \to_S N$; *weakly normalizing* ($M \in \mathrm{WN}$) if $M \to_S^* N$ for some $N \in \mathrm{NF}$; and *strongly normalizing* ($M \in \mathrm{SN}$) if $M$ is constructively well-founded (accessible) with respect to $\to_S$, meaning every reduction sequence starting from $M$ terminates.

Note that the number of closed $S$-terms of leaf size $n \ge 1$ is the Catalan number $C_{n-1} = \frac{1}{n}\binom{2n-2}{n-1}$, since closed $S$-terms of leaf size $n$ are in bijection with full binary trees having $n$ leaf nodes and $n-1$ internal application nodes.

**Proposition 2.2 (Confluence, monotonicity, and $\mathrm{WN} = \mathrm{SN}$).** 
The rewrite system $(\mathcal{T}_S(\mathcal{V}), \to_S)$ satisfies the following properties:

- (i) *Confluence (Church–Rosser):* If $M \to_S^* N_1$ and $M \to_S^* N_2$, there exists $P \in \mathcal{T}_S(\mathcal{V})$ such that $N_1 \to_S^* P$ and $N_2 \to_S^* P$. Consequently, $M =_S N$ holds if and only if $M$ and $N$ share a common reduct, and normal forms are unique up to $\equiv$.
- (ii) *Leaf balance, spine monotonicity, and leaf-preserving redex criterion:* Every contextual contraction $M \equiv C[S X Y Z] \to_S C[(X Z)(Y Z)] \equiv N$ satisfies $|N| + 1 = |M| + |Z|$, $\operatorname{rs}(M) \le \operatorname{rs}(N)$, and $\mathrm{rt}(N) \equiv \mathrm{rt}(M)$. In particular, $|M| \le |N|$, with equality $|M| = |N|$ holding if and only if $|Z| = 1$ (that is, $Z \in \{S\} \cup \mathcal{V}$, and uniquely $Z \equiv S$ when $M \in \mathcal{T}_S$).
- (iii) *Conservation ($\mathrm{WN} = \mathrm{SN}$):* If $M \to_S N$ and $N \in \mathrm{SN}$, then $M \in \mathrm{SN}$. In particular, $\mathrm{WN} = \mathrm{SN}$ on $\mathcal{T}_S(\mathcal{V})$.

*Proof.* 
For (i), $\mathrm{CL}(S)$ is an orthogonal left-linear combinatory rewrite system [60]. Explicitly, adapting Takahashi's parallel reduction method [59], define $M \Rightarrow N$ inductively by $S \Rightarrow S$, $x \Rightarrow x$, and $M_1 M_2 \Rightarrow N_1 N_2$ whenever $M_i \Rightarrow N_i$, together with $S X Y Z \Rightarrow (X' Z')(Y' Z')$ whenever $X \Rightarrow X'$, $Y \Rightarrow Y'$, and $Z \Rightarrow Z'$. Define the complete development map $\Delta \colon \mathcal{T}_S(\mathcal{V}) \to \mathcal{T}_S(\mathcal{V})$ by $\Delta(S X Y Z) \equiv (\Delta(X)\,\Delta(Z))(\Delta(Y)\,\Delta(Z))$ on root redexes, $\Delta(M_1 M_2) \equiv \Delta(M_1)\,\Delta(M_2)$ on non-redex applications, and $\Delta(a) \equiv a$ on atoms $a \in \{S\} \cup \mathcal{V}$. Structural induction on $M \Rightarrow N$ yields the triangle property $N \Rightarrow \Delta(M)$: in the sole overlap check where $M \equiv (S X Y) Z$ steps via $M_1 M_2 \Rightarrow N_1 N_2$, inversion on $S X Y \Rightarrow N_1$ forces $N_1 \equiv S X' Y'$ with $X' \Rightarrow \Delta(X)$ and $Y' \Rightarrow \Delta(Y)$, whence $N_1 N_2 \equiv S X' Y' Z' \Rightarrow (\Delta(X)\,\Delta(Z))(\Delta(Y)\,\Delta(Z)) \equiv \Delta(M)$. The diamond property for $\Rightarrow$ follows, and since $\to_S \;\subseteq\; \Rightarrow \;\subseteq\; \to_S^*$, diagram chasing yields Church–Rosser confluence.

For (ii), let $|C|$ denote the sum of leaf sizes of all side subterms of $C[\,]$, so $|C[U]| = |C| + |U|$. Direct calculation gives

$$
|C[(X Z)(Y Z)]| + 1 \;=\; |C| + |X| + |Y| + 2|Z| + 1 \;=\; \bigl(|C| + 1 + |X| + |Y| + |Z|\bigr) + |Z| \;=\; |C[S X Y Z]| + |Z|.
$$

Since $|Z| \ge 1$, it follows that $|M| \le |N|$, with $|M| = |N|$ if and only if $|Z| = 1$, which restricts $Z$ to an atom in $\{S\} \cup \mathcal{V}$ (and to $S$ when $M \in \mathcal{T}_S$). At a root step, $\operatorname{rs}((X Z)(Y Z)) = 2 + \operatorname{rs}(Z) > 1 + \operatorname{rs}(Z) = \operatorname{rs}(S X Y Z)$ and $\mathrm{rt}((X Z)(Y Z)) \equiv \mathrm{rt}(Z) \equiv \mathrm{rt}(S X Y Z)$; induction over $C[\,]$ preserves $\operatorname{rs}(M) \le \operatorname{rs}(N)$ and $\mathrm{rt}(N) \equiv \mathrm{rt}(M)$ because left-child steps leave right spines untouched and right-child steps act on the right spine directly.

For (iii), enrich parallel reduction with an explicit contraction weight $M \Rightarrow_w N$ ($w \in \mathbb{N}$): atoms have weight $0$, application satisfies $M_1 M_2 \Rightarrow_{w_1 + w_2} N_1 N_2$, and redex contraction satisfies $S X Y Z \Rightarrow_{1 + w_X + w_Y + 2 w_Z} (X' Z')(Y' Z')$. Note that $M \to_S N$ implies $M \Rightarrow_1 N$. Structural induction on $M \Rightarrow_w N$ establishes the projection alternative: for every step $M \to_S M_1$, either there exists $w_1 < w$ with $M_1 \Rightarrow_{w_1} N$ (when $M \to_S M_1$ contracts a redex already contracted in $M \Rightarrow_w N$, using $(w_X + w_Z) + (w_Y + w_Z) < 1 + w_X + w_Y + 2 w_Z$), or there exist $N_1$ and $w_1 \in \mathbb{N}$ such that $N \to_S^+ N_1$ and $M_1 \Rightarrow_{w_1} N_1$ (when $M \to_S M_1$ contracts inside $Z \to_S Z_1$ of a redex $S X Y Z$, both copies of $Z'$ in $(X' Z')(Y' Z')$ step to $Z_1'$, yielding at least two positive steps $N \to_S^+ N_1$ because $Z$ is never erased). Well-founded induction on $N \in \mathrm{SN}$ (lifted to $\to_S^+$) with an inner induction on $w$ proves $M \in \mathrm{SN}$. Induction along $M \to_S^* N \in \mathrm{NF} \subseteq \mathrm{SN}$ yields $\mathrm{WN} \subseteq \mathrm{SN}$, and $\mathrm{SN} \subseteq \mathrm{WN}$ holds constructively by contracting the leftmost redex until none remains.
 $\square$

Leaf-preserving reductions $M \to_{S,\mathrm{lp}} N$ govern every constant-size transient segment of $\mathrm{CL}(S)$ dynamics. While Bergstra's classical exponential weight $\|P Q\|_{\mathrm{B}} = 2\|P\|_{\mathrm{B}} + \|Q\|_{\mathrm{B}}$ [38, 4] drops by $6 \cdot 2^{d_{\mathrm{L}}(C)}$ depending on context depth and yields only an $O(2^{|M|})$ step bound, we establish an exact depth-independent conservation law that makes $(\mathcal{T}_S(\mathcal{V}), \to_{S,\mathrm{lp}})$ a confluent Jordan–Hölder ranked system of sharp quadratic length $\Theta(|M|^2)$.

**Theorem 2.3 (Ranked leaf-preserving conservation law and sharp quarter-square bound).** 
For atoms $a \in \{S\} \cup \mathcal{V}$ and terms $P, Q \in \mathcal{T}_S(\mathcal{V})$, define Bergstra's weight $\|\cdot\|_{\mathrm{B}} \colon \mathcal{T}_S(\mathcal{V}) \to \mathbb{N}$ and the *left-subtree leaf sum* $L \colon \mathcal{T}_S(\mathcal{V}) \to \mathbb{N}$ recursively by

$$
\|a\|_{\mathrm{B}} = 1, \quad \|P Q\|_{\mathrm{B}} = 2\|P\|_{\mathrm{B}} + \|Q\|_{\mathrm{B}}, \qquad\qquad
L(a) = 0, \quad L(P Q) = L(P) + L(Q) + |P|.
$$

Then:

- (i) *Bergstra weight envelope and contextual drop:* Every $M \in \mathcal{T}_S(\mathcal{V})$ satisfies $2|M| - 1 \le \|M\|_{\mathrm{B}} \le 2^{|M|} - 1$; on closed terms $M \in \mathcal{T}_S$, equality $\|M\|_{\mathrm{B}} = 2|M| - 1$ holds if and only if $M \equiv R_{|M|}$, and $\|M\|_{\mathrm{B}} = 2^{|M|} - 1$ holds if and only if $M \equiv L_{|M|}$. Every leaf-preserving step $C[S X Y Z] \to_{S,\mathrm{lp}} C[(X Z)(Y Z)]$ satisfies $\|C[S X Y Z]\|_{\mathrm{B}} = \|C[(X Z)(Y Z)]\|_{\mathrm{B}} + 6 \cdot 2^{d_{\mathrm{L}}(C)}$, whence any $k$-step reduction $M \to_{S,\mathrm{lp}}^k N$ obeys $6k + 2|M| \le 2^{|M|}$.
- (ii) *Exact ranked conservation, confluence, and Jordan–Hölder property:* Every leaf-preserving step $M \to_{S,\mathrm{lp}} N$ at arbitrary depth in $\mathcal{T}_S(\mathcal{V})$ decreases $L$ by the exact constant $2$:

$$
L(M) \;=\; L(N) + 2. \tag{2.1}
$$

  Moreover, $\to_{S,\mathrm{lp}}$ is strongly normalizing and globally confluent on $\mathcal{T}_S(\mathcal{V})$. Consequently, every $M \in \mathcal{T}_S(\mathcal{V})$ admits a unique $\to_{S,\mathrm{lp}}$-normal form $\mathrm{nf}_{\mathrm{lp}}(M)$, and every maximal leaf-preserving reduction starting from $M$ has the identical length $\bigl(L(M) - L(\mathrm{nf}_{\mathrm{lp}}(M))\bigr)/2$.
- (iii) *Quadratic upper bound and quarter-square attainment:* Every $M \in \mathcal{T}_S(\mathcal{V})$ satisfies $|M| - 1 \le L(M)$ and $2 L(M) + |M| \le |M|^2$. Consequently, every $k$-step leaf-preserving reduction $M \to_{S,\mathrm{lp}}^k N$ satisfies

$$
k \;\le\; \left\lfloor \frac{(|M|-1)(|M|-2)}{4} \right\rfloor. \tag{2.2}
$$

  Conversely, define $N_2^{\mathrm{lp}} \equiv S S$, $N_3^{\mathrm{lp}} \equiv S S S$, and $N_{m+4}^{\mathrm{lp}} \equiv T\,N_{m+2}^{\mathrm{lp}}$ for $m \ge 0$. For every $n \ge 2$, the closed left comb $L_n$ satisfies $L_n \to_{S,\mathrm{lp}}^{\lfloor(n-2)^2/4\rfloor} N_n^{\mathrm{lp}}$ with $N_n^{\mathrm{lp}}$ in $\to_{S,\mathrm{lp}}$-normal form, matching (2.2) to within $\lfloor(n-1)/4\rfloor$ steps.

*Proof.* 
For (i), structural induction on $M$ establishes $2|M| \le \|M\|_{\mathrm{B}} + 1 \le 2^{|M|}$: at an application $P Q$, using $\|P\|_{\mathrm{B}} \ge 1$ gives $2|P| \le \|P\|_{\mathrm{B}} + 1 \le 2\|P\|_{\mathrm{B}}$ and hence $2(|P| + |Q|) \le (2\|P\|_{\mathrm{B}} + \|Q\|_{\mathrm{B}}) + 1$, with equality on closed terms forcing $\|P\|_{\mathrm{B}} = 1$ ($P \equiv S$) and $Q \equiv R_{|Q|}$, so $P Q \equiv R_{|P Q|}$. For the upper bound, $(2\|P\|_{\mathrm{B}} + \|Q\|_{\mathrm{B}} + 1) + 2 = 2(\|P\|_{\mathrm{B}} + 1) + (\|Q\|_{\mathrm{B}} + 1) \le 2 \cdot 2^{|P|} + 2^{|Q|} \le 2^{|P|+|Q|} + 2$ because $2 \cdot 2^j + 2^k \le 2^{j+k} + 2$ for all $j, k \ge 1$, with equality if and only if $k = 1$; on closed terms, equality forces $|Q| = 1$ ($Q \equiv S$) and $P \equiv L_{|P|}$, so $P Q \equiv L_{|P Q|}$. At a leaf-preserving root contraction $S X Y Z \to_r (X Z)(Y Z)$, Proposition 2.2(ii) gives $|Z| = 1$ and $\|Z\|_{\mathrm{B}} = 1$, so

$$
\|S X Y Z\|_{\mathrm{B}} \;=\; 4\|X\|_{\mathrm{B}} + 2\|Y\|_{\mathrm{B}} + 9 \;=\; \bigl(4\|X\|_{\mathrm{B}} + 2\|Y\|_{\mathrm{B}} + 3\bigr) + 6 \;=\; \|(X Z)(Y Z)\|_{\mathrm{B}} + 6.
$$

Inducting on $C[\,]$, a drop of $\delta$ at the hole scales by $2$ across $(C[\,]\,R)$ and by $1$ across $(P\,C[\,])$, producing $6 \cdot 2^{d_{\mathrm{L}}(C)} \ge 6$. Summing over $k$ steps gives $6k + 2|M| - 1 \le 6k + \|N\|_{\mathrm{B}} \le \|M\|_{\mathrm{B}} \le 2^{|M|} - 1$.

For (ii), let $M \to_{S,\mathrm{lp}} N$. At a root contraction $S X Y Z \to_r (X Z)(Y Z)$ with $|Z| = 1$, the atom $Z$ satisfies $L(Z) = 0$. Expanding $L$ on both sides yields

$$
\begin{aligned}
  L(S X Y Z) &\;=\; L(S X Y) + L(Z) + |S X Y| \;=\; \bigl(L(S X) + L(Y) + 1 + |X|\bigr) + 0 + (1 + |X| + |Y|) \\
             &\;=\; L(X) + L(Y) + 2|X| + |Y| + 3, \\
  L\bigl((X Z)(Y Z)\bigr) &\;=\; \bigl(L(X) + 0 + |X|\bigr) + \bigl(L(Y) + 0 + |Y|\bigr) + (|X| + 1) \;=\; L(X) + L(Y) + 2|X| + |Y| + 1,
\end{aligned}
$$

proving (2.1) at the root. For a left-child step $P Q \to_{S,\mathrm{lp}} P' Q$, leaf preservation $|P| + |Q| = |P'| + |Q|$ gives $|P| = |P'|$, so $L(P Q) = L(P) + L(Q) + |P| = (L(P') + 2) + L(Q) + |P'| = L(P' Q) + 2$; for a right-child step $P Q \to_{S,\mathrm{lp}} P Q'$, leaf preservation $|Q| = |Q'|$ gives $L(P Q) = L(P) + (L(Q') + 2) + |P| = L(P Q') + 2$. Strong normalization of $\to_{S,\mathrm{lp}}$ follows immediately by bounded induction on $L(M) \in \mathbb{N}$. For confluence, define leaf-preserving parallel reduction $P \Rightarrow_{\mathrm{lp}} Q$ by reflexivity on atoms, congruence on applications, and $S X Y Z \Rightarrow_{\mathrm{lp}} (X' Z)(Y' Z)$ whenever $X \Rightarrow_{\mathrm{lp}} X'$, $Y \Rightarrow_{\mathrm{lp}} Y'$, and $|Z| = 1$ (note that $|Z| = 1$ forces $Z \Rightarrow_{\mathrm{lp}} Z'$ to satisfy $Z' \equiv Z$). Define the conditional complete development $\Delta_{\mathrm{lp}}(S X Y Z) \equiv (\Delta_{\mathrm{lp}}(X)\,Z)(\Delta_{\mathrm{lp}}(Y)\,Z)$ if $|Z| = 1$, and $\Delta_{\mathrm{lp}}(P Q) \equiv \Delta_{\mathrm{lp}}(P)\,\Delta_{\mathrm{lp}}(Q)$ otherwise, with $\Delta_{\mathrm{lp}}(a) \equiv a$ on atoms. Because $|Q| = |P|$ holds along $P \Rightarrow_{\mathrm{lp}} Q$, the side condition $|Z| = 1$ is invariant, giving the triangle property $Q \Rightarrow_{\mathrm{lp}} \Delta_{\mathrm{lp}}(P)$ and hence global confluence of $\to_{S,\mathrm{lp}}^*$. If $M \to_{S,\mathrm{lp}}^{k_1} N_1$ and $M \to_{S,\mathrm{lp}}^{k_2} N_2$ reach $\to_{S,\mathrm{lp}}$-normal forms, confluence forces $N_1 \equiv N_2$, and iterating (2.1) gives $L(M) = L(N_1) + 2 k_1 = L(N_1) + 2 k_2$, whence $k_1 = k_2$.

For (iii), structural induction on $M$ gives $|M| \le L(M) + 1$ (since $|P| + |Q| \le |P| + L(Q) + 1 \le L(P) + L(Q) + |P| + 1 = L(P Q) + 1$) and $2 L(M) + |M| \le |M|^2$, using $|Q| \ge 1$ to bound

$$
2\bigl(L(P) + L(Q) + |P|\bigr) + |P| + |Q| \;=\; \bigl(2 L(P) + |P|\bigr) + \bigl(2 L(Q) + |Q|\bigr) + 2|P| \;\le\; |P|^2 + |Q|^2 + 2|P|\,|Q| \;=\; (|P| + |Q|)^2.
$$

Along $M \to_{S,\mathrm{lp}}^k N$, we have $|N| = |M|$ and $L(M) = L(N) + 2k \ge |M| - 1 + 2k$. Substituting into $2 L(M) + |M| \le |M|^2$ yields $4k + 3|M| - 2 \le |M|^2$ for $|M| \ge 2$ (and $k = 0$ for $|M| = 1$), which rearranges to $4k \le (|M| - 1)(|M| - 2)$ and gives (2.2). Conversely, each $N_n^{\mathrm{lp}}$ has no $\to_{S,\mathrm{lp}}$-step: this is vacuous for $n \in \{2, 3\}$, and for $N_{m+4}^{\mathrm{lp}} \equiv (S S)\,N_{m+2}^{\mathrm{lp}}$, the head has spine length $1$, the left child $S S$ is normal, and any $\to_{S,\mathrm{lp}}$-step in the right child contradicts the induction hypothesis on $N_{m+2}^{\mathrm{lp}}$. Finally, we verify by induction on $m \ge 0$ the peeling reduction $L_{m+4} \to_{S,\mathrm{lp}}^{m+1} T\,L_{m+2}$: at $m = 0$, $L_4 \equiv S S S S \to_{S,\mathrm{lp}} (S S)(S S) \equiv T\,L_2$ in $1$ step; assuming $L_{m+4} \to_{S,\mathrm{lp}}^{m+1} T\,L_{m+2}$, appending $S$ on the right gives $L_{m+5} \equiv L_{m+4} S \to_{S,\mathrm{lp}}^{m+1} (T\,L_{m+2}) S \equiv S S L_{m+2} S \to_{S,\mathrm{lp}} (S S)(L_{m+2} S) \equiv T\,L_{m+3}$ in $m + 2$ steps. Inducting on $n \ge 2$ with step-$2$ stride from $L_2 \equiv N_2^{\mathrm{lp}}$ ($0$ steps) and $L_3 \equiv N_3^{\mathrm{lp}}$ ($0$ steps), $L_{m+4} \to_{S,\mathrm{lp}}^{m+1} T\,L_{m+2} \to_{S,\mathrm{lp}}^{\lfloor m^2/4 \rfloor} T\,N_{m+2}^{\mathrm{lp}} \equiv N_{m+4}^{\mathrm{lp}}$ takes $(m + 1) + \lfloor m^2/4 \rfloor = \lfloor (m^2 + 4m + 4)/4 \rfloor = \lfloor ((m+4)-2)^2/4 \rfloor$ steps.
 $\square$

### 2.2. Acyclicity, Non-Spiralling, Flat $\{S,K\}$ Normalization, and Functional Order

Although $\mathrm{CL}(S)$ admits infinite reductions, its non-erasing binary geometry forbids both cyclic reductions and self-embedding spirals, forces unbounded leaf and redex growth along every infinite path, extends to strong normalization of Klop's flat $\{S, K\}$-terms, and bounds the functional arity of every pure-$S$ term by $3$. We formalize the classical theory of Section 5.4 of Barendregt, Endrullis, Klop, and Waldmann [4, pp. 86–90] in constructive form.

**Proposition 2.4 (Acyclicity, non-spiralling, and functional order at most $3$).** 
Let $M, N \in \mathcal{T}_S(\mathcal{V})$.

- (i) *Bergstra acyclicity and decidability of $\to_S^*$ [38, 4]:* No $M \in \mathcal{T}_S(\mathcal{V})$ satisfies $M \to_S^+ M$, and pointwise reachability $M \to_S^* N$ is constructively decidable for all $M, N \in \mathcal{T}_S(\mathcal{V})$.
- (ii) *Waldmann's no-spiral theorem and absence of reducing fixpoint combinators [66, 4]:* For every one-hole context $C[\,]$ and every $M \in \mathcal{T}_S(\mathcal{V})$, it is impossible that $M \to_S^+ C[M]$; if $C[\,] \not\equiv \square$, then $M \to_S^* C[M]$ does not hold. In particular, no $Y, X \in \mathcal{T}_S(\mathcal{V})$ satisfy $Y X \to_S^* X(Y X)$.
- (iii) *Visser–van Oostrom order-$3$ theorem [4]:* For all $M \in \mathcal{T}_S(\mathcal{V})$ and variables $x_0, x_1, x_2, x_3 \in \mathcal{V}$, there do not exist $P, Q \in \mathcal{T}_S(\mathcal{V})$ such that $M x_0 x_1 x_2 \to_S^* S P Q$. Consequently, every $M \in \mathcal{T}_S(\mathcal{V})$ has functional order $\operatorname{ord}(M) \le 3$: whenever $M x_0 x_1 x_2 x_3 \to_S^* N$, there exists $N' \in \mathcal{T}_S(\mathcal{V})$ such that $N \equiv N' x_3$ and $M x_0 x_1 x_2 \to_S^* N'$.

*Proof.* 
For (i), we record two independent constructive proofs. First, along any candidate path $M \to_S^* N$, Proposition 2.2(ii) requires $|M'| \le |N|$ at every intermediate term $M'$, while each step $M_i \to_S M_{i+1}$ strictly decreases the lexicographic pair $(|N| - |M_i|,\, \|M_i\|_{\mathrm{B}})$ (or $(|N| - |M_i|,\, L(M_i))$) by Theorem 2.3; this both forbids $M \to_S^+ M$ and bounds the finite search tree for deciding $M \to_S^* N$. Second, independently of any weight function, induct structurally on $M$ to refute $M \to_S^+ M$: atoms cannot step, and if $A B \to_S^+ A B$, either every step is non-root—decomposing into $A \to_S^+ A$ or $B \to_S^+ B$ and contradicting the induction hypothesis—or $A B \to_S^* S X Y Z$ and $(X Z)(Y Z) \to_S^* A B$, whence right-spine monotonicity (Proposition 2.2(ii)) yields the impossible chain $\operatorname{rs}(A B) \le 1 + \operatorname{rs}(Z) < 2 + \operatorname{rs}(Z) = \operatorname{rs}((X Z)(Y Z)) \le \operatorname{rs}(A B)$.

For (ii), let $\rho(Q) = 1 + \operatorname{rs}(Q)$ and consider application-labelled terms over $\{S\} \cup \mathcal{V}$ with binary operators $\{\cdot_k\}_{k \ge 1}$, mapping each $P \in \mathcal{T}_S(\mathcal{V})$ to $\overline{P}$ by labelling every subterm $U V$ as $\overline{U} \cdot_{\rho(V)} \overline{V}$. For any label cap $m \ge 1$, define Waldmann's bounded labelled rewrite system $\mathcal{R}_m$ on terms with labels in $\{1, \dots, m\}$ as the union of the contextual closures of

$$
((S \cdot_a X) \cdot_b Y) \cdot_c Z \;\to_{(5.2)}\; (X \cdot_c Z) \cdot_{1+c} (Y \cdot_c Z) \quad (1 + c \le m), \qquad
X \cdot_n Y \;\to_{(5.3)}\; X \cdot_{n+1} Y \quad (n + 1 \le m).
$$

Whenever $P \to_S Q$ and all labels in $\overline{P}, \overline{Q}$ are at most $m$, structural induction on $P \to_S Q$ shows that $\overline{P} \to_{(5.2)} K \to_{(5.3)}^* \overline{Q}$ for an intermediate labelled term $K$ (at a right-child step $U V \to_S U V'$, Proposition 2.2(ii) gives $\rho(V) \le \rho(V') \le m$, absorbed by $\rho(V') - \rho(V)$ applications of $\to_{(5.3)}$). Inverting every label $k$ to $d = m - k \in \{0, \dots, m\}$ embeds $\mathcal{R}_m$ together with direct subterm projections $(U \cdot_d V \succ_{\mathrm{RB}} U, V)$ into a single relation $\succ_{\mathrm{RB}}$ in which $(5.2)$ replaces a root operator $\cdot_d$ by $\cdot_{d'}$ ($d' < d$) applied to two $\cdot_d$-children built from proper subterms, and $(5.3)$ lowers $d$ to $d' < d$. Nested constructive accessibility induction on $d \in \mathbb{N}$ and on the accessibility of $U$ and $V$ proves that the transitive closure $\succ_{\mathrm{RB}}^+$ is well-founded (and hence irreflexive) for every $m \in \mathbb{N}$; in particular, $\mathcal{R}_m$ is constructively strongly normalizing. If $M \to_S^+ C[M]$, choosing $m$ above all canonical labels occurring along that finite reduction yields $\overline{M} \to_{\mathcal{R}_m}^+ \overline{C[M]}$, which composes with hole projections along $C[\,]$ to give a cycle in $\succ_{\mathrm{RB}}^+$, a contradiction. If $C[\,] \not\equiv \square$, then $|M| < |C[M]|$ excludes $M \equiv C[M]$ as well; specializing $M \equiv Y X$ and $C[\square] \equiv X\,\square$ refutes $Y X \to_S^* X(Y X)$ [4, Remark 15].

For (iii), let $\mathcal{W}_1 = \{P \in \mathcal{T}_S(\mathcal{V}) : \mathrm{rt}(P) \in \mathcal{V}\}$, $\mathcal{W}_2 = \{P Q : P, Q \in \mathcal{W}_1\}$, and $\mathcal{W}_3 = \{L R : L \in \mathcal{W}_2,\, R \in \mathcal{W}_1\}$. By Proposition 2.2(ii), $\mathrm{rt}$ is invariant under $\to_S$, so $\mathcal{W}_1$ is closed under $\to_S$. Closure of $\mathcal{W}_2$ under $\to_S$ follows at a root step $(S X Y) Z \to_r (X Z)(Y Z)$ from $Z \in \mathcal{W}_1$, which places both $X Z$ and $Y Z$ in $\mathcal{W}_1$. Likewise, if $((S X) Y) Z \in \mathcal{W}_3$, then $(S X) Y \in \mathcal{W}_2$ gives $S X \in \mathcal{W}_1$ and hence $X \in \mathcal{W}_1$; together with $Z \in \mathcal{W}_1$, this yields $X Z \in \mathcal{W}_2$ and $Y Z \in \mathcal{W}_1$, so $(X Z)(Y Z) \in \mathcal{W}_3$, while contextual steps preserve $\mathcal{W}_3$ because $\mathcal{W}_2$ contains only applications. Now $M x_0 x_1 x_2 \in \mathcal{W}_3$ because $M x_0, x_1, x_2 \in \mathcal{W}_1$, whereas $S P Q \equiv (S P) Q \notin \mathcal{W}_3$ because $S \notin \mathcal{W}_1$ implies $S P \notin \mathcal{W}_2$. Thus $M x_0 x_1 x_2$ never reduces to $S P Q$, so in any reduction of $(M x_0 x_1 x_2)\,x_3$ neither a root step nor a step inside $x_3$ can occur, forcing every reduct to have the form $N' x_3$ with $M x_0 x_1 x_2 \to_S^* N'$.
 $\square$

**Proposition 2.5 (Unbounded leaf and redex growth, and Klop's flat $\{S,K\}$ theorem).** 
The quantitative potential and bounded-label methods of Theorem 2.3 and Proposition 2.4 yield three further consequences [4, Remark 16 and Theorem 18, p. 89]:

- (i) *Constructive unbounded leaf count:* Let $M_0 \to_S M_1 \to_S M_2 \to_S \cdots$ be an infinite reduction in $\mathcal{T}_S(\mathcal{V})$. Define $N_0 = \|M_0\|_{\mathrm{B}}$ and $N_{b+1} = N_b + \|M_{N_b}\|_{\mathrm{B}}$ for $b \in \mathbb{N}$ (or $N'_0 = \lfloor L(M_0)/2 \rfloor + 1$ and $N'_{b+1} = N'_b + \lfloor L(M_{N'_b})/2 \rfloor + 1$). Then $|M_{N_b}| > b$ (and $|M_{N'_b}| > b$) holds for every $b \in \mathbb{N}$.
- (ii) *Unbounded contracted redex size:* In every infinite reduction $M_0 \to_S M_1 \to_S M_2 \to_S \cdots$ in $\mathcal{T}_S(\mathcal{V})$ contracting the redex sequence $R_0, R_1, R_2, \dots$, neither the canonical $\mathcal{R}_m$-labels of $M_n$ nor the leaf sizes $|R_n|$ are bounded above by any constant $B \in \mathbb{N}$.
- (iii) *Klop's strong normalization theorem for flat $\{S,K\}$-terms:* Let $(\mathcal{T}_{S,K}, \to_{S,K})$ be closed $\{S, K\}$-combinatory logic with rules $S X Y Z \to_{S,K} (X Z)(Y Z)$ and $K X Y \to_{S,K} X$. Define the class $\mathcal{F}_{S,K} \subset \mathcal{T}_{S,K}$ of *flat $\{S,K\}$-terms* inductively by $S, K \in \mathcal{F}_{S,K}$ and $P S, P K \in \mathcal{F}_{S,K}$ for $P \in \mathcal{F}_{S,K}$, and define Klop's superclass $\mathcal{SP} \supseteq \mathcal{F}_{S,K}$ inductively by $S, K \in \mathcal{SP}$ together with $P S, P K, K K P, K S P, S K P, S S P \in \mathcal{SP}$ whenever $P \in \mathcal{SP}$. Then $\mathcal{SP}$ is closed under $\to_{S,K}$, and every term in $\mathcal{SP}$ (hence every flat $\{S,K\}$-term) is constructively strongly normalizing under $\to_{S,K}$.

*Proof.* 
For (i), we verify by induction on $w \ge 1$ that whenever $\|M_k\|_{\mathrm{B}} \le w$, one has $|M_k| < |M_{k+w}|$: if $|M_k| = |M_{k+1}|$, Theorem 2.3(i) gives $\|M_{k+1}\|_{\mathrm{B}} < \|M_k\|_{\mathrm{B}} \le w$, so $\|M_{k+1}\|_{\mathrm{B}} \le w - 1$ (impossible when $w = 1$ since $\|M_{k+1}\|_{\mathrm{B}} \ge 1$, and handled by the induction hypothesis at $k + 1$ when $w \ge 2$), whereas if $|M_k| < |M_{k+1}|$, leaf monotonicity gives $|M_k| < |M_{k+1}| \le |M_{k+w}|$. Induction on $b \in \mathbb{N}$ starting from $|M_0| \ge 1$ then yields $|M_{N_b}| > b$ (and identically for $N'_b$ via (2.1)).

For (ii), if all canonical labels of $\overline{M_n}$ were bounded by $m$, Proposition 2.4(ii) would map $(M_n)_{n \ge 0}$ to an infinite $\mathcal{R}_m$-reduction, contradicting strong normalization of $\mathcal{R}_m$. Suppose next that $|R_n| \le B$ holds for all $n \ge 0$, and set $B' = \max(1, B)$. Call a labelled version $\widehat{M}$ of an unlabelled term $M \in \mathcal{T}_S(\mathcal{V})$ *validly lower-labelled* up to $B'$ if its label erasure is $M$ and every application node $U \cdot_k V$ in $\widehat{M}$ satisfies $1 \le k \le \min(\rho(V_{\mathrm{erase}}), B')$. Initializing $\widehat{M}_0$ by assigning label $1$ to every application node of $M_0$ satisfies this invariant since $1 \le \rho(V_{\mathrm{erase}})$ and $1 \le B'$. Given $\widehat{M}_n$ and a step $M_n \to_S M_{n+1}$ contracting $R_n \equiv S X Y Z$ with $|R_n| \le B \le B'$, let $\cdot_c$ be the outer label at the contracted redex in $\widehat{M}_n$. By validity, $c \le \rho(Z) = 1 + \operatorname{rs}(Z) \le |Z|$; since $1 + |Z| \le (1 + |X| + |Y|) + |Z| = |R_n| \le B'$, we have $1 + c \le B'$. Contracting that node via rule $(5.2)$ alone—without any $(5.3)$ lifts—produces a labelled term $\widehat{M}_{n+1}$ erasing to $M_{n+1}$ with all labels at most $B'$, preserving $1 \le k \le \rho(V'_{\mathrm{erase}})$ at every ancestor of a right-child step because $\rho(V_{\mathrm{erase}}) \le \rho(V'_{\mathrm{erase}})$. This yields an infinite $\to_{(5.2)}$-chain in $\mathcal{R}_{B'}$, contradicting strong normalization of $\mathcal{R}_{B'}$.

For (iii), let $\pi \colon \mathcal{T}_{S,K} \to \mathcal{T}_S$ replace every leaf $K$ by $S$, preserving total leaf count $|\pi(P)| = |P|_{S,K}$. We check by structural induction on $P \to_{S,K} Q$ with $P \in \mathcal{SP}$ that $Q \in \mathcal{SP}$ and either $|Q|_{S,K} < |P|_{S,K}$ or $(|Q|_{S,K} = |P|_{S,K} \text{ and } \pi(P) \to_{S,\mathrm{lp}} \pi(Q))$. At a root $K$-contraction $(K X) Y \to_{S,K} X$, inversion on $(K X) Y \in \mathcal{SP}$ forces $X \in \{S, K\} \subset \mathcal{SP}$ and $|X|_{S,K} = 1 < 2 + |Y|_{S,K} = |(K X) Y|_{S,K}$. At a root $S$-contraction $((S X) Y) Z \to_{S,K} (X Z)(Y Z)$, none of the four prefix constructors $K K M, K S M, S K M, S S M$ matches $((S X) Y) Z$ (whose left-left grandchild is $S X$ rather than an atom), so $Z \in \{S, K\}$ and $(S X) Y \in \mathcal{SP}$; inverting $(S X) Y \in \mathcal{SP}$ in turn forces $X \in \{S, K\}$ and $Y \in \mathcal{SP}$. Consequently, $Y Z \in \mathcal{SP}$ and $X Z \in \{K K, K S, S K, S S\}$, placing $(X Z)(Y Z) \in \mathcal{SP}$ with $|(X Z)(Y Z)|_{S,K} = |((S X) Y) Z|_{S,K}$ (since $|Z|_{S,K} = 1$) and $\pi(((S X) Y) Z) \to_r (\pi(X)\,S)(\pi(Y)\,S) \equiv \pi((X Z)(Y Z))$. Left-child steps occur only inside $P S$ or $P K$ (since $K K, K S, S K, S S$ are normal), and right-child steps occur only inside $A B M$ for $A, B \in \{S, K\}$ (since $S$ and $K$ are normal), both preserving $\mathcal{SP}$ and the disjunction by the induction hypothesis. Nested well-founded induction on $|P|_{S,K} \in \mathbb{N}$ and $\|\pi(P)\|_{\mathrm{B}} \in \mathbb{N}$ (via Theorem 2.3(i)) establishes constructive strong normalization for every $P \in \mathcal{SP}$, and $\mathcal{F}_{S,K} \subseteq \mathcal{SP}$ completes the proof.
 $\square$

### 2.3. Head Reduction, Root Normal Forms, and Böhm Trees

Every closed $S$-term $M \in \mathcal{T}_S$ decomposes uniquely along its left spine as $M \equiv S M_1 M_2 \cdots M_k$ where $k = \operatorname{ls}(M) \ge 0$. If $k \le 2$ (that is, $M \equiv S$, $M \equiv S M_1$, or $M \equiv S M_1 M_2$), no contraction can occur at or along the left spine of $M$; if $k \ge 3$, the unique redex $S M_1 M_2 M_3$ at the top of the left spine is the *head redex* of $M$.

**Definition 2.6 (Head normal forms, root normal forms, Böhm trees, and productivity).** 
On closed $S$-terms $M, N \in \mathcal{T}_S$:

- (i) *Head reduction* $\to_h$ contracts the unique head redex along the left spine: $S X Y Z \to_h (X Z)(Y Z)$, and $P Q \to_h P' Q$ whenever $P \to_h P'$. A term $M \in \mathcal{T}_S$ is in *head normal form* ($M \in \mathrm{HNF}$) if $\operatorname{ls}(M) \le 2$, and is *solvable* or *head-normalizing* ($M \in \mathrm{HN}$) if $M \to_S^* H$ for some $H \in \mathrm{HNF}$; otherwise $M$ is *unsolvable* ($M \in \mathcal{T}_S \setminus \mathrm{HN}$).
- (ii) A term $M \in \mathcal{T}_S$ is a *root normal form* ($M \in \mathrm{RNF}$) if there do not exist $X, Y, Z \in \mathcal{T}_S$ such that $M \to_S^* S X Y Z$. Following Berarducci [9, 8], $M$ is *mute* (or root-active) if $M$ cannot reduce to any root normal form.
- (iii) Following Böhm [13] and Barendregt [1], the *Böhm tree* $\operatorname{BT}(M)$ is the potentially infinite labelled tree over signature $\{S, \cdot, \bot\}$ defined coinductively by $\operatorname{BT}(M) = \bot$ if $M \notin \mathrm{HN}$, and

$$
\operatorname{BT}(M) \;=\; S \qquad (M \to_S^* S), \qquad
\operatorname{BT}(M) \;=\; S\,\operatorname{BT}(M_1) \qquad (M \to_S^* S M_1), \qquad
\operatorname{BT}(M) \;=\; S\,\operatorname{BT}(M_1)\,\operatorname{BT}(M_2) \qquad (M \to_S^* S M_1 M_2).
$$

  Similarly, the *Berarducci tree* $\operatorname{BeT}(M)$ unfolds $M$ at every node having a root normal form ($S$ if $M \to_S^* S$, or $\operatorname{BeT}(P) \cdot \operatorname{BeT}(Q)$ if $M \to_S^* P Q \in \mathrm{RNF}$) and places $\bot$ at mute subterms.
- (iv) To reason constructively about $\bot$-occurrence without coinductive choice, define the inductive finite-depth predicate $\bot_d(M)$ ($d \in \mathbb{N}$, read "$\operatorname{BT}(M)$ contains $\bot$ at tree depth at most $d$") by four rules: (a) if $M \notin \mathrm{HN}$, then $\bot_d(M)$ holds for all $d$; (b) if $M \to_S^* S X$ and $\bot_d(X)$, then $\bot_{d+1}(M)$; (c) if $M \to_S^* S X Y$ and $\bot_d(X)$, then $\bot_{d+1}(M)$; and (d) if $M \to_S^* S X Y$ and $\bot_d(Y)$, then $\bot_{d+1}(M)$. A closed $S$-term $M \in \mathcal{T}_S$ is *productive* ($M \in \mathrm{Prod}$) if $\neg\bot_d(M)$ holds for all $d \in \mathbb{N}$ [26, 4].

Observe that $\mathrm{HNF}$ is closed under arbitrary reductions $\to_S^*$: if $\operatorname{ls}(H) \le 2$ and $H \to_S H'$, then either $H \equiv S X \to_S S X'$ or $H \equiv S X Y \to_S S X' Y$ or $S X Y'$, preserving $\operatorname{ls}(H') = \operatorname{ls}(H) \le 2$.

**Lemma 2.7 (Conversion invariance of $\mathrm{HN}$ and $\mathrm{Prod}$).** 
For all $M, N \in \mathcal{T}_S$ satisfying $M =_S N$, one has $M \in \mathrm{HN}$ if and only if $N \in \mathrm{HN}$, $\bot_d(M)$ if and only if $\bot_d(N)$ for every $d \in \mathbb{N}$, and hence $M \in \mathrm{Prod}$ if and only if $N \in \mathrm{Prod}$.

*Proof.* 
By Proposition 2.2(i), it suffices to show that $M \to_S^* N$ implies the equivalences $M \in \mathrm{HN}$ if and only if $N \in \mathrm{HN}$, and $\bot_d(M)$ if and only if $\bot_d(N)$. First, if $N \to_S^* H$ with $\operatorname{ls}(H) \le 2$, transitivity gives $M \to_S^* H$, so $N \in \mathrm{HN}$ implies $M \in \mathrm{HN}$. Conversely, if $M \to_S^* H$ with $\operatorname{ls}(H) \le 2$, Church–Rosser yields $U$ with $N \to_S^* U$ and $H \to_S^* U$; since $\operatorname{ls} \le 2$ is preserved under $\to_S^*$, we have $\operatorname{ls}(U) \le 2$ and $N \in \mathrm{HN}$.

Next we prove by induction on $d$ that $M \to_S^* N$ implies $\bot_d(M)$ if and only if $\bot_d(N)$. At depth $d = 0$, the predicate $\bot_0(P)$ holds if and only if $P \notin \mathrm{HN}$, which is already invariant. Assume equivalence holds at depth $d$. If $\bot_{d+1}(N)$ holds via $N \to_S^* S X$ with $\bot_d(X)$ (or $N \to_S^* S X Y$ with $\bot_d(X)$ or $\bot_d(Y)$), then $M \to_S^* N \to_S^* S X$ (or $S X Y$) derives $\bot_{d+1}(M)$. Conversely, suppose $\bot_{d+1}(M)$ holds. If $M \notin \mathrm{HN}$, then $N \notin \mathrm{HN}$ and $\bot_{d+1}(N)$ holds by rule (a). If $M \to_S^* S X$ with $\bot_d(X)$, Church–Rosser on $M \to_S^* N$ and $M \to_S^* S X$ yields $U$ with $N \to_S^* U$ and $S X \to_S^* U$; inversion on $S X \to_S^* U$ forces $U \equiv S X'$ with $X \to_S^* X'$, so the induction hypothesis gives $\bot_d(X')$ and hence $\bot_{d+1}(N)$. The remaining two cases where $M \to_S^* S X Y$ follow identically because $S X Y \to_S^* U$ forces $U \equiv S X' Y'$ with $X \to_S^* X'$ and $Y \to_S^* Y'$. Negating the existence of $d \in \mathbb{N}$ satisfying $\bot_d(-)$ yields $M \in \mathrm{Prod}$ if and only if $N \in \mathrm{Prod}$.
 $\square$

### 2.4. Bottom-Up Tree Automata, Finite $S$-Algebras, and Ongoing Simulation

Because $\mathcal{T}_S$ is the set of ground terms over a signature consisting of one nullary constant $S$ and one binary operator $\cdot$, deterministic bottom-up tree automata on $\mathcal{T}_S$ coincide with finite pointed magmas equipped with an accepting subset [25, 4].

**Definition 2.8 (Bottom-up tree automata and finite $S$-algebras).** 
A *deterministic bottom-up tree automaton* (DTA) over $\mathcal{T}_S$ is a quadruple $\mathcal{A} = (Q, q_0, \odot, F)$, where $Q$ is a finite nonempty set of states, $q_0 \in Q$ is the leaf constant ($q_0 = \llbracket S \rrbracket_{\mathcal{A}}$), $\odot \colon Q \times Q \to Q$ is the binary transition operation, and $F \subseteq Q$ is the accepting subset. The evaluation morphism $\llbracket - \rrbracket_{\mathcal{A}} \colon \mathcal{T}_S \to Q$ is defined recursively by

$$
\llbracket S \rrbracket_{\mathcal{A}} \;=\; q_0, \qquad \llbracket M N \rrbracket_{\mathcal{A}} \;=\; \llbracket M \rrbracket_{\mathcal{A}} \odot \llbracket N \rrbracket_{\mathcal{A}},
$$

and the recognized regular tree language is $L(\mathcal{A}) = \{M \in \mathcal{T}_S : \llbracket M \rrbracket_{\mathcal{A}} \in F\}$. Clearly $\llbracket M \rrbracket_{\mathcal{A}}$ is computable in a single bottom-up pass of $2|M| - 1$ table lookups ($O(|M|)$ time). We call $\mathcal{A}$ a *finite $S$-algebra* if $\odot$ satisfies the combinatory identity

$$
((q_0 \odot x) \odot y) \odot z \;=\; (x \odot z) \odot (y \odot z) \qquad (\text{for all } x, y, z \in Q). \tag{2.3}
$$

Because $\llbracket - \rrbracket_{\mathcal{A}}$ is compositional on application contexts, (2.3) implies $\llbracket M \rrbracket_{\mathcal{A}} = \llbracket N \rrbracket_{\mathcal{A}}$ whenever $M =_S N$, making $L(\mathcal{A})$ invariant under unrestricted pure-$S$ conversion.

Building on classical criteria for non-trivial simulation and encoding complexity [22, 28, 35] together with Priese [51], van Emde Boas [62], Neary and Woods [45], and Wolfram [71], we formalize ongoing simulation of a deterministic computation system in $\mathrm{CL}(S)$ with explicit sub-universal guards on all boundary maps.

**Definition 2.9 (Ongoing pure-$S$ simulation with sub-universal boundary maps).** 
Let $\mathcal{S}$ be a deterministic computational model with instance set $\mathcal{I}$, step relation $\vdash_{\mathcal{S}}$, halting predicate $\mathrm{Halts}_{\mathcal{S}}(I)$, and partial output map $\operatorname{out}_{\mathcal{S}} \colon \mathcal{I} \rightharpoonup \Sigma^*$. An *ongoing selected-path simulation* of $\mathcal{S}$ in $\mathrm{CL}(S)$ is a quadruple $(\mathcal{E}, \sigma, \mathcal{H}, \mathcal{D})$ consisting of:

- (i) a total polynomial-time (or logspace) *encoder* $\mathcal{E} \colon \mathcal{I} \to \mathcal{T}_S$ mapping each instance $I \in \mathcal{I}$ to a finite closed $S$-term $T_0 = \mathcal{E}(I)$ of size $|T_0| \le \mathrm{poly}(\|I\|)$;
- (ii) a fixed stateless *single-step selector* $\sigma \colon \mathcal{T}_S \to \mathcal{T}_S \cup \{\mathsf{normal}\}$ realized by a finite-state tree-walking automaton that resets to a unique initial control state at the root of $T$ before each step, halts on every $T \in \mathcal{T}_S$ in $O(|T|)$ cursor transitions, and satisfies $T \to_S \sigma(T)$ whenever $\sigma(T) \in \mathcal{T}_S$;
- (iii) a *halting detector* $\mathcal{H} = (Q_{\mathrm{halt}}, q_0, \odot_{\mathrm{halt}}, F_{\mathrm{halt}})$ given by a fixed deterministic bottom-up finite tree automaton ($L(\mathcal{H}) \in \mathrm{REG}$); and
- (iv) a total polynomial-time (in $|T|$) read-only *output decoder* $\mathcal{D} \colon \mathcal{T}_S \to \Sigma^* \cup \{\bot\}$,

such that along the iterated reduction trajectory $T_0 = \mathcal{E}(I)$ and $T_{k+1} = \sigma(T_k)$ (defined while $\sigma(T_k) \in \mathcal{T}_S$), one has $\mathrm{Halts}_{\mathcal{S}}(I)$ if and only if there exists $k \ge 0$ with $T_k \in L(\mathcal{H})$, and every such step $k$ satisfies $\mathcal{D}(T_k) = \operatorname{out}_{\mathcal{S}}(I)$. Because $\mathcal{E}$ is total polynomial-time (indeed logspace-constructible up to tree output), $\mathcal{H}$ has $O(1)$ finite memory, and $\mathcal{D}$ terminates in bounded polynomial time on every bare tree $T \in \mathcal{T}_S$, none of the boundary maps $(\mathcal{E}, \mathcal{H}, \mathcal{D})$ can decide any $\Sigma_1^0$-complete problem on its own.

### 2.5. Open Spirals and Structural Obstructions to Conjecture 17

Waldmann's Theorem 14 (Proposition 2.4(ii)) rules out self-embedding reductions $M \to_S^+ C[M]$ for identical copies of $M$, whether closed or open. When $M \in \mathcal{T}_S(\mathcal{V})$ contains variables, however, one may ask whether $M$ can self-embed modulo a non-trivial substitution $\sigma \colon \mathcal{V} \to \mathcal{T}_S(\mathcal{V})$. In Section 5.4 of [4, Definition 11(iii) and Conjecture 17, pp. 86, 89], Barendregt, Endrullis, Klop, and Waldmann conjectured that no such open spiralling $S$-term exists. While Conjecture 17 in full generality remains open, we establish a suite of constructive structural obstructions that eliminate broad classes of substitutions, contexts, variable-occurrence patterns, and short reduction lengths, while isolating a parametric self-embedding near-miss native to pure $\mathrm{CL}(S)$.

**Definition 2.10 (Open spiralling, iterated substitutions, and variable-spine depth).** 
Let $\sigma \colon \mathcal{V} \to \mathcal{T}_S(\mathcal{V})$ be a substitution. Its *iterates* $\sigma^n \colon \mathcal{V} \to \mathcal{T}_S(\mathcal{V})$ ($n \in \mathbb{N}$) are defined by $\sigma^0(x) \equiv x$ and $\sigma^{n+1}(x) \equiv (\sigma(x))^{\sigma^n}$, satisfying $(M^\sigma)^{\sigma^n} \equiv M^{\sigma^{n+1}}$ for all $M \in \mathcal{T}_S(\mathcal{V})$. A term $M \in \mathcal{T}_S(\mathcal{V})$ *open-spirals* via a one-hole context $C[\,]$ and substitution $\sigma$ if $M \to_S^+ C[M^\sigma]$; *Conjecture 17* of [4] asserts that $\neg(M \to_S^+ C[M^\sigma])$ holds for all $M \in \mathcal{T}_S(\mathcal{V})$, $C[\,]$, and $\sigma$.

A *left-spine context* is generated by $L[\,] ::= \square \mid (L[\,]\,R)$ ($R \in \mathcal{T}_S(\mathcal{V})$). For each variable $x \in \mathcal{V}$, the *maximum $x$-tailed right-spine depth* $\mathrm{maxRS}_x \colon \mathcal{T}_S(\mathcal{V}) \to \mathbb{N}$ is defined recursively by $\mathrm{maxRS}_x(a) = 0$ on atoms $a \in \{S\} \cup \mathcal{V}$ and

$$
\mathrm{maxRS}_x(P Q) \;=\; \max\bigl(\delta_{\mathrm{rt}(Q), x}\,(1 + \operatorname{rs}(Q)),\; \mathrm{maxRS}_x(P),\; \mathrm{maxRS}_x(Q)\bigr),
$$

where $\delta_{\mathrm{rt}(Q), x} = 1$ if $\mathrm{rt}(Q) \equiv x$ and $0$ otherwise.

**Proposition 2.11 (Divergence projection, minimal counterexample geometry, and $8$-leaf open threshold).** 
Let $M \in \mathcal{T}_S(\mathcal{V})$.

- (i) *Universal substitution divergence and minimal spine geometry:* If $M \to_S^+ C[M^\sigma]$, then $M \notin \mathrm{SN}$, and $M^\tau \notin \mathrm{SN}$ holds for every substitution $\tau \colon \mathcal{V} \to \mathcal{T}_S(\mathcal{V})$ (in particular for the closing projection $\tau_S(v) \equiv S$, which satisfies $|M^{\tau_S}| = |M|$). Moreover, if $M$ is leaf-minimal among open-spiralling terms, then $M \to_S^+ C[M^\sigma]$ performs at least one root contraction, $\mathrm{hd}(M) \equiv S$, and $\operatorname{ls}(M) \ge 3$.
- (ii) *Exact $8$-leaf threshold for open non-normalization:* Every open term $M \in \mathcal{T}_S(\mathcal{V}) \setminus \mathcal{T}_S$ containing at least one variable and having leaf size $|M| \le 7$ lies in $\mathrm{SN}$ (and therefore cannot open-spiral). At leaf size $|M| = 8$, non-normalizing open $S$-terms appear both by wrapping $7$-leaf closed divergers (such as $S(S S)S S S S x$) and as genuinely open divergers whose proper closed subterms all normalize, such as $S A S (S(S x))$.

*Proof.* 
For (i), compatibility of $\to_S^+$ with substitutions and contexts implies that $M_0 \equiv M$ and $M_{n+1} \equiv C[M_n^\sigma]$ satisfy $M_n \to_S^+ M_{n+1}$ for all $n \in \mathbb{N}$, refuting constructive accessibility of $M \in \mathrm{SN}$. Because $P \to_S Q$ implies $P^\tau \to_S Q^\tau$, accessibility of $M^\tau$ pulls back by structural induction on the accessibility witness to accessibility of $M$, whence $M^\tau \notin \mathrm{SN}$. Suppose next that $M$ has minimal leaf size among all open-spiralling terms and $M \to_S^+ C[M^\sigma]$ uses no root contraction. Then $M \equiv P Q$ with $P \to_S^* P'$, $Q \to_S^* Q'$, and $P' Q' \equiv C[P^\sigma Q^\sigma]$. If $C[\,] \equiv \square$, then $P' \equiv P^\sigma$, $Q' \equiv Q^\sigma$, and at least one of $P \to_S^+ P^\sigma$ or $Q \to_S^+ Q^\sigma$ holds, yielding an open spiral on a proper subterm of $M$. If $C[\,] \equiv (C_1[\,]\,R)$, then $P^\sigma Q^\sigma \trianglelefteq P'$, so $P^\sigma \triangleleft P'$, say $P' \equiv C_a[P^\sigma]$ with $C_a[\,] \not\equiv \square$; since $|P| \le |P^\sigma| < |C_a[P^\sigma]| = |P'|$, the reduction $P \to_S^* P'$ must have positive length $P \to_S^+ C_a[P^\sigma]$, again contradicting leaf-minimality of $M$ (and symmetrically when $C[\,] \equiv (L\,C_2[\,])$). Thus $M \to_S^+ C[M^\sigma]$ performs a root contraction. Because any step from a variable-headed term preserves its variable head and prevents root contractions, $\mathrm{hd}(M) \equiv S$; similarly, if $\mathrm{hd}(M) \equiv S$ and $\operatorname{ls}(M) \le 2$, every step preserves $\mathrm{hd} \equiv S$ and $\operatorname{ls} \le 2$, ruling out root contractions and forcing $\operatorname{ls}(M) \ge 3$.

For (ii), let $M \in \mathcal{T}_S(\mathcal{V}) \setminus \mathcal{T}_S$ have $|M| \le 7$, and suppose toward a contradiction that $M \notin \mathrm{SN}$. By pullback under $\tau_S(v) \equiv S$, the closed projection $M^{\tau_S} \in \mathcal{T}_S$ satisfies $|M^{\tau_S}| = |M| \le 7$ and $M^{\tau_S} \notin \mathrm{SN}$. As shown by Duboué [2] and verified in Section 9, every closed $S$-term of leaf size at most $6$ normalizes, and at leaf size $7$ the only closed non-normalizing terms are $X_1 \equiv S(S S)S S S S$ and $X_2 \equiv S S S(S S)S S$. Identifying all variables of $M$ to $x_0$ and substituting $S$ for all but one occurrence of $x_0$ yields a single-variable $7$-leaf term $M_1(x_0) \notin \mathrm{SN}$ obtained from $X_1$ or $X_2$ by replacing one leaf $S$ with $x_0$. Direct normalization of all $14$ single-leaf variable replacements of $X_1$ and $X_2$ shows that the $7$ replacements of $X_1$ reach normal form in $0, 1, 2, 3, 4, 8, 14$ leftmost-outermost steps respectively, and those of $X_2$ reach normal form in $0, 1, 4, 2, 3, 7, 13$ steps, a contradiction. At $|M| = 8$, the term $X_1 x_0$ inherits every infinite reduction of $X_1$. For the genuinely open $8$-leaf term $S A S (S(S x_0))$, set $K \equiv S(S(S x_0))$ and let $\mathcal{G} \subset \mathcal{T}_S(\mathcal{V})$ be generated inductively by $K \in \mathcal{G}$ and $U V \in \mathcal{G}$ for $U, V \in \mathcal{G}$. Two contractions give $S A S (S(S x_0)) \to_S A(S(S x_0))\,K \to_S K K K \in \mathcal{G}$. Moreover, for any $U_1, U_2 \in \mathcal{G}$, three contractions on $K U_1 U_2 \equiv S(S(S x_0))\,U_1\,U_2$ yield

$$
K U_1 U_2 \;\to_S\; \bigl(S(S x_0)\,U_2\bigr)(U_1 U_2) \;\to_S\; \bigl(S x_0\,(U_1 U_2)\bigr)\bigl(U_2(U_1 U_2)\bigr) \;\to_S\; \bigl(x_0(U_2(U_1 U_2))\bigr)\Bigl((U_1 U_2)\bigl(U_2(U_1 U_2)\bigr)\Bigr),
$$

whose right factor $(U_1 U_2)(U_2(U_1 U_2)) \in \mathcal{G}$ again has at least two $\mathcal{G}$-arguments along its left spine above $K$, generating an infinite reduction; hence $S A S (S(S x_0)) \notin \mathrm{SN}$ by Proposition 2.2(iii).
 $\square$

Our next theorem eliminates the ambient context $C[\,]$ via a constructive step-indexed dependency-pair extraction and combines it with weighted right-spine path orderings to restrict the right-spine action of any candidate substitution $\sigma$.

**Theorem 2.12 (Right-spine orbit obstruction, weighted Waldmann criterion, and self-right-tail theorem).** 
Let $M \in \mathcal{T}_S(\mathcal{V})$, let $C[\,]$ be a one-hole context, and let $\sigma \colon \mathcal{V} \to \mathcal{T}_S(\mathcal{V})$ be a substitution.

- (i) *Bounded right-spine orbits and weighted right-spine LPO:* If there exists $R \in \mathbb{N}$ such that $\operatorname{rs}(\sigma^n(x)) \le R$ for all $n \in \mathbb{N}$ and all $x \in \mathrm{Vars}(M)$, then $\neg(M \to_S^+ C[M^\sigma])$. Likewise, given weights $w \colon \mathcal{V} \to \mathbb{N}$, define $\rho_w(S) = 1$, $\rho_w(x) = w(x)$, and $\rho_w(P Q) = 1 + \rho_w(Q)$; if $\rho_w(\sigma(x)) \le w(x)$ holds for all $x \in \mathrm{Vars}(M)$, then $\neg(M \to_S^+ C[M^\sigma])$. In particular, $\neg(M \to_S^+ C[M^\sigma])$ holds whenever every $x \in \mathrm{Vars}(M)$ satisfies $\mathrm{rt}(\sigma(x)) \equiv S$ (all $S$-tailed and closed substitutions) or $\operatorname{rs}(\sigma(x)) = 0$ (all variable renamings and $S$-erasures).
- (ii) *Dependency-pair self-right-tail theorem:* If $M \to_S^+ C[M^\sigma]$, then there exists a variable $x \in \mathrm{Vars}(M)$ satisfying both

$$
\mathrm{rt}(\sigma(x)) \;\equiv\; x \qquad \text{and} \qquad \operatorname{rs}(\sigma(x)) \;\ge\; 1. \tag{2.4}
$$

  Equivalently, if no variable in $\mathrm{Vars}(M)$ is a positive right-spine self-loop of $\sigma$, then $\neg(M \to_S^+ C[M^\sigma])$. In particular, $\neg(M \to_S^+ C[M^\sigma])$ holds whenever $\mathrm{rt}(\sigma(x)) \not\equiv x$ for all $x \in \mathrm{Vars}(M)$ (eliminating all cyclic right-spine permutations of period $p \ge 2$), and every single-variable open spiral $M(x) \to_S^+ C[M(\sigma(x))]$ forces $x \in \mathrm{Vars}(M)$, $\mathrm{rt}(\sigma(x)) \equiv x$, and $\operatorname{rs}(\sigma(x)) \ge 1$.

*Proof.* 
For (i), observe first that $P \to_S^* Q$ implies $\mathrm{Vars}(Q) \subseteq \mathrm{Vars}(P)$; hence if $M \to_S^+ C[M^\sigma]$, every $x \in \mathrm{Vars}(M)$ satisfies $\mathrm{Vars}(\sigma(x)) \subseteq \mathrm{Vars}(M^\sigma) \subseteq \mathrm{Vars}(C[M^\sigma]) \subseteq \mathrm{Vars}(M)$, so $\mathrm{Vars}(M)$ is $\sigma$-closed. Under the uniform orbit bound $\operatorname{rs}(\sigma^n(x)) \le R$ on $\mathrm{Vars}(M)$, set $L = R + \max_{x \in \mathrm{Vars}(M)} \max\mathrm{label}(\overline{\sigma(x)})$, where $\overline{P}$ is the canonical $\rho$-labelling from Proposition 2.4(ii). Because $\rho(U^\tau) \le \rho(U) + R$ whenever $\operatorname{rs}(\tau(v)) \le R$ on $\mathrm{Vars}(U)$, induction on $n$ shows that $\max\mathrm{label}(\overline{\sigma^n(x)}) \le L$ for all $n \in \mathbb{N}$ and $x \in \mathrm{Vars}(M)$. Let $B_0$ be the maximum canonical label occurring along the finite reduction $M \to_S^+ C[M^\sigma]$, and set $B = \max(B_0 + R, L)$. Substituting $\sigma^n$ across $M \to_S^+ C[M^\sigma]$ produces reductions $M^{\sigma^n} \to_S^+ C^{\sigma^n}[M^{\sigma^{n+1}}]$ whose canonical labels never exceed $B$; composing with hole projections along $C^{\sigma^n}[\,]$ yields an infinite chain in the $B$-inverted relation $\succ_{\mathrm{RB}}^+$, contradicting its constructive well-foundedness established in Proposition 2.4(ii). For the weighted criterion, merge $S$ and all variables into a single leaf symbol $\bullet$ and label each application $U V$ by $\rho_w(V)$. When $\rho_w(\sigma(x)) \le w(x)$ on $\mathrm{Vars}(M)$, structural induction gives $\rho_w(N^\sigma) \le \rho_w(N)$ for every $N \trianglelefteq M$, so the $B$-inverted leaf-merged representation of $M^\sigma$ reduces via label-lifting, subterm projection (taking any $\sigma(x)$ to $\bullet$), and congruence to that of $M$, creating a cycle in the leaf-merged analogue of $\succ_{\mathrm{RB}}^+$ whenever $M \to_S^+ C[M^\sigma]$. Choosing $w(x) = 1 + \operatorname{rs}(\sigma(x))$ yields $\rho_w(\sigma(x)) = 1 + \operatorname{rs}(\sigma(x)) = w(x)$ when $\mathrm{rt}(\sigma(x)) \equiv S$, and choosing $w(x) = 1$ yields $\rho_w(\sigma(x)) = 1$ when $\operatorname{rs}(\sigma(x)) = 0$.

For (ii), fix $\sigma$ and define the dependency-pair relation $U \Rightarrow_{\mathcal{DP}} V$ inductively by the base clause $U \to_{\mathrm{nr}}^* V$ and the three step clauses: whenever $U \to_{\mathrm{nr}}^* S X Y Z$, one has $U \Rightarrow_{\mathcal{DP}} V$ if $(X Z)(Y Z) \Rightarrow_{\mathcal{DP}} V$ (clause $\mathrm{dp}_1$), $X Z \Rightarrow_{\mathcal{DP}} V$ (clause $\mathrm{dp}_2$), or $Y Z \Rightarrow_{\mathcal{DP}} V$ (clause $\mathrm{dp}_3$). We first prove by strong induction on $n \in \mathbb{N}$ that whenever $T \to_S^n C'[V]$, either there exist $n' \le n$, a proper subterm $U \triangleleft T$, and a context $C''[\,]$ with $U \to_S^{n'} C''[V]$, or else $T \Rightarrow_{\mathcal{DP}} V$. If $T \to_S^n C'[V]$ uses no root steps, then either $C'[\,] \equiv \square$ (giving $T \to_{\mathrm{nr}}^* V$, hence $T \Rightarrow_{\mathcal{DP}} V$) or $T \equiv T_1 T_2$ with $C'[\,] \equiv (C_1[\,]\,R)$ or $(L\,C_2[\,])$, in which case non-root decomposition projects directly to $T_1 \to_S^{n_1} C_1[V]$ or $T_2 \to_S^{n_2} C_2[V]$ ($n_i \le n$). Otherwise split at the first root step $T \to_{\mathrm{nr}}^k S X Y Z \to_r (X Z)(Y Z) \to_S^m C'[V]$ with $k + 1 + m = n$ ($T \equiv T_1 T_2$, $T_1 \to_S^{k_1} S X Y$, $T_2 \to_S^{k_2} Z$, $k_1 + k_2 = k$). Applying the induction hypothesis to $(X Z)(Y Z) \to_S^m C'[V]$ ($m < n$), either $(X Z)(Y Z) \Rightarrow_{\mathcal{DP}} V$ (giving $T \Rightarrow_{\mathcal{DP}} V$ via $\mathrm{dp}_1$), or some $U_1 \triangleleft (X Z)(Y Z)$ satisfies $U_1 \to_S^{m_1} C_1[V]$ ($m_1 \le m$). If $U_1 \trianglelefteq X, Y$, or $Z$, embedding $U_1 \to_S^{m_1} C_1[V]$ inside $S X Y$ or $Z$ and prepending $T_1 \to_S^{k_1} S X Y$ or $T_2 \to_S^{k_2} Z$ lifts the reduction to $T_1$ or $T_2 \triangleleft T$ in at most $k + m < n$ steps; if instead $U_1 \equiv X Z$ or $U_1 \equiv Y Z$, a second appeal to the induction hypothesis on $U_1 \to_S^{m_1} C_1[V]$ ($m_1 \le m < n$) either yields $U_1 \Rightarrow_{\mathcal{DP}} V$ (giving $T \Rightarrow_{\mathcal{DP}} V$ via $\mathrm{dp}_2$ or $\mathrm{dp}_3$) or locates $U_2 \triangleleft U_1$, so $U_2 \trianglelefteq X, Y$, or $Z$, lifting again to $T_1$ or $T_2 \triangleleft T$.

Now let $M$ be leaf-minimal among terms open-spiralling under the fixed substitution $\sigma$, with $M \to_S^n C[M^\sigma]$ ($n \ge 1$). If some proper subterm $U \triangleleft M$ ($M \equiv D[U]$, $D[\,] \not\equiv \square$) satisfied $U \to_S^{n'} C'[M^\sigma] \equiv (C' \circ D^\sigma)[U^\sigma]$, then $|U| < |M| \le |M^\sigma| \le |(C' \circ D^\sigma)[U^\sigma]|$ would force $n' \ge 1$, contradicting leaf-minimality of $M$. Therefore $M \Rightarrow_{\mathcal{DP}} M^\sigma$. Every $\mathcal{DP}$-transition preserves $\mathrm{rt}$ ($\mathrm{rt}((X Z)(Y Z)) \equiv \mathrm{rt}(X Z) \equiv \mathrm{rt}(Y Z) \equiv \mathrm{rt}(Z) \equiv \mathrm{rt}(S X Y Z)$) and is non-decreasing in $\operatorname{rs}$, while any derivation using $\mathrm{dp}_1$ at least once satisfies $\operatorname{rs}(M) < \operatorname{rs}(M^\sigma)$ strictly because $\operatorname{rs}((X Z)(Y Z)) = 2 + \operatorname{rs}(Z) > 1 + \operatorname{rs}(Z) \ge \operatorname{rs}(U)$. Suppose $M \Rightarrow_{\mathcal{DP}} M^\sigma$ used only the base clause, $\mathrm{dp}_2$, and $\mathrm{dp}_3$. By Proposition 2.11(i) (or Proposition 2.4(ii) on atoms), $M \equiv A_0 B_0$ is an application. Inducting along a $\mathrm{dp}_1$-free chain from $A_0 B_0$ to $A_0^\sigma B_0^\sigma$ shows that either $A_0 \to_S^* A_0^\sigma$ and $B_0 \to_S^* B_0^\sigma$ (in the base clause), or $A_0 \to_S^* D[A_0^\sigma]$ for a non-empty context $D[\,] \not\equiv \square$ (since $A_0 \to_S^* S X Y$ embeds any target reached from $X$ or $Y$ strictly inside $(S\,\square)\,Y$ or $(S X)\,\square$). Both cases are impossible: $A_0 \to_S^* D[A_0^\sigma]$ forces $A_0 \to_S^+ D[A_0^\sigma]$ by $|A_0| < |D[A_0^\sigma]|$, contradicting leaf-minimality of $M$, while $A_0 \to_S^* A_0^\sigma$ and $B_0 \to_S^* B_0^\sigma$ either give $M^\sigma \equiv M$ (contradicting Proposition 2.4(ii) on $M \to_S^+ C[M]$) or yield $A_0 \to_S^+ A_0^\sigma$ or $B_0 \to_S^+ B_0^\sigma$, again contradicting leaf-minimality of $M$. Thus $\mathrm{dp}_1$ must occur, giving $\mathrm{rt}(M) \equiv \mathrm{rt}(M^\sigma)$ and $\operatorname{rs}(M) < \operatorname{rs}(M^\sigma)$. If $\mathrm{rt}(M) \equiv S$, then $\operatorname{rs}(M^\sigma) = \operatorname{rs}(M)$, a contradiction. Hence $\mathrm{rt}(M) \equiv x$ for some $x \in \mathrm{Vars}(M)$, whence $\mathrm{rt}(M^\sigma) \equiv \mathrm{rt}(\sigma(x))$ and $\operatorname{rs}(M^\sigma) = \operatorname{rs}(M) + \operatorname{rs}(\sigma(x))$, forcing $\mathrm{rt}(\sigma(x)) \equiv x$ and $\operatorname{rs}(\sigma(x)) \ge 1$.
 $\square$

Even when $\sigma$ admits positive right-spine self-loops satisfying (2.4), four further structural laws rule out empty and left-spine contexts, non-duplicating counter substitutions, left-only variable patterns, and $1$- or $2$-step loops universally across $\mathcal{T}_S(\mathcal{V})$, while explaining how pure $\mathrm{CL}(S)$ nonetheless realizes parametric open self-reproduction. In part (i) below, we invoke Waldmann's top-termination theorem and the open head-step potential $\nu_{\mathrm{HN}}$, which are proved independently in Section 6 (Theorem 6.9) using only Subsection 2.1 and Proposition 2.4(i).

**Theorem 2.13 (Unconditional context/short-loop obstructions, multiplicity–spine coupling, and pure-$\mathrm{CL}(S)$ near-miss).** 
Let $M \in \mathcal{T}_S(\mathcal{V})$, let $C[\,]$ be a one-hole context, let $L[\,]$ be a left-spine context, and let $\sigma \colon \mathcal{V} \to \mathcal{T}_S(\mathcal{V})$ be an arbitrary substitution.

- (i) *Absence of open cycles and left-spine spirals:* One has $\neg(M \to_S^+ M^\sigma)$ unconditionally ($C[\,] \equiv \square$). Moreover, $\neg(M \to_S^+ L[M^\sigma])$ holds unconditionally whenever $\mathrm{hd}(M) \in \mathcal{V}$, and more generally whenever $M$ evaluates outside the unsolvable sink $\infty_{\mathrm{HN}}$ in the open extension of the $35$-state head-normalization algebra $\mathcal{A}_{\mathrm{HN}}$ (with $\llbracket x \rrbracket_{\mathrm{HN}}^{\mathrm{open}} = \infty_{\mathrm{HN}}$ for all $x \in \mathcal{V}$).
- (ii) *Variable-multiplicity and right-spine coupling:* Every step $P \to_S Q$ in $\mathcal{T}_S(\mathcal{V})$ and every variable $x \in \mathcal{V}$ satisfy $\#_x(P) \le \#_x(Q)$, $\operatorname{rs}(Q) - \operatorname{rs}(P) \le \#_x(Q) - \#_x(P)$ whenever $\mathrm{rt}(P) \equiv x$, and

$$
\mathrm{maxRS}_x(Q) + \#_x(P) \;\le\; \mathrm{maxRS}_x(P) + \#_x(Q). \tag{2.5}
$$

  Consequently: (a) if $\mathrm{maxRS}_x(M) = 0$ for all $x \in \mathcal{V}$ (every variable in $M$ occurs solely in left/function positions), then $\neg(M \to_S^+ C[M^\sigma])$ for all $C[\,]$ and $\sigma$; and (b) if $\#_x(C) = 0$ for all $x \in \mathrm{Vars}(M)$ and $\sigma$ is diagonally non-duplicating on $\mathrm{Vars}(M)$ ($\#_x(\sigma(x)) \le 1$ and $x \notin \mathrm{Vars}(\sigma(y))$ for $y \in \mathrm{Vars}(M) \setminus \{x\}$), then $\neg(M \to_S^+ C[M^\sigma])$.
- (iii) *Universal $1$-step and $2$-step open-spiral impossibility:* Neither $M \to_S C[M^\sigma]$ nor $M \to_S^2 C[M^\sigma]$ holds for any $M \in \mathcal{T}_S(\mathcal{V})$, $C[\,]$, and $\sigma$.
- (iv) *Parametric self-embedding near-miss in pure $\mathrm{CL}(S)$:* Recall $T \equiv S S$, $G_0 \equiv S T T$, and $V \equiv S G_0$, and define $T^0 U \equiv U$, $T^{n+1} U \equiv T(T^n U)$. For every $x \in \mathcal{V}$ and every $n \in \mathbb{N}$, there exists an explicit context $C_n[\,] \not\equiv \square$ such that under leftmost-outermost pure-$S$ reduction $\to_{\mathrm{lo}}$,

$$
V x\,\bigl(T^n(V x)\bigr) \;\to_{\mathrm{lo}}^{4n+3}\; C_n\Bigl[V x\,\bigl(T^{n+1}(V x)\bigr)\Bigr]. \tag{2.6}
$$

*Proof.* 
For (i), suppose $M \to_S^+ M^\sigma$ with $|M|$ minimal. If no root contraction occurred along $M \to_S^+ M^\sigma$, then $M \equiv P Q$ would satisfy $P \to_S^+ P^\sigma$ or $Q \to_S^+ Q^\sigma$, contradicting minimality of $|M|$. Thus $M$ reduces to $M^\sigma$ via a sequence containing at least one root contraction ($M \xrightarrow{r} M^\sigma$). Since $\xrightarrow{r}$ is preserved under arbitrary substitutions, applying $\sigma^n$ yields an infinite sequence $M \xrightarrow{r} M^\sigma \xrightarrow{r} M^{\sigma^2} \xrightarrow{r} \cdots$ with infinitely many root contractions, contradicting constructive top-termination on $\mathcal{T}_S(\mathcal{V})$ (Theorem 6.9). Next suppose $M \to_S^+ L[M^\sigma]$. If $\mathrm{hd}(M) \in \mathcal{V}$ or if $M \to_S^+ L[M^\sigma]$ uses only non-head internal steps, then left-spine length is preserved identically: $\operatorname{ls}(M) = \operatorname{ls}(L[M^\sigma]) = \operatorname{ls}(M^\sigma) + d_{\mathrm{L}}(L) \ge \operatorname{ls}(M) + d_{\mathrm{L}}(L)$, forcing $d_{\mathrm{L}}(L) = 0$ ($L[\,] \equiv \square$) and contradicting $\neg(M \to_S^+ M^\sigma)$. Otherwise $M \to_S^+ L[M^\sigma]$ decomposes as $M \to_S^* P_1 \to_h P_2 \to_S^* L[M^\sigma]$. When $\llbracket M \rrbracket_{\mathrm{HN}}^{\mathrm{open}} \ne \infty_{\mathrm{HN}}$, both $\to_h$ and $\to_S^*$ commute with $\sigma^k$ and left-spine contexts $K[\,]$, while by Theorem 6.9 internal steps never increase the integer potential $\nu_{\mathrm{HN}} \in \mathbb{N}$ and each head step outside $\infty_{\mathrm{HN}}$ strictly decreases $\nu_{\mathrm{HN}}$ by at least $1$; unrolling $M \to_S^* P_1 \to_h P_2 \to_S^* L[M^\sigma]$ through $\nu_{\mathrm{HN}}(M) + 1$ iterations yields $\nu_{\mathrm{HN}}(M) < 0$, a contradiction.

For (ii), at a root contraction $S P Q R \to_r (P R)(Q R)$, we have $\#_x((P R)(Q R)) - \#_x(S P Q R) = \#_x(R) \ge 0$. If $\mathrm{rt}(S P Q R) \equiv \mathrm{rt}(R) \equiv x$, then $x \in \mathrm{Vars}(R)$ gives $\#_x(R) \ge 1$, while $\operatorname{rs}((P R)(Q R)) - \operatorname{rs}(S P Q R) = 1 \le \#_x(R)$ and $\mathrm{maxRS}_x((P R)(Q R)) \le \mathrm{maxRS}_x(S P Q R) + 1 \le \mathrm{maxRS}_x(S P Q R) + \#_x(R)$; if $\mathrm{rt}(R) \not\equiv x$, then $\mathrm{maxRS}_x((P R)(Q R)) = \mathrm{maxRS}_x(S P Q R)$. Induction over left and right contexts preserves all three inequalities, using $\mathrm{rt}(R') \equiv \mathrm{rt}(R)$ from Proposition 2.2(ii) on right-child steps. For (a), the same root/context inspection shows that $\mathrm{maxRS}_w(P) = 0$ and $P \to_S Q$ imply $\mathrm{maxRS}_w(Q) = 0$. Hence if $\mathrm{maxRS}_w(M) = 0$ for all $w$ and $M \to_S^+ C[M^\sigma]$, then $\mathrm{maxRS}_w(C[M^\sigma]) = 0$ for all $w$; for each $v \in \mathrm{Vars}(M)$ with $\mathrm{rt}(\sigma(v)) \equiv w$, the subterm inclusion $\sigma(v) \trianglelefteq C[M^\sigma]$ forces $\operatorname{rs}(\sigma(v)) \le \mathrm{maxRS}_w(\sigma(v)) \le \mathrm{maxRS}_w(C[M^\sigma]) = 0$, contradicting Theorem 2.12(ii). For (b), if $M \to_S^+ C[M^\sigma]$ under diagonal non-duplication and variable-free $C[\,]$, Theorem 2.12(ii) yields $x \in \mathrm{Vars}(M)$ with $\mathrm{rt}(\sigma(x)) \equiv x$ and $\operatorname{rs}(\sigma(x)) \ge 1$. Then $\mathrm{maxRS}_x(M) + \operatorname{rs}(\sigma(x)) \le \mathrm{maxRS}_x(M^\sigma) \le \mathrm{maxRS}_x(C[M^\sigma])$, whereas $\#_x(C[M^\sigma]) = \#_x(M^\sigma) \le \#_x(M)$, contradicting $\mathrm{maxRS}_x(C[M^\sigma]) + \#_x(M) \le \mathrm{maxRS}_x(M) + \#_x(C[M^\sigma])$ obtained by summing (2.5).

For (iii), we first show by induction on $M \to_S N$ that $M^\sigma \not\trianglelefteq N$. At $M \equiv S P Q R \to_r (P R)(Q R)$, $|M^\sigma| \ge 1 + |P| + |Q| + |R|$ exceeds both $|P R|$ and $|Q R|$, while root equality $((S P^\sigma) Q^\sigma) R^\sigma \equiv (P R)(Q R)$ forces $S P^\sigma \equiv P$, contradicting $|S P^\sigma| \ge 1 + |P|$. Contextual steps $A B \to_S A' B$ and $A B \to_S A B'$ follow by leaf count on the unchanged child and the induction hypothesis on the stepped child. Next suppose $M \to_S M_1 \to_S N$ with $M^\sigma \trianglelefteq N$, minimal in $|M|$. If both steps are non-root on $M \equiv A B$, two steps on the same side contradict $|M|$-minimality, while $A \to_S A_1$ and $B \to_S B_1$ ($N \equiv A_1 B_1$) reduce to $A^\sigma \trianglelefteq A_1$ or $B^\sigma \trianglelefteq B_1$, contradicting the $1$-step case. If one step is root $S P Q R \to_r (P R)(Q R)$ and the other steps internally inside $P$, $Q$, or $R$, leaf bounds $|M^\sigma| \ge 1 + |P| + |Q| + |R|$ and the $1$-step impossibility on the stepped argument eliminate every subterm position of $N$ (with root match forcing either $|S P^\sigma| = |P|$ or $P^\sigma \trianglelefteq P'$). Only the four overlapping two-root-contraction shapes remain, and in each case leaf-size inequalities eliminate all proper subterms except a single candidate equation refuted by second-order substitution unification:

- (1) For $M \equiv S(S U) Q R \to_r (S U R)(Q R) \to_r (U(Q R))(R(Q R))$, only $M^\sigma \equiv R(Q R)$ survives leaf bounds, giving $(S(S U^\sigma)) Q^\sigma \equiv R$ and $R^\sigma \equiv Q R$. Applying $\sigma$ yields $(S(S U^{\sigma^2})) Q^{\sigma^2} \equiv Q R$, so $Q \equiv S(S U^{\sigma^2})$ and $R \equiv Q^{\sigma^2} \equiv S(S U^{\sigma^4})$, whose left child $S$ clashes with $S(S U^\sigma)$ in $R \equiv (S(S U^\sigma)) Q^\sigma$.
- (2) For $M \equiv S S Y P R \to_{\mathrm{nr}} (S P)(Y P) R \to_r (P R)((Y P) R)$, only $M^\sigma \equiv (P R)((Y P) R)$ survives, giving $(S S) Y^\sigma \equiv P$, $P^\sigma \equiv R$, and $R^\sigma \equiv (Y P) R$. Then $R \equiv (S S) Y^{\sigma^2}$ and $(Y P) R \equiv (S S) Y^{\sigma^3}$, forcing $Y P \equiv S S$ and $P \equiv S$, clashing with $P \equiv (S S) Y^\sigma$.
- (3) For $M \equiv S(S X_1 X_2) Q R \to_r (S X_1 X_2 R)(Q R) \to_{\mathrm{nr}} ((X_1 R)(X_2 R))(Q R)$, only the root match survives, giving $S(S X_1^\sigma X_2^\sigma) \equiv X_1 R$ (so $X_1 \equiv S$ and $R \equiv S X_1^\sigma X_2^\sigma$), $Q^\sigma \equiv X_2 R$, and $R^\sigma \equiv Q R$. Since $X_1 \equiv S$, the identity $Q R \equiv R^\sigma \equiv (S S) X_2^{\sigma^2}$ gives $Q \equiv S S$, $X_2 R \equiv Q^\sigma \equiv S S$, and $R \equiv S$, clashing with $R \equiv S X_1^\sigma X_2^\sigma$.
- (4) For $M \equiv S P (S X_1 X_2) R \to_r (P R)(S X_1 X_2 R) \to_{\mathrm{nr}} (P R)((X_1 R)(X_2 R))$, only $M^\sigma \equiv (X_1 R)(X_2 R)$ survives, giving $(S P^\sigma)(S X_1^\sigma X_2^\sigma) \equiv X_1 R$ (so $R \equiv S X_1^\sigma X_2^\sigma$) and $R^\sigma \equiv X_2 R$. Applying $\sigma$ gives $(S X_1^{\sigma^2}) X_2^{\sigma^2} \equiv X_2 R$, so $X_2 \equiv S X_1^{\sigma^2}$ and $R \equiv X_2^{\sigma^2} \equiv S X_1^{\sigma^4}$, whose left child $S$ clashes with $S X_1^\sigma$ in $R \equiv (S X_1^\sigma) X_2^\sigma$.

For (iv), put $U \equiv V x \equiv S G_0 x$. Because $G_0 \equiv S T T \in \mathrm{NF}$, induction gives $T^m U \in \mathrm{NF}$ for all $m \in \mathbb{N}$ and hence $R_n \equiv x(T^n U) \in \mathrm{NF}$. Two leftmost-outermost steps yield

$$
U(T^n U) \;\equiv\; S G_0 x (T^n U) \;\to_{\mathrm{lo}}\; \bigl(G_0(T^n U)\bigr)\,R_n \;\to_{\mathrm{lo}}\; \bigl((T^{n+1} U)(T^{n+1} U)\bigr)\,R_n.
$$

For any normal form $W_0 \in \mathrm{NF}$, set $W \equiv T W_0 \equiv S S W_0$, $R \equiv x W_0 \in \mathrm{NF}$, and $P_k \equiv (T^k U)\,W\,R$ ($k \ge 1$). We verify by induction on $k \ge 1$ that $P_k \to_{\mathrm{lo}}^{4k-3} D_k[U W]$ for some $D_k[\,] \not\equiv \square$: at $k = 1$, $P_1 \equiv S S U W R \to_{\mathrm{lo}} (S W\,(U W))\,R$ takes $1 = 4(1) - 3$ step; for $k = m + 1 \ge 2$, four leftmost-outermost steps give

$$
P_{m+1} \equiv S S (T^m U)\,W\,R \;\to_{\mathrm{lo}}\; \bigl(S W\,(T^m U\,W)\bigr)\,R \;\to_{\mathrm{lo}}\; (S S W_0 R)\,P_m \;\to_{\mathrm{lo}}\; \bigl(S R\,(W_0 R)\bigr)\,P_m \;\to_{\mathrm{lo}}\; x\,W_0\,P_m\,\bigl((W_0 R)\,P_m\bigr).
$$

Because the head is the variable $x$ and the first spine argument $W_0$ lies in $\mathrm{NF}$, leftmost-outermost reduction proceeds inside $P_m$ for the next $4m - 3$ steps to reach $x\,W_0\,D_m[U W]\,\bigl((W_0 R)\,P_m\bigr)$ in $4 + (4m - 3) = 4(m+1) - 3$ steps. Taking $W_0 \equiv T^n U$ and $k = n + 1$ yields (2.6) in $2 + (4n + 1) = 4n + 3$ steps.
 $\square$

*Remark 2.14 (Why parametric pure-$S$ self-reproduction fails to close into an open spiral).* 
In Waldmann's Example 33 [4, p. 95], the closed normal form $S V V$ spirals after translation into the $\lambda$-calculus by reducing underneath $\lambda$-abstractions. Equation (2.6) shows that open pure-$S$ rewriting already achieves parametric $n \mapsto n + 1$ self-embedding directly inside $\mathrm{CL}(S)$, because the ambient argument $x(T^n(V x))$ supplies the third argument needed to peel $T \equiv S S$. Theorem 2.13(ii) explains why this $n \mapsto n + 1$ shift cannot be absorbed into a substitution $M \to_S^+ C[M^\sigma]$: encoding the increment on a single variable via $\sigma(x) = T x$ over a variable-free context violates (2.5) (increasing $\mathrm{maxRS}_x$ by $\operatorname{rs}(T x) = 1$ requires duplicating $x$, forcing $\#_x(C) \ge 1$), whereas abstracting the tower $T^n(V x)$ into a second variable $y$ with $\sigma(y) = T y$ (as in $V x y$ or $V x (y(V x))$) replaces the active combinator $T \equiv S S$ by a passive head variable $y$, stalling head reduction before self-reproduction can occur.


Finally, whereas $\mathrm{maxRS}_x$ in (2.5) can grow when $x$ is duplicated, minimizing right-spine depth over all right-maximal subterms ending in $x$—and dually minimizing left-spine arity over all left-maximal subterms headed by $x$—yields two unconditional step-by-step monotone invariants across all of $\mathcal{T}_S(\mathcal{V})$, removing every multiplicity restriction on $M$ in Theorem 2.13(ii)(b) and characterizing full Conjecture 17 purely in terms of context-free $\mathcal{DP}$-chains.

**Theorem 2.15 (Universal $\mathrm{minRS}_x$ and $\mathrm{minLS}_x$ monotonicity, arbitrary-multiplicity non-spiralling, and $\mathcal{DP}$ equivalence).** 
For $P \in \mathcal{T}_S(\mathcal{V})$ and $x \in \mathrm{Vars}(P)$, let $\mathrm{minRS}_x(P) \in \mathbb{N}$ denote the minimum of $\operatorname{rs}(U)$ over all right-maximal subterms $U$ of $P$ (that is, $U \equiv P$ or $U$ appears as the left child $U V \trianglelefteq P$) satisfying $\mathrm{rt}(U) \equiv x$, and let $\mathrm{minLS}_x(P) \in \mathbb{N}$ denote the minimum of $\operatorname{ls}(W)$ over all left-maximal subterms $W$ of $P$ ($W \equiv P$ or $V W \trianglelefteq P$) satisfying $\mathrm{hd}(W) \equiv x$.

- (i) *Variable conservation and dual universal monotonicities:* Every pure-$S$ contraction $P \to_S Q$ preserves $\mathrm{Vars}(Q) = \mathrm{Vars}(P)$ identically, and for every $x \in \mathrm{Vars}(P)$ satisfies

$$
\mathrm{minRS}_x(Q) \;\le\; \mathrm{minRS}_x(P) \qquad \text{and} \qquad \mathrm{minLS}_x(P) \;\le\; \mathrm{minLS}_x(Q). \tag{2.7}
$$

  Moreover, $\mathrm{minLS}_x(P) \le \mathrm{minLS}_x(Q)$ persists across arbitrary context-stripped dependency-pair chains $P \Rightarrow_{\mathcal{DP}} Q$ whenever $x \in \mathrm{Vars}(Q)$.
- (ii) *Arbitrary-multiplicity $1$-variable and multi-variable non-spiralling:* Let $M \in \mathcal{T}_S(\mathcal{V})$ with arbitrary variable multiplicities $\#_v(M)$. (a) If $\mathrm{Vars}(M) \subseteq \{x\}$, $x \notin \mathrm{Vars}(C)$, and every off-right-spine occurrence of $x$ in $\sigma(x)$ has local right-spine depth at least $\mathrm{minRS}_x(M) + 1$ (in particular whenever $\#_x(\sigma(x)) \le 1$, for example $\sigma(x) = T^k x$ with $k \ge 0$), then $\neg(M \to_S^+ C[M^\sigma])$. (b) If $C[\,]$ is variable-free, every $v \in \mathrm{Vars}(M)$ has variable-free left off-spine branches along the right spine of $\sigma(v)$, and $\operatorname{rs}(\sigma(v)) \ge 1$ whenever $\sigma(v) \notin \mathcal{T}_S$ (allowing arbitrary variable permutations and variable-merging substitutions such as $(x, y) \mapsto (T x, S x)$ or $(x, y) \mapsto (T y, S x)$), then $\neg(M \to_S^+ C[M^\sigma])$.
- (iii) *Context-free dependency-pair characterization of Conjecture 17:* Full Conjecture 17 ($\forall M, C[\,], \sigma,\; \neg(M \to_S^+ C[M^\sigma])$ over all open or closed contexts $C[\,]$) holds if and only if no $M \in \mathcal{T}_S(\mathcal{V})$ and $\sigma \colon \mathcal{V} \to \mathcal{T}_S(\mathcal{V})$ satisfy both $M \Rightarrow_{\mathcal{DP}} M^\sigma$ and $\operatorname{rs}(M) < \operatorname{rs}(M^\sigma)$.

*Proof.* 
For (i), variable conservation $\mathrm{Vars}((X Z)(Y Z)) = \mathrm{Vars}(X) \cup \mathrm{Vars}(Y) \cup \mathrm{Vars}(Z) = \mathrm{Vars}(S X Y Z)$ is immediate because $Z$ appears on both sides. For $\mathrm{minRS}_x$, define for each right-spine offset $k \in \mathbb{N}$ the parametrized minimum $\mathrm{minRS}_x^{(k)}(T) \in \mathbb{N} \cup \{\infty\}$ by $\mathrm{minRS}_x^{(k)}(S) = \infty$, $\mathrm{minRS}_x^{(k)}(v) = k$ if $v \equiv x$ and $\infty$ otherwise, and $\mathrm{minRS}_x^{(k)}(A B) = \min(\mathrm{minRS}_x^{(0)}(A),\, \mathrm{minRS}_x^{(k+1)}(B))$; structural induction identifies $\mathrm{minRS}_x(P) = \mathrm{minRS}_x^{(0)}(P)$. At a root redex $W \equiv S X Y Z \to_r (X Z)(Y Z) \equiv W'$ with enclosing offset $k$, one computes

$$
\mathrm{minRS}_x^{(k)}(W) \;=\; \min\bigl(\mathrm{minRS}_x^{(1)}(X),\, \mathrm{minRS}_x^{(1)}(Y),\, \mathrm{minRS}_x^{(k+1)}(Z)\bigr),
$$

whereas

$$
\mathrm{minRS}_x^{(k)}(W') \;=\; \min\bigl(\mathrm{minRS}_x^{(0)}(X),\, \mathrm{minRS}_x^{(1)}(Z),\, \mathrm{minRS}_x^{(0)}(Y),\, \mathrm{minRS}_x^{(k+2)}(Z)\bigr).
$$

Since $\mathrm{minRS}_x^{(a)}(T) \le \mathrm{minRS}_x^{(b)}(T)$ whenever $a \le b$, we have $\mathrm{minRS}_x^{(0)}(X) \le \mathrm{minRS}_x^{(1)}(X)$, $\mathrm{minRS}_x^{(0)}(Y) \le \mathrm{minRS}_x^{(1)}(Y)$, and $\min(\mathrm{minRS}_x^{(1)}(Z), \mathrm{minRS}_x^{(k+2)}(Z)) = \mathrm{minRS}_x^{(1)}(Z) \le \mathrm{minRS}_x^{(k+1)}(Z)$, giving $\mathrm{minRS}_x^{(k)}(W') \le \mathrm{minRS}_x^{(k)}(W)$ for all $k \in \mathbb{N}$; left and right congruence steps preserve this inequality directly. Dually, defining $\mathrm{minLS}_x^{(k)}(S) = \infty$, $\mathrm{minLS}_x^{(k)}(v) = k$ if $v \equiv x$ and $\infty$ otherwise, and $\mathrm{minLS}_x^{(k)}(A B) = \min(\mathrm{minLS}_x^{(k+1)}(A),\, \mathrm{minLS}_x^{(0)}(B))$ gives $\mathrm{minLS}_x(P) = \mathrm{minLS}_x^{(0)}(P)$ and $\mathrm{minLS}_x^{(k)}(W) = \min(\mathrm{minLS}_x^{(0)}(X), \mathrm{minLS}_x^{(0)}(Y), \mathrm{minLS}_x^{(0)}(Z)) \le \min(\mathrm{minLS}_x^{(1)}(X), \mathrm{minLS}_x^{(0)}(Z), \mathrm{minLS}_x^{(1)}(Y)) \le \mathrm{minLS}_x^{(k)}(W')$ for all $k \in \mathbb{N}$. Along $P \Rightarrow_{\mathcal{DP}} Q$, non-root reductions preserve $\mathrm{minLS}_x$ monotonicity and projecting from $(X Z)(Y Z)$ to $X Z$ or $Y Z$ drops arguments from a minimum, which cannot decrease the minimum whenever $x$ remains present in the retained branch.

For (ii), induction on $T \in \mathcal{T}_S(\mathcal{V})$ shows that if $\mathrm{minRS}_x^{\mathrm{off}}(\sigma(v)) \ge B$ (where $\mathrm{minRS}_x^{\mathrm{off}}(A B) = \min(\mathrm{minRS}_x^{(0)}(A), \mathrm{minRS}_x^{\mathrm{off}}(B))$ and $\mathrm{minRS}_x^{\mathrm{off}}(a) = \infty$ on atoms) for all $v \in \mathrm{Vars}(T)$, and $\operatorname{rs}(\sigma(v)) + \mathrm{minRS}_v^{(k)}(T) \ge B$ whenever $\mathrm{rt}(\sigma(v)) \equiv x$, then $\mathrm{minRS}_x^{(k)}(T^\sigma) \ge B$; moreover, if $x \notin \mathrm{Vars}(C)$, every $x$-occurrence in $C[U]$ lies inside $U$ at right-spine depth at least its depth in $U$, so $\mathrm{minRS}_x(C[U]) \ge \mathrm{minRS}_x(U)$. In (a), if $M \to_S^+ C[M^\sigma]$, Theorem 2.12(ii) forces $x \in \mathrm{Vars}(M)$, $\mathrm{rt}(\sigma(x)) \equiv x$, and $\operatorname{rs}(\sigma(x)) \ge 1$; setting $m = \mathrm{minRS}_x(M)$ and $B = m + 1$ yields $\mathrm{minRS}_x(C[M^\sigma]) \ge \mathrm{minRS}_x(M^\sigma) \ge m + 1$, contradicting $\mathrm{minRS}_x(C[M^\sigma]) \le \mathrm{minRS}_x(M) = m$ from (2.7). In (b), collapse all variables to a single variable $x_0$ via $\pi(v) \equiv x_0$; if $M \to_S^+ C[M^\sigma]$, then $\pi(M)$ contains $x_0$ (by Proposition 2.4(ii)), so $x_0 \in \mathrm{Vars}(\pi(C[M^\sigma]))$ and $\mathrm{minRS}_{x_0}(\pi(C[M^\sigma])) \le \mathrm{minRS}_{x_0}(\pi(M))$ by (i), and under the hypotheses on $C[\,]$ and $\sigma$, every variable occurrence in $C[M^\sigma]$ originates at the rightmost leaf of some non-closed $\sigma(v)$ ($v \in \mathrm{Vars}(M)$) with $\operatorname{rs}(\sigma(v)) \ge 1$, giving $\mathrm{minRS}_{x_0}(\pi(C[M^\sigma])) \ge \mathrm{minRS}_{x_0}(\pi(M)) + 1$, a contradiction.

For (iii), the forward implication from Conjecture 17 follows because induction on $A \Rightarrow_{\mathcal{DP}} V$ constructs a context $C[\,]$ with $A \to_S^* C[V]$ (wrapping $\square$ inside $(\square\,(Y Z))$ on $\mathrm{dp}_2$ and $((X Z)\,\square)$ on $\mathrm{dp}_3$), and $\operatorname{rs}(M) < \operatorname{rs}(M^\sigma) \le \operatorname{rs}(C[M^\sigma])$ rules out zero-step equality $M \equiv C[M^\sigma]$, forcing $M \to_S^+ C[M^\sigma]$. Conversely, if some $M \to_S^+ C[M^\sigma]$ existed, choosing a leaf-minimal open-spiralling witness $M$ yields $M \Rightarrow_{\mathcal{DP}} M^\sigma$ with at least one $\mathrm{dp}_1$ transition and hence $\operatorname{rs}(M) < \operatorname{rs}(M^\sigma)$ by the proof of Theorem 2.12(ii).
 $\square$

## 3. Polynomial-Size Turing Machine Simulation Under Root-Restarted Selection

Arbitrary deterministic binary Turing machines admit an explicit ongoing pure-$S$ simulation $(\mathcal{E}_{\mathrm{TM}}, \sigma_{\mathrm{TM}}, \mathcal{H}_{11}, \mathcal{D}_{\mathrm{TM}})$ with quartic initial tree size $O((|Q|^2 + |w|)^2)$, node-linear stateless tree-walking step selection, a minimal $11$-state bottom-up halting automaton, and linear-time bare-term output recovery. Following the modular simulation methodology of Cook [18], Neary and Woods [45, 44], and Smith [56], we factor the compiler into four layers: boundary-safe marked normalization, compilation to $U_{3,11}$, $4$-bit binary specialization to $U_{\mathrm{bin}}$, and protected spine-$2$ pure-$S$ encoding.

### 3.1. Source Normalization and Compilation to Neary–Woods $U_{3,11}$

In Neary and Woods's universal Turing machine $U_{3,11}$ [45, 44], the simulated binary machine operates on a one-way infinite tape indexed by $\mathbb{N}$, never steps left from cell $0$ during active computation, and signals halting by entering a designated final state that sweeps left until exiting cell $0$. Our first definition compiles any partial clamping-left binary Turing machine into this exact normal form without corrupting output bits.

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

Within the small universal Turing machine program initiated by Watanabe [67] and advanced through the tag-based machines of Rogozhin and Kudlek [52, 53, 39] (surveyed in [75]), Neary and Woods's $3$-state, $11$-symbol machine $U_{3,11}$ [45, 44] achieves direct quadratic-time Turing simulation without intermediate tag-system exponential blowup.

**Definition 3.2 (The universal Turing machine $U_{3,11}$ and encoder $\mathcal{E}_U$).** 
The machine $U_{3,11}$ has state set $Q_U = \{u_1, u_2, u_3\}$ (with start state $u_1$) and $11$-symbol tape alphabet

$$
\Sigma_{11} \;=\; \bigl\{\,\overleftarrow{a},\, \overleftarrow{b},\, e,\, h,\, \overrightarrow{e},\, \overrightarrow{h},\, \overleftarrow{e},\, \overleftarrow{h},\, \lambda,\, \delta,\, \gamma\,\bigr\},
$$

indexed $0, 1, \dots, 10$ in that order, with blank symbol $\overleftarrow{a}$ ($0$) and $32$ defined transitions displayed in Table 2; the unique undefined halting pair is $(u_3, \delta)$.

**Table 2.** Complete transition table of Neary and Woods's $3$-state, $11$-symbol universal Turing machine $U_{3,11}$ [45, 44], where $\overleftarrow{a}$ is the blank symbol and $(u_3, \delta)$ is the unique halting configuration.

| Index | Symbol | State $u_1$ | State $u_2$ | State $u_3$ |
| ---: | :---: | :---: | :---: | :---: |
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

For (ii), each simulated step of $M_{\mathrm{norm}}$ factors into the four sub-table cycles of [45, 44]: *Cycle 1 (Index)* shuttles between the unary $\overleftarrow{b}^{k+2}$ state counter on the simulated head and $\lambda$-delimiters in the table, neutralizing $k$ delimiters $\lambda \mapsto \delta$ from right to left until selecting the $k$-th ETR block ($0 \le k < 5s$); *Cycle 2 (Print)* copies the selected ETR block character by character ($e \mapsto \overleftarrow{a}, h \mapsto \overleftarrow{b}$) across the overlined region onto the head; *Cycle 3 (Restore)* sweeps left to right in $u_2$, restoring every neutralized $\delta \mapsto \lambda$ and arrowed symbol $\overleftarrow{e}, \overleftarrow{h} \mapsto e, h$; and *Cycle 4 (Choose Read/Write)* aligns the head over the adjacent simulated cell. Cutting the inductive simulation invariant *immediately after Cycle 1* (the *post-index invariant*) unifies all four transition geometries: at configuration $(q, h, \tau_{\mathrm{norm}})$, $U_{3,11}$ stands in state $u_2$ reading $\gamma$, with untouched blocks $k+1, \dots, 5s-1$ on the far left, the active block $\lambda\,E(\delta_{\mathrm{norm}}(q, \tau_{\mathrm{norm}}[h]))$, $k$ neutralized blocks, $\delta\,\overleftarrow{e}\,\langle \tau_{\mathrm{norm}}[0\mathinner{\ldotp\ldotp}h-1] \rangle_L\,\overleftarrow{e}^{5s+3}$ immediately to the left of $\gamma$, and $\langle \tau_{\mathrm{norm}}[h+1\mathinner{\ldotp\ldotp}] \rangle_R$ to the right of $\gamma$ (modulo trailing $\overleftarrow{a}$-blanks).

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

To ensure that evaluation-order selection retains no hidden memory between pure-$S$ contractions and inspects only bounded local tree neighborhoods, we formalize the selector $\sigma_{\mathrm{TM}}$ as a deterministic root-restarted finite-state tree-walking automaton operating on a Huet zipper [37].

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
- (ii) width-$11$ shift buffers ($\{0,1\}^{\le 11}$) and decoded cell registers $\{0,1\} \times \{\mathsf{off}, \mathsf{active}, \mathsf{movingL}, \mathsf{movingR}\} \times \{0,\dots,255\}$ implementing a two-pass tape scan: *Pass 1* scans the tape spine for any cell in status $\mathsf{movingL}$ or $\mathsf{movingR}$ and completes its neighbor arrival and source reset to $\mathsf{off}$; if none is pending, *Pass 2* locates the unique $\mathsf{active}$ cell $(b, \mathsf{active}, q)$ and consults the fixed $262$-rule table of $U_{\mathrm{bin}}$ (opening the hub halt flag if $(q, b)$ is undefined, or appending the next $11$-bit record, or extending the post-halt left-spine frontier if the halt flag is already open);
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
| ---: | :---: | :---: | :---: | :--- |
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
Formatting $\mathcal{E}_U(M,w)$ requires only $O(\log(|Q| + |w|))$ workspace [45], and expanding $u_0$ into the unshared syntax tree $T_0 = \mathcal{E}_{\mathrm{TM}}(M,w)$ is a deterministic uniform block substitution running in time linear in $|T_0|$, while $\mathcal{H}_{11}$ is an $11$-state finite tree automaton and $\mathcal{D}_{\mathrm{TM}}$ runs in read-only time $O(|T_k|)$. In concrete evaluations, compiling the $1$-state halting Turing machine on the empty input ($|Q|=1, |w|=0$, where $|u_0| = 540$ versus the upper bound $N = 788$) produces an explicit pure-$S$ tree of $1{,}996{,}921$ leaves; compiling a $2$-state write-$1$ machine produces $7{,}477{,}337$ leaves; and simulating the $2$-state Busy Beaver executes $912$ pure-$S$ contractions to enter $L(\mathcal{H}_{11})$ and output $1111$, contrasting with the unmaterializable seeds of at least $2^{57207}$ bits required by unary counter/tag pipelines [27].

## 4. Program-Free Cyclic Tag Simulation, Ten-Leaf Seed Genesis, and the Linear-Time Pocket Tree Transducer

In Section 3, the root-restarted selector $\sigma_{\mathrm{TM}}$ incorporates the fixed $262$-rule binary transition table of $U_{\mathrm{bin}}$ inside its finite control. One naturally asks whether this embedded universal transition table can be eliminated altogether, so that both the simulated program and its data reside inside the closed $S$-term while a single program-free selector executes arbitrary computations purely by structural manipulation of $\mathcal{T}_S$. Here we answer this question affirmatively via cyclic tag systems [18], prove that every encoded instance unfolds by pure-$S$ reduction from a single $10$-leaf combinator $D_{\mathrm{seed}}$, and compress the resulting program-free selector into an explicit two-pass contextual finite-state tree transducer $\mathcal{T}_{\mathrm{pocket}}$ running in at most $2|M| - 1 + \mathrm{depth}(M)$ transitions per invocation.

### 4.1. Cyclic Tag Systems and Self-Describing Pure-$S$ Queue Encoding

Introduced by Cook [18] as a binary refinement of Post's canonical and tag systems [48, 50] and Minsky and Cocke's universal $2$-tag machines [42, 17], and later shown by Woods and Neary [74] to simulate Turing machines with polynomial time overhead, cyclic tag systems dispense with explicit control states in favor of a cyclically rotating ring of binary appendants.

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
- (ii) Otherwise, parse $t \equiv H_{\mathrm{hdr}} \cdot F(\mathrm{Flag}, F(\mathrm{Ring}, \mathrm{Queue}, j_1), j_0)$, scan the newest committed $2$-bit status of each phase in $\mathrm{Ring}$ and its $3$-bit template statuses, and scan $\mathrm{Queue}$ to locate the first $\mathsf{consuming}$ cell ($\mathtt{10}b$), first $\mathsf{unconsumed}$ cell ($\mathtt{00}b$), first $\mathsf{staging}$ cell ($\mathtt{01}s$), or any freshly opened uninitialized tail slot:
  - *Handoff completion:* If some phase $j$ has status $\mathsf{handoff}$ ($\mathtt{11}$), then if a queue cell is $\mathsf{consuming}$ ($\mathtt{10}b$), append record $\mathtt{11}b$ ($\mathsf{consumed}$) to it; else if $m = 1$, append $\mathtt{10}$ ($\mathsf{active}$) to phase $0$; else if phase $j' = (j+1) \bmod m$ is not yet $\mathtt{10}$, append $\mathtt{10}$ to phase $j'$, and once phase $j'$ is $\mathtt{10}$, append $\mathtt{00}$ ($\mathsf{inactive}$) to phase $j$.
  - *Active phase dispatch:* If no phase is in $\mathsf{handoff}$ and phase $j$ is $\mathsf{active}$ ($\mathtt{10}$):
    - (a) When no queue cell is $\mathsf{consuming}$: if no $\mathsf{unconsumed}$ cell exists, open the halt flag $\mathrm{Flag}$ at path $[1,0,1]$; else if the front $\mathsf{unconsumed}$ cell holds bit $b = 0$, append $\mathtt{100}$ ($\mathsf{consuming}$); else ($b = 1$) if phase $j$ still has an $\mathsf{idle}$ template ($\mathtt{00}s$), append $\mathtt{10}s$ ($\mathsf{armed}$) to the first $\mathsf{idle}$ template, and once all templates of phase $j$ are $\mathsf{armed}$, append $\mathtt{101}$ ($\mathsf{consuming}$) to the front queue cell.
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

Second, let $\Lambda$ range over finite binary layout skeletons generated by $\Lambda ::= \mathsf{unopened} \mid \mathsf{opened}(\Lambda_1, \Lambda_2)$, where $\mathrm{Term}(\mathsf{unopened}, m, n) \equiv G(m,n)$ and $\mathrm{Term}(\mathsf{opened}(\Lambda_1,\Lambda_2), m, n)$ recursively places $\mathrm{Term}(\Lambda_1, m', n')$ and $\mathrm{Term}(\Lambda_2, m', n')$ into the left and right slots of $F(-,-,j)$ using the phase transition $(m,n) \mapsto (m',n')$ of Construction 3.4. We prove by structural induction on $\Lambda$ that $G(m,n) \to_S^* \mathrm{Term}(\Lambda, m, n)$ for all $m, n \in \mathbb{N}$ with $2 \le n$ and $m \le n$. The base case $\Lambda = \mathsf{unopened}$ is reflexive. For $\Lambda = \mathsf{opened}(\Lambda_1, \Lambda_2)$, Lemma 3.5(i) gives $G(m,n) \to_S^6 F(G(m',n'), G(m',n'), j)$ (if $m \ge 1$) or $G(m,n) \to_S^7 F(G(m',n'), G(m',n'), j)$ (if $m = 0$), with $2 \le n'$ and $m' \le n'$. Because $\to_S^*$ is congruent inside both $a$ and $b$ of $F(a,b,j) \equiv (S a)(S b j)$, applying the induction hypotheses $G(m',n') \to_S^* \mathrm{Term}(\Lambda_1, m', n')$ on the left and $G(m',n') \to_S^* \mathrm{Term}(\Lambda_2, m', n')$ on the right yields $G(m,n) \to_S^* \mathrm{Term}(\mathsf{opened}(\Lambda_1,\Lambda_2), m, n)$. By Construction 4.2, $\mathcal{E}_{\mathrm{CTS}}(P,w) \equiv (\nu_1 S)\,\mathrm{Term}(\Lambda_{P,w}, 2, 2)$ for an explicit finite layout $\Lambda_{P,w}$, whence $D_{\mathrm{seed}} \to_S^5 (\nu_1 S)\,G(2,2) \to_S^* \mathcal{E}_{\mathrm{CTS}}(P,w)$. $\square$

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

Although Definition 4.3 eliminates all universal Turing and tag transition tables from $\sigma_{\mathrm{CTS}}$, its specification still relies on recursive structural scanners over unbounded phase rings, queue spines, and version chains; compressing $\sigma_{\mathrm{CTS}}$ into an explicit minimal finite-state tree transducer directly addresses the helper-complexity question posed in Wolfram's challenge announcement [71].

### 4.3. Two-Pass Linear-Time Contextual Tree Transducer Compression

In Section 3, the root-restarted zipper walker $\sigma_{\mathrm{TM}}$ requires $|Q_{\mathrm{ctrl}}| = 4{,}376{,}490{,}905$ control states to store the $262$-rule transition table of $U_{\mathrm{bin}}$ alongside $11$-bit cell shift buffers, and executes up to $3500(2|M|-1)$ cursor steps per contraction. Conversely, Definition 4.3 formulates $\sigma_{\mathrm{CTS}}$ in terms of unbounded phase indices $(j + 1) \bmod m$ and tree-address lists. We now show that $\sigma_{\mathrm{CTS}}$ is extensionally identical on all of $\mathcal{T}_S$ to a compact two-pass contextual finite-state tree transducer $\mathcal{T}_{\mathrm{pocket}}$: a single bottom-up pass conditioned on $25$ static structural roles assigns a $23$-state summary ($< 5$ bits) to every node in $2|M| - 1$ node transitions, and a single top-down pointer pass with $136$ states descends directly along one root-to-redex path in at most $\mathrm{depth}(M)$ edge transitions without consulting role labels, re-scanning subtrees, or performing unbounded arithmetic.

**Definition 4.6 (Two-pass contextual finite-state tree transducer).** 
For every closed pure-$S$ tree $M \in \mathcal{T}_S$, define its binary tree height $\mathrm{depth}(M) \in \mathbb{N}$ recursively by $\mathrm{depth}(S) = 0$ and $\mathrm{depth}(M_1 M_2) = 1 + \max\{\mathrm{depth}(M_1), \mathrm{depth}(M_2)\}$. Write $\alpha \in \{0,1\}^*$ for a binary tree address ($0$ descending left, $1$ descending right, and $\varepsilon$ denoting the root), $M|_{\alpha}$ for the subterm at $\alpha$ when defined, and $M[\alpha \leftarrow N]$ for single-subtree replacement at $\alpha$.

A *two-pass contextual finite-state tree transducer* over $\mathcal{T}_S$ is a $10$-tuple

$$
\mathcal{T} \;=\; \bigl(R,\, Q,\, P,\, r_0,\, \rho,\, \delta_{\mathrm{leaf}},\, \delta_{\mathrm{app}},\, F_{\mathrm{halt}},\, p_0,\, \delta_{\mathrm{TD}}\bigr),
$$

consisting of finite nonempty state sets $R$ (*static structural roles*), $Q$ (*bottom-up node states*), and $P$ (*top-down pointer states*), an initial root role $r_0 \in R$, a static child-role map $\rho \colon R \to R \times R$, a leaf rule $\delta_{\mathrm{leaf}} \colon R \to Q$, a role-indexed bottom-up transition $\delta_{\mathrm{app}} \colon R \times Q \times Q \to Q$, a halting subset $F_{\mathrm{halt}} \subseteq Q$, an initial pointer state $p_0 \in P$, and a role-free top-down transition function

$$
\delta_{\mathrm{TD}} \;\colon\; P \times Q \times Q \;\longrightarrow\; \{\mathsf{left}(p') : p' \in P\} \cup \{\mathsf{right}(p') : p' \in P\} \cup \{\mathsf{contract},\, \mathsf{stuck}\}.
$$

Given an input tree $M \in \mathcal{T}_S$, execution of $\mathcal{T}$ proceeds in two deterministic passes:

- (i) *Pass 1 (contextual bottom-up annotation):* For each $(r, N) \in R \times \mathcal{T}_S$, define the $Q$-annotated tree $\widehat{N} = \mathrm{Ann}_{\mathcal{T}}(r, N)$, its root state $\mathrm{st}(\widehat{N}) \in Q$, and its node-transition count $s_1(r, N) \in \mathbb{N}$ recursively by setting $\mathrm{st}(\mathrm{Ann}_{\mathcal{T}}(r, S)) = \delta_{\mathrm{leaf}}(r)$ with $s_1(r, S) = 1$, and, for $N \equiv N_1 N_2$ with $\rho(r) = (r_{\mathrm{L}}, r_{\mathrm{R}})$, $\widehat{N}_1 = \mathrm{Ann}_{\mathcal{T}}(r_{\mathrm{L}}, N_1)$, and $\widehat{N}_2 = \mathrm{Ann}_{\mathcal{T}}(r_{\mathrm{R}}, N_2)$, labeling the root of $\widehat{N}$ with

$$
\mathrm{st}(\widehat{N}) \;=\; \delta_{\mathrm{app}}\bigl(r,\, \mathrm{st}(\widehat{N}_1),\, \mathrm{st}(\widehat{N}_2)\bigr), \qquad
s_1(r, N_1 N_2) \;=\; 1 + s_1(r_{\mathrm{L}}, N_1) + s_1(r_{\mathrm{R}}, N_2).
$$

  At the root of $M$, Pass 1 computes $\widehat{M}_0 = \mathrm{Ann}_{\mathcal{T}}(r_0, M)$. If $\mathrm{st}(\widehat{M}_0) \in F_{\mathrm{halt}}$, then $\mathcal{T}$ halts immediately with outcome $\mathcal{T}(M) = \mathsf{halt}$ and total transition count $\tau_{\mathcal{T}}(M) = s_1(r_0, M)$.

- (ii) *Pass 2 (role-free top-down redex location and contraction):* If $\mathrm{st}(\widehat{M}_0) \notin F_{\mathrm{halt}}$, define the pointer descent $\mathrm{Loc}_{\mathcal{T}}(p, \widehat{N}) \in (\{0,1\}^* \cup \{\bot\}) \times \mathbb{N}$ recursively by $\mathrm{Loc}_{\mathcal{T}}(p, \widehat{S}) = (\bot, 0)$ on leaves and, on an annotated application $\widehat{N}$ with children $(\widehat{N}_1, \widehat{N}_2)$ bearing states $(q_{\mathrm{L}}, q_{\mathrm{R}}) = (\mathrm{st}(\widehat{N}_1), \mathrm{st}(\widehat{N}_2))$, by evaluating $\delta_{\mathrm{TD}}(p, q_{\mathrm{L}}, q_{\mathrm{R}})$—which inspects only $(p, q_{\mathrm{L}}, q_{\mathrm{R}})$ without role input from $R$, subtree re-scanning, or unbounded arithmetic:
  - if $\delta_{\mathrm{TD}}(p, q_{\mathrm{L}}, q_{\mathrm{R}}) = \mathsf{left}(p')$ and $\mathrm{Loc}_{\mathcal{T}}(p', \widehat{N}_1) = (\omega', s_2')$, return $(0 \cdot \omega', s_2' + 1)$ (with $0 \cdot \bot := \bot$);
  - if $\delta_{\mathrm{TD}}(p, q_{\mathrm{L}}, q_{\mathrm{R}}) = \mathsf{right}(p')$ and $\mathrm{Loc}_{\mathcal{T}}(p', \widehat{N}_2) = (\omega', s_2')$, return $(1 \cdot \omega', s_2' + 1)$ (with $1 \cdot \bot := \bot$);
  - if $\delta_{\mathrm{TD}}(p, q_{\mathrm{L}}, q_{\mathrm{R}}) = \mathsf{contract}$, return $(\varepsilon, 1)$;
  - if $\delta_{\mathrm{TD}}(p, q_{\mathrm{L}}, q_{\mathrm{R}}) = \mathsf{stuck}$, return $(\bot, 1)$.

  Let $(\omega, s_2) = \mathrm{Loc}_{\mathcal{T}}(p_0, \widehat{M}_0)$ and set $\tau_{\mathcal{T}}(M) = s_1(r_0, M) + s_2$. If $\omega = \alpha \in \{0,1\}^*$ and $M|_{\alpha} \equiv S X Y Z$, then $\mathcal{T}(M) = M[\alpha \leftarrow (X Z)(Y Z)] \in \mathcal{T}_S$; otherwise $\mathcal{T}(M) = \mathsf{stuck}$.

To instantiate Definition 4.6 for self-describing CTS terms (4.1), observe that every frame $F(a, b, j) \equiv (S a)((S b) j)$ wraps its left slot $a$ inside a unary prefix $S a$ and its right slot $b$ inside a binary wrapper $(S b) j$. Accordingly, our concrete transducer $\mathcal{T}_{\mathrm{pocket}}$ employs $25$ static roles $R_{\mathrm{pocket}}$, summarized in Table 4: $11$ primary roles ($\mathsf{rt}$, $\mathsf{hub}$, $\mathsf{pay}$, $\mathsf{ring}$, $\mathsf{body}$, $\mathsf{tmpl}$, $\mathsf{queue}$, $\mathsf{ver}_2$, $\mathsf{ver}_3$, $\mathsf{fld}$, $\mathsf{sp}$), $9$ left-wrapper roles $\mathsf{L}_X$ matching $S a$, and $5$ right-wrapper roles $\mathsf{R}_Y$ matching $(S b) j$. Because all inner non-ring roles take at most $16$ summary values in $\{0,\dots,15\}$, shifting valid wrapper states on $\mathsf{L}_X$ ($X \ne \mathsf{ring}$) and $\mathsf{R}_Y$ ($Y \ne \mathsf{ring}$) by $+7$ into $\{7,\dots,22\}$ keeps them disjoint from truncated spine arities $\{0,\dots,5\}$, multiplexing all $25$ roles into a shared carrier $Q_{\mathrm{pocket}} = \{0,\dots,22\}$ of size $23$ without passing $R_{\mathrm{pocket}}$ to Pass 2.

**Table 4.** Static $25$-role grammar $\rho(r) = (r_{\mathrm{L}}, r_{\mathrm{R}})$ and Pass-1 semantic state encodings of $\mathcal{T}_{\mathrm{pocket}}$ within $Q_{\mathrm{pocket}} = \{0,\dots,22\}$ ($\delta_{\mathrm{leaf}}(r) = 0$ for all $r \in R_{\mathrm{pocket}}$; $F_{\mathrm{halt}} = \{1\}$ at root role $r_0 = \mathsf{rt}$).

| Role $r$ (count) | Child roles $\rho(r)$ | Codomain | Pass-1 bottom-up invariant $\varsigma(r, N)$ on $N \in \mathcal{T}_S$ |
| :--- | :--- | :---: | :--- |
| $\mathsf{rt}$ ($1$) | $(\mathsf{sp}, \mathsf{hub})$ | $\{0,1\}$ | $1$ iff $N \in L(\mathcal{H}_{11})$ ($\mathsf{rootHalt}(N) = 1$) |
| $\mathsf{hub}$ ($1$) | $(\mathsf{L}_{\mathsf{sp}}, \mathsf{R}_{\mathsf{pay}})$ | $\{0,1\}$ | $1$ iff $N \equiv F(\mathrm{Flag}, \mathrm{Pay}, j_0)$ with $\mathrm{Flag}$ an $F$-frame |
| $\mathsf{pay}$ ($1$) | $(\mathsf{L}_{\mathsf{ring}}, \mathsf{R}_{\mathsf{queue}})$ | $\{0,1,2\}$ | $0$ non-frame; $2$ active empty-queue halt trigger; $1$ else |
| $\mathsf{ring}$ ($1$) | $(\mathsf{L}_{\mathsf{body}}, \mathsf{R}_{\mathsf{ring}})$ | $\{0,\dots,21\}$ | $0$ end; $1\text{–}4$ handoff $(b_{\mathrm{hd}}, b_{\mathrm{last}})$; $5$ idle; $6\text{–}21$ active |
| $\mathsf{body}$ ($1$) | $(\mathsf{L}_{\mathsf{ver}_2}, \mathsf{R}_{\mathsf{tmpl}})$ | $\{0,\dots,10\}$ | $0$ non-frame; $1$ $\mathtt{11}$; $2$ $\mathtt{0}b$/none; $3 + c_{\mathrm{tmpl}}$ on $\mathtt{10}$ |
| $\mathsf{tmpl}$ ($1$) | $(\mathsf{L}_{\mathsf{ver}_3}, \mathsf{R}_{\mathsf{tmpl}})$ | $\{0,\dots,7\}$ | $4 b_{\mathrm{idle}} + c_4$ ($\mathsf{idle}$ bit and $\mathsf{appending}$/$\mathsf{armed}$ priority) |
| $\mathsf{queue}$ ($1$) | $(\mathsf{L}_{\mathsf{ver}_3}, \mathsf{R}_{\mathsf{queue}})$ | $\{0,\dots,11\}$ | $9 + \mathrm{su}$ if $\mathsf{consuming}$; else $3 u + \mathrm{su}$ ($\mathsf{unconsumed}$, tail) |
| $\mathsf{ver}_2$ ($1$) | $(\mathsf{L}_{\mathsf{ver}_2}, \mathsf{R}_{\mathsf{fld}})$ | $\{0,\dots,3\}$ | Newest $2$-bit phase status ($0$ none, $1$ $\mathtt{11}$, $2$ $\mathtt{10}$, $3$ $\mathtt{0}b$) |
| $\mathsf{ver}_3$ ($1$) | $(\mathsf{L}_{\mathsf{ver}_3}, \mathsf{R}_{\mathsf{fld}})$ | $\{0,\dots,8\}$ | Newest $3$-bit record ($0$ none, $1 + 4 b_0 + 2 b_1 + b_2$) |
| $\mathsf{fld}$ ($1$) | $(\mathsf{L}_{\mathsf{sp}}, \mathsf{R}_{\mathsf{fld}})$ | $\{0,\dots,15\}$ | Bit-field prefix of length $0$ ($1$), $1$ ($2\text{–}3$), $2$ ($4\text{–}7$), $\ge 3$ ($8\text{–}15$) |
| $\mathsf{sp}$ ($1$) | $(\mathsf{sp}, \mathsf{sp})$ | $\{0,\dots,6\}$ | $6$ if $N$ is an $F$-frame; else $\min\{5, \operatorname{ls}(N)\} \in \{0,\dots,5\}$ |
| $\mathsf{L}_{\mathsf{ring}}, \mathsf{R}_{\mathsf{ring}}$ ($2$) | $(\mathsf{sp}, \mathsf{ring}),\, (\mathsf{L}_{\mathsf{ring}}, \mathsf{sp})$ | $\{0,\dots,22\}$ | $1 + \varsigma(\mathsf{ring}, u)$ on $S u$ resp. $(S u) j$; $0$ otherwise |
| $\mathsf{L}_X$, $X \ne \mathsf{ring}$ ($8$) | $(\mathsf{sp}, X)$ | $\{0,\dots,22\}$ | $7 + \varsigma(X, u)$ on $S u$; else $\min\{5, \operatorname{ls}(N)\} \in \{0,\dots,5\}$ |
| $\mathsf{R}_Y$, $Y \ne \mathsf{ring}$ ($4$) | $(\mathsf{L}_Y, \mathsf{sp})$ | $\{0,\dots,22\}$ | $7 + \varsigma(Y, v)$ on $(S v) j$; else $\min\{5, \operatorname{ls}(N)\} \in \{0,\dots,5\}$ |

**Theorem 4.7 (Linear-time pocket tree transducer equivalence and program-free universality).** 
There exists an explicit program-free two-pass contextual finite-state tree transducer

$$
\mathcal{T}_{\mathrm{pocket}} \;=\; \bigl(R_{\mathrm{pocket}},\, Q_{\mathrm{pocket}},\, P_{\mathrm{pocket}},\, r_0,\, \rho,\, \delta_{\mathrm{leaf}},\, \delta_{\mathrm{app}},\, F_{\mathrm{halt}},\, p_0,\, \delta_{\mathrm{TD}}\bigr)
$$

with $|R_{\mathrm{pocket}}| = 25$ static structural roles, $|Q_{\mathrm{pocket}}| = 23$ bottom-up node states ($< 5$ bits per node, with $271$ pairs $(r, q) \in R_{\mathrm{pocket}} \times Q_{\mathrm{pocket}}$ reachable from $r_0$ over $\mathcal{T}_S$), and $|P_{\mathrm{pocket}}| = 136$ single-edge top-down pointer states ($54$ decision macro-states together with $50$ two-edge frame-left and $32$ three-edge frame-right stepping states), containing zero universal Turing or tag transition tables, such that:

- (i) *Exact linear transition bounds:* For every closed pure-$S$ tree $M \in \mathcal{T}_S$, Pass 1 executes in $2|M| - 1$ node transitions and Pass 2 executes in at most $\mathrm{depth}(M)$ edge transitions. Consequently, $\mathcal{T}_{\mathrm{pocket}}$ halts unconditionally in

$$
\tau_{\mathcal{T}_{\mathrm{pocket}}}(M) \;\le\; 2|M| - 1 + \mathrm{depth}(M) \tag{4.4}
$$

  total transitions on every $M \in \mathcal{T}_S$, and satisfies $\tau_{\mathcal{T}_{\mathrm{pocket}}}(M) + 2 \le 2|M| - 1 + \mathrm{depth}(M)$ (at most $2|M| - 3 + \mathrm{depth}(M)$ total transitions) whenever a pure-$S$ redex is contracted ($\mathcal{T}_{\mathrm{pocket}}(M) = M' \in \mathcal{T}_S$).

- (ii) *Extensional equivalence with $\sigma_{\mathrm{CTS}}$ and universal cyclic tag simulation:* On every closed tree $M \in \mathcal{T}_S$, one has $\mathcal{T}_{\mathrm{pocket}}(M) = \sigma_{\mathrm{CTS}}(M)$ identically. Hence, for every cyclic tag system $P = (A_0, \dots, A_{m-1})$ and input word $w \in \{0,1\}^*$, the pure-$S$ encoding $T_0 = \mathcal{E}_{\mathrm{CTS}}(P, w) \in \mathcal{T}_S$ unfolds via $D_{\mathrm{seed}} \to_S^* T_0$ from the $10$-leaf seed $D_{\mathrm{seed}} \equiv S(S(S S))(S(S S))(S S)S \equiv S B B T S$, and iterating $\mathcal{T}_{\mathrm{pocket}}$ simulates $(P, w)$ with bidirectional halting equivalence ($(0, w)$ halts under $\vdash_P^*$ if and only if $\mathcal{T}_{\mathrm{pocket}}^k(T_0) = T_k$ satisfies $\mathcal{T}_{\mathrm{pocket}}(T_k) = \mathsf{halt}$ for some $k \ge 0$), exact bare-term terminal readback $\mathcal{D}_{\mathrm{CTS}}(T_k) = (i_{\mathrm{fin}}, \varepsilon)$ matching $(0, w) \vdash_P^* (i_{\mathrm{fin}}, \varepsilon)$, and the all-step quadratic leaf bound $|T_k| \le 35{,}000(\|(P, w)\| + k + 1)^2$.

*Proof.* 
We establish (i) for any transducer $\mathcal{T}$ of Definition 4.6 before proving Pass-1 and Pass-2 correctness of $\mathcal{T}_{\mathrm{pocket}}$ in (ii).

For (i), structural induction on $N \in \mathcal{T}_S$ shows $s_1(r, N) = 2|N| - 1$ for every $r \in R$: on $N \equiv S$, $s_1(r, S) = 1 = 2|S| - 1$; on $N \equiv N_1 N_2$ with $\rho(r) = (r_{\mathrm{L}}, r_{\mathrm{R}})$, the induction hypothesis gives

$$
s_1(r, N_1 N_2) \;=\; 1 + \bigl(2|N_1| - 1\bigr) + \bigl(2|N_2| - 1\bigr) \;=\; 2\bigl(|N_1| + |N_2|\bigr) - 1 \;=\; 2|N_1 N_2| - 1.
$$

Next, let $(\omega, s_2) = \mathrm{Loc}_{\mathcal{T}}(p, \widehat{N})$ where $\widehat{N} = \mathrm{Ann}_{\mathcal{T}}(r, N)$. Structural induction on $N$ proves $s_2 \le \mathrm{depth}(N)$: on $N \equiv S$, $s_2 = 0 = \mathrm{depth}(S)$; on $N \equiv N_1 N_2$, if $\delta_{\mathrm{TD}}$ returns $\mathsf{contract}$ or $\mathsf{stuck}$, then $s_2 = 1 \le 1 + \max\{\mathrm{depth}(N_1), \mathrm{depth}(N_2)\} = \mathrm{depth}(N_1 N_2)$, whereas if $\delta_{\mathrm{TD}}$ steps left or right into $\widehat{N}_i$ ($i \in \{1, 2\}$), the induction hypothesis gives $s_2 = 1 + s_2' \le 1 + \mathrm{depth}(N_i) \le \mathrm{depth}(N_1 N_2)$. Hence $\tau_{\mathcal{T}}(M) \le 2|M| - 1 + \mathrm{depth}(M)$ for all $M \in \mathcal{T}_S$ (with $\tau_{\mathcal{T}}(M) = 2|M| - 1$ when $\mathrm{st}(\widehat{M}_0) \in F_{\mathrm{halt}}$). Moreover, suppose $\mathcal{T}(M) = M' \in \mathcal{T}_S$, so $\omega = \alpha \in \{0,1\}^*$ and $U \equiv M|_{\alpha} \equiv ((S X) Y) Z$. Because $\mathrm{depth}(S X) \ge 1$ and $\mathrm{depth}((S X) Y) \ge 2$, every pure-$S$ redex satisfies $\mathrm{depth}(U) \ge 3$. At $\alpha$, $\delta_{\mathrm{TD}}$ emits $\mathsf{contract}$ in $1 \le \mathrm{depth}(U) - 2$ transition; inducting upward along each edge of $\alpha$ adds $1$ to $s_2$ and increases $\mathrm{depth}$ by at least $1$, yielding $s_2 \le \mathrm{depth}(M) - 2$ and $\tau_{\mathcal{T}}(M) = (2|M| - 1) + s_2 \le 2|M| - 3 + \mathrm{depth}(M)$.

For (ii), define the $25$-role transition $\delta_{\mathrm{app}} \colon R_{\mathrm{pocket}} \times Q_{\mathrm{pocket}}^2 \to Q_{\mathrm{pocket}}$ to implement the specification $\varsigma(r, N) \in \{0,\dots,22\}$ in Table 4, with $\delta_{\mathrm{leaf}}(r) = 0$ for all $r$. Define the spine-arity projections $\pi_{\mathrm{L}}, \pi_{\mathrm{R}} \colon Q_{\mathrm{pocket}} \to \{0,\dots,5\}$ by setting $\pi_{\mathrm{L}}(q) = q$ for $q \le 5$, $\pi_{\mathrm{L}}(6) = 2$, and $\pi_{\mathrm{L}}(q) = 1$ for $q \ge 7$, while $\pi_{\mathrm{R}}(q) = q$ for $q \le 5$ and $\pi_{\mathrm{R}}(q) = 2$ for $q \ge 6$. We verify by structural induction on $N \in \mathcal{T}_S$ that $\mathrm{st}(\mathrm{Ann}_{\mathcal{T}_{\mathrm{pocket}}}(r, N)) = \varsigma(r, N)$ simultaneously for all $r \in R_{\mathrm{pocket}}$. For $N \equiv S$, every role satisfies $\varsigma(r, S) = 0 = \delta_{\mathrm{leaf}}(r)$. For $N \equiv N_1 N_2$ with child states $(q_{\mathrm{L}}, q_{\mathrm{R}}) = (\varsigma(r_{\mathrm{L}}, N_1), \varsigma(r_{\mathrm{R}}, N_2))$:

- *Spine and frame-wrapper roles:* Because $S$ is the unique atom of $\mathcal{T}_S$, a closed term $U \in \mathcal{T}_S$ satisfies $\operatorname{ls}(U) = 0$ if and only if $U \equiv S$, $\operatorname{ls}(U) = 1$ if and only if $U \equiv S u$, and $\operatorname{ls}(U) = 2$ if and only if $U \equiv (S v) j$. Every $F$-frame $(S a)((S b) j)$ has $\operatorname{ls} = 2$, so $\pi_{\mathrm{L}}(\varsigma(\mathsf{sp}, U)) = \pi_{\mathrm{R}}(\varsigma(\mathsf{sp}, U)) = \min\{5, \operatorname{ls}(U)\}$ holds for all $U \in \mathcal{T}_S$. On $\mathsf{sp}$, $N_1 N_2$ is an $F$-frame if and only if $q_{\mathrm{L}} = 1$ and $\pi_{\mathrm{R}}(q_{\mathrm{R}}) = 2$ (outputting $6$), and otherwise $\min\{5, \pi_{\mathrm{L}}(q_{\mathrm{L}}) + 1\} = \min\{5, \operatorname{ls}(N_1 N_2)\}$. On $\mathsf{L}_X$ ($X \ne \mathsf{ring}$, where $\varsigma(X, u) \le 15$), testing $\pi_{\mathrm{L}}(q_{\mathrm{L}}) = 0$ detects $N_1 \equiv S$ and outputs $7 + q_{\mathrm{R}} \in \{7,\dots,22\}$, else outputs $\min\{5, \pi_{\mathrm{L}}(q_{\mathrm{L}}) + 1\} \in \{2,\dots,5\}$; symmetrically, on $\mathsf{R}_Y$ ($Y \ne \mathsf{ring}$), testing $q_{\mathrm{L}} \ge 7$ detects $N_1 \equiv S v$ and propagates $q_{\mathrm{L}} = 7 + \varsigma(Y, v)$, else outputs $\min\{5, \pi_{\mathrm{L}}(q_{\mathrm{L}}) + 1\} \in \{1,3,4,5\}$. Consequently, $\pi_{\mathrm{L}}(\varsigma(\mathsf{L}_X, U)) = \pi_{\mathrm{R}}(\varsigma(\mathsf{R}_Y, U)) = \min\{5, \operatorname{ls}(U)\}$ for all $U \in \mathcal{T}_S$, and at any frame role $r \in \{\mathsf{hub}, \mathsf{body}, \mathsf{tmpl}, \mathsf{queue}, \mathsf{ver}_2, \mathsf{ver}_3, \mathsf{fld}\}$ the condition $q_{\mathrm{L}} \ge 7 \land q_{\mathrm{R}} \ge 7$ holds if and only if $N_1 N_2 \equiv (S a)((S b) j)$ with $(a, b)$ encoded by $(q_{\mathrm{L}} - 7, q_{\mathrm{R}} - 7)$ (while $\mathsf{L}_{\mathsf{ring}}$ and $\mathsf{R}_{\mathsf{ring}}$ encode valid wrappers as $1 + \varsigma(\mathsf{ring}, u) \in \{1,\dots,22\}$ and non-wrappers as $0$).
- *Fields, version chains, templates, and queue:* On non-frames ($q_{\mathrm{L}} < 7$ or $q_{\mathrm{R}} < 7$), $\delta_{\mathrm{app}}$ outputs $0$. On a frame $F(a, b, j)$: $\mathsf{fld}$ prepends the Boolean bit $b_0 = \mathbf{1}[\varsigma(\mathsf{sp}, a) = 6]$ to $\varsigma(\mathsf{fld}, b) \in \{0,\dots,15\}$, recording $1$ at the $0$-bit sentinel ($\varsigma(\mathsf{fld}, b) = 1$) and packing length-$1$, length-$2$, and length-$\ge 3$ prefixes into $\{2,3\}$, $\{4,\dots,7\}$, and $\{8,\dots,15\}$; $\mathsf{ver}_2$ and $\mathsf{ver}_3$ return $\varsigma(\mathsf{ver}_w, a)$ whenever $\varsigma(\mathsf{ver}_w, a) \ne 0$ (since newer records occupy the left spine) and otherwise decode the $2$-bit or $3$-bit prefix from $\varsigma(\mathsf{fld}, b)$; $\mathsf{tmpl}$ updates $(b_{\mathrm{idle}}, c_4) \in \{0,1\} \times \{0,1,2,3\}$ ($8$ states), where $b_{\mathrm{idle}}$ indicates an $\mathsf{idle}$ entry ($\mathtt{00}s$) and $c_4$ records the first $\mathsf{appending}$ bit ($2 + s$ for $\mathtt{11}s$), else presence of an $\mathsf{armed}$ entry ($1$ for $\mathtt{10}s$), else $0$; and $\mathsf{queue}$ updates the $12$-state code combining tail-allocation priority $\mathrm{su} \in \{0,1,2\}$ ($2$ for $\mathsf{staging}$ $\mathtt{01}s$, else $1$ for an uninitialized slot $\varsigma(\mathsf{ver}_3, a) = 0$, else $0$) with either presence of a $\mathsf{consuming}$ cell $\mathtt{10}b$ ($9 + \mathrm{su}$) or front $\mathsf{unconsumed}$ cell status $\in \{\text{none}, \mathtt{000}, \mathtt{001}\}$ ($3 u + \mathrm{su}$).
- *Phase body, modular phase ring, payload, hub, and root:* Role $\mathsf{body}$ maps $F(p_{\mathrm{ver}}, L_{\mathrm{tmpl}}, j)$ to $1$ on $\mathtt{11}$, $3 + \varsigma(\mathsf{tmpl}, L_{\mathrm{tmpl}}) \in \{3,\dots,10\}$ on $\mathtt{10}$, and $2$ otherwise. On $\mathsf{ring}$, a phase frame $F(e_0, R', j)$ combines $\varsigma(\mathsf{body}, e_0)$ with $\varsigma(\mathsf{ring}, R') \in \{0,\dots,21\}$ without counting ring length $m$: state $0$ marks a non-frame terminator; states $1 + 2 b_{\mathrm{hd}} + b_{\mathrm{last}} \in \{1,\dots,4\}$ indicate that a $\mathsf{handoff}$ phase ($\mathtt{11}$) occurs, storing only the head-active bit $b_{\mathrm{hd}} = \mathbf{1}[e_0\text{ has status }\mathtt{10}]$ and the last-handoff bit $b_{\mathrm{last}} \in \{0,1\}$ testing whether the first $\mathtt{11}$ phase is immediately followed by the ring terminator ($b_{\mathrm{last}} = \mathbf{1}[\varsigma(\mathsf{ring}, R') = 0]$ when $\varsigma(\mathsf{body}, e_0) = 1$, and inherited from $\varsigma(\mathsf{ring}, R')$ modulo $2$ when $\varsigma(\mathsf{body}, e_0) \ne 1$); state $5$ marks a nonempty suffix with no $\mathtt{11}$ or $\mathtt{10}$ phase; and states $6 + 8 b_{\mathrm{hd}} + c_{\mathrm{tmpl}} \in \{6,\dots,21\}$ record $b_{\mathrm{hd}}$ together with the $8$-state template summary $c_{\mathrm{tmpl}}$ of the first $\mathtt{10}$ phase when no $\mathtt{11}$ phase occurs. Finally, $\mathsf{pay}$ outputs $2$ when $\varsigma(\mathsf{ring}, \mathrm{Ring}) \ge 6$ and $\varsigma(\mathsf{queue}, \mathrm{Queue}) < 3$ and $1$ on all other valid payload frames; $\mathsf{hub}$ outputs $1$ iff $q_{\mathrm{L}} = 13$ ($\mathrm{Flag}$ is an $F$-frame) and $q_{\mathrm{R}} \ge 7$; and $\mathsf{rt}$ copies $q_{\mathrm{R}}$. Exhaustive traversal from $r_0 = \mathsf{rt}$ confirms that exactly $271$ pairs $(r, q) \in R_{\mathrm{pocket}} \times Q_{\mathrm{pocket}}$ are inhabited on $\mathcal{T}_S$.

At the root, $\varsigma(\mathsf{rt}, M) = 1 \in F_{\mathrm{halt}}$ holds if and only if $M \equiv P\,F(\mathrm{Flag}, \mathrm{Pay}, j_0)$ with $\mathrm{Flag}$ an $F$-frame, which coincides by Proposition 3.8 with $M \in L(\mathcal{H}_{11})$, so $\mathcal{T}_{\mathrm{pocket}}(M) = \mathsf{halt}$ holds if and only if $\sigma_{\mathrm{CTS}}(M) = \mathsf{halt}$.

When $M \notin L(\mathcal{H}_{11})$, we partition $P_{\mathrm{pocket}} = \{0,\dots,135\}$ into $54$ decision macro-states ($0 \dots 53$), $50$ two-edge frame-left stepping states ($54 \dots 103$), and $32$ three-edge frame-right stepping states ($104 \dots 135$). Entering the left slot $a$ of $F(a,b,j) \equiv (S a)((S b) j)$ for continuation $c \in \{0,\dots,49\}$ emits $\mathsf{left}(54 + c)$, after which state $54 + c$ emits $\mathsf{right}(c)$ along path $0 \cdot 1$; entering the right slot $b$ for $c \in \{0,\dots,31\}$ emits $\mathsf{right}(104 + c)$, after which state $104 + c$ emits $\mathsf{left}(54 + c)$ and state $54 + c$ emits $\mathsf{right}(c)$ along path $1 \cdot 0 \cdot 1$. Starting from $p_0 = 50$ at $M \equiv P H$, one right step reaches $H$ in state $51$: if $H$ or $\mathrm{Pay}$ is not an $F$-frame, both $\mathcal{T}_{\mathrm{pocket}}$ and $\sigma_{\mathrm{CTS}}$ return $\mathsf{stuck}$; if $\varsigma(\mathsf{pay}, \mathrm{Pay}) = 2$, state $51$ steps frame-left into $\mathrm{Flag}$ in opening state $p = 1$ (matching empty-queue halt opening at $[1,0,1]$); otherwise state $51$ steps frame-right into $\mathrm{Pay}$ in dispatch state $p = 0$.

At $\mathrm{Pay}$ ($p = 0$), $(q_{\mathrm{L}} - 1, q_{\mathrm{R}} - 7) = (\varsigma(\mathsf{ring}, \mathrm{Ring}), \varsigma(\mathsf{queue}, \mathrm{Queue}))$ determines every branch of Definition 4.3(ii):

- *Modular handoff ($1 \le \varsigma(\mathsf{ring}, \mathrm{Ring}) \le 4$):* If $\varsigma(\mathsf{queue}, \mathrm{Queue}) \ge 9$, state $0$ steps frame-right to $\mathrm{Queue}$ in seeker state $p = 17$ to append $\mathtt{11}b$ to the first $\mathsf{consuming}$ cell. Otherwise it steps frame-left to $\mathrm{Ring}$ in handoff-root state $p = 32$. At the root phase $e_0$ with tail $R'$, if $\varsigma(\mathsf{body}, e_0) = 1$ ($j = 0$ is $\mathtt{11}$), then $\varsigma(\mathsf{ring}, R') = 0$ ($m = 1$) re-activates $e_0$ to $\mathtt{10}$, $b_{\mathrm{hd}}(R') = 1$ (phase $1$ already $\mathtt{10}$) deactivates $e_0$ to $\mathtt{00}$, and $b_{\mathrm{hd}}(R') = 0$ steps to the head of $R'$ ($p = 25$) to write $\mathtt{10}$. If $\varsigma(\mathsf{body}, e_0) \ne 1$ ($j > 0$), $b_{\mathrm{last}}(R') = 1$ means $j = m - 1$ and $(j + 1) \bmod m = 0$: if $e_0$ is already $\mathtt{10}$ ($\varsigma(\mathsf{body}, e_0) \ge 3$), state $32$ scans $R'$ ($p = 26$) to deactivate the first $\mathtt{11}$ phase to $\mathtt{00}$, else it activates $e_0$ at the root to $\mathtt{10}$. Finally, if $j > 0$ and $b_{\mathrm{last}}(R') = 0$ ($0 < j < m - 1$), state $32$ scans $R'$ ($p = 27$) to the first $\mathtt{11}$ phase and inspects $b_{\mathrm{hd}}$ of its right sibling, either deactivating phase $j$ to $\mathtt{00}$ or advancing one frame ($p = 25$) to activate phase $j + 1$ to $\mathtt{10}$.
- *Active-phase dispatch ($\varsigma(\mathsf{ring}, \mathrm{Ring}) \ge 6$):* Decoding $(b_{\mathrm{idle}}, c_4)$ of the first $\mathtt{10}$ phase alongside $\varsigma(\mathsf{queue}, \mathrm{Queue}) \ge 3$ (when $< 9$, since $\varsigma(\mathsf{pay}, \mathrm{Pay}) \ne 2$) or $\varsigma(\mathsf{queue}, \mathrm{Queue}) \ge 9$ dispatches to the unique queue seeker $p \in \{16,\dots,21\}$ (locating the unopened queue tail, first $\mathsf{consuming}$, first $\mathsf{unconsumed}$, first $\mathsf{staging}$, or first uninitialized cell) or active-phase seeker $p \in \{28,\dots,31\}$ (descending via $p \in \{33,34,35\}$ to $\mathsf{ver}_2$ or via $p \in \{36,37,38\}$ and template seekers $p \in \{22,23,24\}$ to the first $\mathsf{idle}$, $\mathsf{armed}$, or $\mathsf{appending}$ template), matching rules (ii)(a)–(b) of Definition 4.3.
- *Version-chain extension and local generator opening:* Width-$2$ writers $p \in \{39,40,41\}$ and width-$3$ writers $p \in \{42,\dots,49\}$ walk the left spine while $\varsigma(\mathsf{fld}, b) \ge 2^w$ and enter $\mathsf{fld}$ in states $p \in \{2,\dots,15\}$ on the first incomplete record (or open an uninitialized chain leaf), stepping down $\mathsf{fld}$ until reaching the first $1$-bit slot whose left child is not yet an $F$-frame ($\varsigma(\mathsf{sp}, a) \ne 6$) or an unopened field/sentinel generator. On any unopened or mid-opening generator, states $p \in \{1, 52, 53\}$ inspect $(\pi_{\mathrm{L}}(q_{\mathrm{L}}), \pi_{\mathrm{R}}(q_{\mathrm{R}}))$ to execute the depth-$\le 5$ redex probe of Lemma 3.5(i): emitting $\mathsf{contract}$ when $\pi_{\mathrm{L}}(q_{\mathrm{L}}) = 2$ ($S X Y Z$), $\mathsf{left}(53)$ when $\pi_{\mathrm{L}}(q_{\mathrm{L}}) = 3$ ($S X Y Z\,W$, where state $53$ contracts at $\pi_{\mathrm{L}} = 2$), $\mathsf{right}(52)$ when $(\pi_{\mathrm{L}}, \pi_{\mathrm{R}}) = (1, 4)$ ($S\,(S X Y Z\,W)$), and $\mathsf{right}(53)$ when $(\pi_{\mathrm{L}}, \pi_{\mathrm{R}}) = (1, 3)$ ($S\,(S X Y Z)$).

Thus $\mathrm{Loc}_{\mathcal{T}_{\mathrm{pocket}}}(p_0, \widehat{M}_0)$ returns the exact redex address (or $\bot$) selected by $\sigma_{\mathrm{CTS}}(M)$, proving $\mathcal{T}_{\mathrm{pocket}}(M) = \sigma_{\mathrm{CTS}}(M)$ for every closed $M \in \mathcal{T}_S$. Because $M \in \mathcal{T}_S$ and $M \to_S M'$ imply $M' \in \mathcal{T}_S$, induction on $k \ge 0$ shows that the $k$-step trajectories of $\mathcal{T}_{\mathrm{pocket}}$ and $\sigma_{\mathrm{CTS}}$ starting from $T_0 = \mathcal{E}_{\mathrm{CTS}}(P, w) \in \mathcal{T}_S$ coincide identically; Proposition 4.4 and Theorem 4.5 therefore yield $D_{\mathrm{seed}} \to_S^* T_0$, bidirectional halting equivalence, terminal readback $\mathcal{D}_{\mathrm{CTS}}(T_k) = (i_{\mathrm{fin}}, \varepsilon)$, and the quadratic trajectory bound $|T_k| \le 35{,}000(\|(P, w)\| + k + 1)^2$. $\square$

*Remark 4.8 (Helper-state compression and linear transition complexity).* 
Relative to the $4{,}376{,}490{,}905$-state root-restarted zipper walker $\sigma_{\mathrm{TM}}$ of Section 3, $\mathcal{T}_{\mathrm{pocket}}$ removes the universal transition table from the controller and compresses the reachable state footprint to $271$ role-state pairs in Pass 1 together with $136$ single-edge pointer states in Pass 2 ($407$ active state configurations in total, a reduction exceeding $1.075 \times 10^7$-fold), while tightening the per-contraction transition bound from $3500(2|M| - 1)$ cursor micro-ticks to at most $2|M| - 3 + \mathrm{depth}(M)$ transitions and less than $5$ bits of Pass-1 state per tree node.

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
Theorem 5.2 clarifies the relationship between controlled pure-$S$ universality and tree-walking automata theory. Read-only finite-state tree-walking automata cannot recognize all regular tree languages [12], whereas Kutrib and Meyer showed that equipping a finite control with a dynamically growing tree-walking storage already recognizes non-semilinear unary languages strictly beyond regular languages even under real-time non-erasing operation [40, 41]. Theorem 5.2 establishes that when multi-pass stateless root-restarted navigation is allowed to mutate an unlabeled tree solely via $\mathsf{Leaf} \to_{\mathrm{sp}} \mathsf{Node}(\mathsf{Leaf},\mathsf{Leaf})$, the resulting system is Turing-complete. Thus, when a universal machine table is permitted inside the finite controller (as in [27] and Theorem 3.9), universality stems from addressable growing tree storage rather than from combinatory dynamics. What $\mathrm{CL}(S)$ genuinely contributes beyond $\to_{\mathrm{sp}}$ is in-tree duplicative computation $S X Y Z \to_S (X Z)(Y Z)$, which enables both the program-free selector $\sigma_{\mathrm{CTS}}$ and universal seed genesis from $D_{\mathrm{seed}}$ in Section 4.

### 5.2. Constant-Step Multiway Halting Shortcuts

We next show that removing external evaluation-order selection in favor of unrestricted multiway rewriting $\to_S^*$ causes immediate soundness collapse across both major pure-$S$ encoding architectures: unopened-generator halt flags (Sections 3–4) and live/tombstone $D \cdot Q$ tag dispatchers [27].

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

Proposition 5.4(ii) raises the question of whether one could redesign pure-$S$ branch dispatchers using "Church-Boolean" thunk gates $B_0, B_1 \in \mathcal{T}_S$ so that $B_0\,x_0\,x_1$ activates only the first branch thunk $x_0$ while $B_1\,x_0\,x_1$ activates only the second branch thunk $x_1$ (without triggering a divergent computation hidden behind $x_0$). On the first branch, $T \equiv S S$ succeeds in one step:

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

- (i) the class $\mathcal{W}_0$ is generated by $C x_0 \in \mathcal{W}_0$ for every $C \in \mathcal{F}$, and $W_1 W_2 \in \mathcal{W}_0$ whenever $W_1, W_2 \in \mathcal{W}_0$;
- (ii) the class $\mathcal{O}$ is generated by $W x_1 \in \mathcal{O}$ for every $W \in \mathcal{W}_0$, and $P U \in \mathcal{O}$ whenever $P \in \mathcal{O}$ and $U \in \mathcal{F}$.

Every term in $\mathcal{W}_0$ is an application (so $S \notin \mathcal{W}_0$ and $x_k \notin \mathcal{W}_0$) and contains no occurrence of $x_1$. Consequently:

- If $S P \in \mathcal{W}_0$, then since $S \notin \mathcal{W}_0$, it cannot arise from $W_1 W_2$, so $S P \equiv C x_0$ and hence $P \equiv x_0$.
- If $S P Q \in \mathcal{W}_0$, either $S P Q \equiv C x_0$ (giving $Q \equiv x_0$) or $S P \in \mathcal{W}_0$ (giving $P \equiv x_0$). Thus *every* arity-$2$ prefix $S P Q \in \mathcal{W}_0$ satisfies $P \equiv x_0$ or $Q \equiv x_0$.
- Similarly, every $T' \in \mathcal{O}$ has $\operatorname{ls}(T') \ge 2$ (so $T' \not\equiv S$, $T' \not\equiv x_1$, and $T' \not\equiv S P$), and if $T' \equiv S P Q \in \mathcal{O}$, inversion forces $T' \equiv W x_1$ with $W \equiv S P \in \mathcal{W}_0$, whence $P \equiv x_0$. Moreover, no term in $\mathcal{O}$ satisfies $\mathrm{call}_1$: in $W x_1$, $W \not\equiv x_1$ and $x_1$ is absent from $W$; in $P U$, $P \not\equiv x_1$ and $x_1$ is absent from $U \in \mathcal{F}$.

We claim that if $W \in \mathcal{W}_0$ and $W \to_S W'$, then either $W' \in \mathcal{W}_0$ or $\mathrm{call}_0(W')$ holds. By structural induction on $W \in \mathcal{W}_0$: if $W \equiv C x_0$ ($C \in \mathcal{F}$), either $C \to_S C' \in \mathcal{F}$ (giving $C' x_0 \in \mathcal{W}_0$) or $C \equiv S X Y$ with $X, Y \in \mathcal{F}$ and $S X Y x_0 \to_r (X x_0)(Y x_0) \in \mathcal{W}_0$; if $W \equiv W_1 W_2$, contextual steps in $W_1$ or $W_2$ preserve $\mathcal{W}_0$ or establish $\mathrm{call}_0$ by induction, whereas a root step requires $W_1 \equiv S P Q \in \mathcal{W}_0$, so $P \equiv x_0$ or $Q \equiv x_0$, and the contractum $(P W_2)(Q W_2)$ contains $x_0 W_2$, making $\mathrm{call}_0(W')$ true.

Lifting by structural induction to $T' \in \mathcal{O}$ shows that whenever $T' \to_S T''$, either $T'' \in \mathcal{O}$ or $\mathrm{call}_0(T'')$ holds: for $T' \equiv W x_1$, a left step $W \to_S W'$ yields $W' x_1 \in \mathcal{O}$ or $\mathrm{call}_0(W' x_1)$, while a root step forces $W \equiv S P Q \in \mathcal{W}_0$, hence $P \equiv x_0$ or $Q \equiv x_0$, producing $x_0 x_1$ inside $(P x_1)(Q x_1)$; for $T' \equiv P U$ ($U \in \mathcal{F}$), left steps use the induction hypothesis, right steps $U \to_S U' \in \mathcal{F}$ preserve $\mathcal{O}$, and a root step forces $P \equiv S X Y \in \mathcal{O}$, whence $X \equiv x_0$ and the contractum $(x_0 U)(Y U)$ satisfies $\mathrm{call}_0$.

Finally, $M x_0 \in \mathcal{W}_0$, $(M x_0) x_1 \in \mathcal{O}$, and appending $U_1, \dots, U_m \in \mathcal{F}$ places $T_{\mathrm{start}} \equiv M x_0 x_1 U_1\cdots U_m \in \mathcal{O}$. By induction along $T_{\mathrm{start}} \to_S^* N$ combined with $\to_S$-monotonicity of $\mathrm{call}_0$, either $N \in \mathcal{O}$—which contradicts $\mathrm{call}_1(N)$ since $\mathrm{call}_1$ vanishes on $\mathcal{O}$—or $\mathrm{call}_0(N)$ holds.
 $\square$

## 6. Finite $S$-Algebras, Automaton-Free Book Proofs, Böhm Faithfulness Dichotomy, and Order Hierarchy

When external tree-walking controllers are removed and closed $S$-terms evolve solely under the intrinsic rewrite relation $\to_S$, the dynamics of $\mathrm{CL}(S)$ is governed by a hierarchy of finite combinatory $S$-algebras together with elementary syntactic invariants. Because every ground $S$-term is built from a single leaf constant $S$ by binary application, any finite $S$-algebra $\mathcal{A} = (Q, q_0, \odot)$ (Definition 2.8) defines a deterministic bottom-up tree automaton running in $2|M| - 1$ table lookups on unfolded syntax trees (and in linear DAG size on shared representations) while remaining invariant under unrestricted conversion $=_S$ by (2.3). In this section we develop this algebraic and syntactic theory constructively without König's lemma or classical choice. First, we establish collapsed finite-rank normalization for Waldmann's $39$-state normalization algebra [66, 4], prove automaton-free head conservation, and construct a pointwise-minimal pure multiplier potential ($B \equiv 0$) resolving Question 10 and Footnote 4 of Barendregt, Endrullis, Klop, and Waldmann [4]. Next, we compress completeness of the $39$-state productivity algebra for Question 5 to $10$ ranks while proving $113$-state Myhill–Nerode minimality of its joint solvability product. Finally, we give short automaton-free proofs of Questions 7 and 31 alongside a complete Böhm-tree faithfulness dichotomy and a constructive convertibility decider across $\mathrm{Prod} \times \mathcal{T}_S$ advancing Scott's Question 30, and we determine the minimal $S$-algebras of sizes $35$, $12$, and $3$ governing the functional order hierarchy $\{0, 1, 2, 3\}$.

Table 5 summarizes the finite $S$-algebras, deterministic tree automata, and minimal quotient or product subalgebras studied across Sections 6–9. Given $F \subseteq Q$, we write $L(\mathcal{A}, F) = \{ M \in \mathcal{T}_S : \llbracket M \rrbracket_{\mathcal{A}} \in F \}$, retaining the abbreviations $T \equiv S S$, $A \equiv S S S$, right combs $R_n$ ($n \ge 1$, $|R_n| = n$), leaf count $|M|$, left-spine arity $\operatorname{ls}(M)$, and right-spine depth $\operatorname{rs}(M)$ from Section 2.

**Table 5.** Finite $S$-algebras, deterministic bottom-up tree automata, and minimal quotient or product subalgebras in $\mathrm{CL}(S)$.

| Structure | $\vert Q\vert$ | $S$-Law | Recognized Property or Algebraic Invariant on $\mathcal{T}_S$ |
| :--- | :---: | :---: | :--- |
| $\mathcal{A}_{\mathrm{ord},3}$ | $3$ | Yes | Minimal $S$-algebra for functional order $3$ (right combs $R_n$; Theorem 6.25) |
| $\mathcal{D}_4$ | $4$ | Yes | Functionally complete Boolean algebra realizing $11$-leaf normal-form Rule 110 |
| $\mathcal{B}_Z$ | $8$ | DTA | Accepts step-$t$ reducts of $Z_{\mathrm{Zac}}$ iff $t = \tfrac{1}{2}n(n+3)$ across six strategies |
| $\mathcal{A}_{\mathrm{ord},2}$ | $12$ | Yes | Minimal $S$-algebra deciding $\{\operatorname{ord} = 2\}$ and $\{\operatorname{ord} \ge 2\}$ (Theorem 6.25) |
| $\mathcal{A}_{\mathrm{HN}}$ | $35$ | Yes | Minimal $S$-algebra for $\mathrm{HN}$, $\{\operatorname{ord} = 0\}$, $\{\operatorname{ord} = 1\}$, and $4$-valued $\operatorname{ord}$ (Question 10) |
| $\mathcal{A}_{36}$ | $36$ | Yes | Refines $\infty_{\mathrm{HN}}$ into $\{q_{34}, q_{35}\}$, separating $A A A \neq_S A A A S$ (Question 31) |
| $\mathcal{A}_{\mathrm{SN}}$ | $39$ | Yes | Minimal $S$-algebra for strong and weak normalization ($\llbracket M \rrbracket_{\mathrm{SN}} \neq \infty_{\mathrm{SN}}$; Theorem 6.2) |
| $\mathcal{A}_P$ | $39$ | Yes | Böhm-tree productivity ($\llbracket M \rrbracket_P \neq \infty_P$; Question 5, Theorem 6.14) |
| $\mathcal{A}_P \times \mathcal{A}_{\mathrm{SN}}$ | $44$ | Yes | Reachable pairs isolating $(q_{29}, \infty_{\mathrm{SN}})$ as unique non-$\mathrm{SN}$ productive redex fiber |
| $\mathcal{A}_{\mathrm{SN}} \times \mathcal{A}_{\mathrm{HN}}$ | $112$ | Yes | Reachable pairs: $94$ in $\mathrm{SN}$, $17$ in $\mathrm{HN} \setminus \mathrm{SN}$, and $1$ in $\overline{\mathrm{HN}}$ |
| $\mathcal{A}_P \times \mathcal{A}_{\mathrm{HN}}$ | $113$ | Yes | Myhill–Nerode minimal $(\mathrm{Prod}, \mathrm{HN})$ algebra ($95$ accepting, $18$ rejecting; Proposition 6.15) |
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

We define the $39$-state combinatory $S$-algebra $\mathcal{A}_{\mathrm{SN}} = (Q_{\mathrm{SN}}, q_0, \odot_{\mathrm{SN}})$ with carrier $Q_{\mathrm{SN}} = \{q_0, q_1, \dots, q_{37}, \infty_{\mathrm{SN}}\}$ (identifying $\infty_{\mathrm{SN}} = q_{38}$), accepting subset $F_{\mathrm{SN}} = Q_{\mathrm{SN}} \setminus \{\infty_{\mathrm{SN}}\}$ of cardinality $38$, and transition operation $\odot_{\mathrm{SN}}$ obtained by transposing Figure 5.11 of Barendregt et al. [4, p. 82] and adjoining $\infty_{\mathrm{SN}}$ as a two-sided absorbing sink ($\infty_{\mathrm{SN}} \odot_{\mathrm{SN}} y = x \odot_{\mathrm{SN}} \infty_{\mathrm{SN}} = \infty_{\mathrm{SN}}$ for all $x, y \in Q_{\mathrm{SN}}$). Direct evaluation over all $39^3 = 59{,}319$ triples in $Q_{\mathrm{SN}}^3$ confirms (2.3).

**Theorem 6.2 (Regularity of strong normalization [66]; [4, Theorem 9]).** 
For every closed $S$-term $M \in \mathcal{T}_S$,

$$
M \in \mathrm{SN} \;\Longleftrightarrow\; M \in \mathrm{WN} \;\Longleftrightarrow\; \llbracket M \rrbracket_{\mathrm{SN}} \neq \infty_{\mathrm{SN}},
$$

and membership $M \in \mathrm{SN}$ is decidable in $2|M| - 1$ deterministic table lookups.

*Proof.* 
Equivalence of $M \in \mathrm{SN}$ and $M \in \mathrm{WN}$ holds by Lemma 6.1(ii). For soundness (that $M \in \mathrm{WN}$ implies $\llbracket M \rrbracket_{\mathrm{SN}} \neq \infty_{\mathrm{SN}}$), inspection of row $q_0$ and of all $38^2 = 1{,}444$ pairs $(x, y) \in F_{\mathrm{SN}}^2$ in $\mathcal{A}_{\mathrm{SN}}$ shows that $q_0 \neq \infty_{\mathrm{SN}}$, that $x \neq \infty_{\mathrm{SN}}$ implies $q_0 \odot_{\mathrm{SN}} x \neq \infty_{\mathrm{SN}}$, and that $x, y \neq \infty_{\mathrm{SN}}$ implies $(q_0 \odot_{\mathrm{SN}} x) \odot_{\mathrm{SN}} y \neq \infty_{\mathrm{SN}}$. Structural induction on the grammar (6.1) therefore yields $\llbracket V \rrbracket_{\mathrm{SN}} \neq \infty_{\mathrm{SN}}$ for every $V \in \mathcal{N}$. If $M \to_S^* V \in \mathcal{N}$, conversion invariance of $\mathcal{A}_{\mathrm{SN}}$ gives $\llbracket M \rrbracket_{\mathrm{SN}} = \llbracket V \rrbracket_{\mathrm{SN}} \neq \infty_{\mathrm{SN}}$.

For constructive completeness (that $\llbracket M \rrbracket_{\mathrm{SN}} \neq \infty_{\mathrm{SN}}$ implies $M \to_S^* V$ for some $V \in \mathcal{N}$), we avoid König's lemma by constructing a total recursive normalization operator $\mathrm{app}_{\mathcal{N}}(F, Z) \in \mathcal{N}$ satisfying $F Z \to_S^* \mathrm{app}_{\mathcal{N}}(F, Z)$ for all canonical normal forms $F, Z \in \mathcal{N}$ with $\llbracket F \rrbracket_{\mathrm{SN}} \odot_{\mathrm{SN}} \llbracket Z \rrbracket_{\mathrm{SN}} \neq \infty_{\mathrm{SN}}$. Once $\mathrm{app}_{\mathcal{N}}$ is established, structural induction on $M$ normalizes every accepted term: $\mathrm{norm}(S) = S$, and for $M \equiv L R$ with $\llbracket L R \rrbracket_{\mathrm{SN}} \neq \infty_{\mathrm{SN}}$, the two-sided sink property of $\infty_{\mathrm{SN}}$ forces $\llbracket L \rrbracket_{\mathrm{SN}} \neq \infty_{\mathrm{SN}}$ and $\llbracket R \rrbracket_{\mathrm{SN}} \neq \infty_{\mathrm{SN}}$, whence $L R \to_S^* \mathrm{norm}(L)\,\mathrm{norm}(R) \to_S^* \mathrm{app}_{\mathcal{N}}(\mathrm{norm}(L), \mathrm{norm}(R)) \in \mathcal{N}$.

Rather than storing an unstructured $59{,}319$-entry three-dimensional array, the rank map $\tau_{\mathrm{SN}} \colon Q_{\mathrm{SN}}^3 \to \{0, 1, \dots, 6\}$ collapses to a two-dimensional sub-rank matrix $\hat{\tau}_{\mathrm{SN}} \colon Q_{\mathrm{SN}}^2 \to \{0, 1, \dots, 6\}$ modified on $35$ explicit overrides ($34$ entries at $x = q_1$ assigned rank $2$, plus the single triple $(q_9, q_0, q_1)$ assigned rank $3$), setting $\tau_{\mathrm{SN}}(x, y, z) = \hat{\tau}_{\mathrm{SN}}((q_0 \odot_{\mathrm{SN}} x) \odot_{\mathrm{SN}} y,\, z)$ everywhere else. Let $I_2 \subseteq F_{\mathrm{SN}}$ denote the set of states inhabited by spine-$2$ normal forms $S A_1 A_2$. Finite verification across $F_{\mathrm{SN}}^3$ confirms $\tau_{\mathrm{SN}}(x, y, z) \le \hat{\tau}_{\mathrm{SN}}((q_0 \odot_{\mathrm{SN}} x) \odot_{\mathrm{SN}} y,\, z)$ and establishes two strict decrease laws whenever $((q_0 \odot_{\mathrm{SN}} x) \odot_{\mathrm{SN}} y) \odot_{\mathrm{SN}} z \neq \infty_{\mathrm{SN}}$, alongside $\hat{\tau}_{\mathrm{SN}}(x, z) \le \tau_{\mathrm{SN}}(x, y, z)$ and $\hat{\tau}_{\mathrm{SN}}(y, z) \le \tau_{\mathrm{SN}}(x, y, z)$:

$$
\begin{aligned}
\tau_{\mathrm{SN}}(u, z, y \odot_{\mathrm{SN}} z) &\;<\; \tau_{\mathrm{SN}}(q_0 \odot_{\mathrm{SN}} u, y, z)
&&\textrm{whenever } x = q_0 \odot_{\mathrm{SN}} u, \\
\hat{\tau}_{\mathrm{SN}}(x \odot_{\mathrm{SN}} z, y \odot_{\mathrm{SN}} z) &\;<\; \tau_{\mathrm{SN}}(x, y, z)
&&\textrm{whenever } x \in I_2.
\end{aligned} \tag{6.2–6.3}
$$

Assign to each call $(F, Z)$ its rank $r(F, Z) = 0$ if $F \equiv S$ or $F \equiv S X$, and $r(S X Y, Z) = \tau_{\mathrm{SN}}(\llbracket X \rrbracket_{\mathrm{SN}}, \llbracket Y \rrbracket_{\mathrm{SN}}, \llbracket Z \rrbracket_{\mathrm{SN}}) \ge 1$ otherwise. We proceed by well-founded lexicographic induction on $(r(F, Z), |F|) \in \mathbb{N}^2$. If $F \equiv S$ or $F \equiv S X$, then $F Z \in \mathcal{N}$ already. If $F \equiv S X Y$ with $X, Y \in \mathcal{N}$, then $(S X Y) Z \to_S (X Z)(Y Z)$, and conversion invariance plus the two-sided sink property ensure $\llbracket X Z \rrbracket_{\mathrm{SN}} \neq \infty_{\mathrm{SN}}$, $\llbracket Y Z \rrbracket_{\mathrm{SN}} \neq \infty_{\mathrm{SN}}$, and $\llbracket (X Z)(Y Z) \rrbracket_{\mathrm{SN}} \neq \infty_{\mathrm{SN}}$. Since $|Y| < |S X Y|$ and $r(Y, Z) \le \hat{\tau}_{\mathrm{SN}}(\llbracket Y \rrbracket_{\mathrm{SN}}, \llbracket Z \rrbracket_{\mathrm{SN}}) \le r(S X Y, Z)$, the induction hypothesis normalizes $Y Z \to_S^* W \in \mathcal{N}$ with $\llbracket W \rrbracket_{\mathrm{SN}} = \llbracket Y \rrbracket_{\mathrm{SN}} \odot_{\mathrm{SN}} \llbracket Z \rrbracket_{\mathrm{SN}}$. Similarly, $|X| < |S X Y|$ and $r(X, Z) \le r(S X Y, Z)$ normalize $X Z \to_S^* V \in \mathcal{N}$ with $\llbracket V \rrbracket_{\mathrm{SN}} = \llbracket X \rrbracket_{\mathrm{SN}} \odot_{\mathrm{SN}} \llbracket Z \rrbracket_{\mathrm{SN}}$. We now branch on $X \in \mathcal{N}$:

- (i) If $X \equiv S$, then $V \equiv S Z$ and $(X Z)(Y Z) \to_S^* S Z W \in \mathcal{N}$, completing normalization.
- (ii) If $X \equiv S U$ with $U \in \mathcal{N}$, then $V \equiv S U Z$, and by (6.2) the outer call $(S U Z, W)$ has strictly smaller first component $\tau_{\mathrm{SN}}(\llbracket U \rrbracket_{\mathrm{SN}}, \llbracket Z \rrbracket_{\mathrm{SN}}, \llbracket W \rrbracket_{\mathrm{SN}}) < r(S(S U)Y, Z)$.
- (iii) If $X \equiv S A_1 A_2$ with $A_1, A_2 \in \mathcal{N}$, then $\llbracket X \rrbracket_{\mathrm{SN}} \in I_2$, and by (6.3) we have $r(V, W) \le \hat{\tau}_{\mathrm{SN}}(\llbracket V \rrbracket_{\mathrm{SN}}, \llbracket W \rrbracket_{\mathrm{SN}}) < r(S X Y, Z)$, so $\mathrm{app}_{\mathcal{N}}(V, W) \in \mathcal{N}$ terminates.
 $\square$

*Remark 6.3 (Automaton minimization and table orientation).* 
Two bibliographical details merit record when comparing implementations of $\mathcal{A}_{\mathrm{SN}}$ across the literature. First, Waldmann's original top-down grammar construction [65, 66] yielded $43$ non-terminals; Endrullis, de Vrijer, and Waldmann [25, Section 5, p. 15] subsequently applied local termination and Myhill–Nerode minimization to obtain the minimal $39$-state totalized deterministic bottom-up tree automaton ($38$ accepting states and $1$ undefined sink). Second, in Figure 5.11 of Barendregt, Endrullis, Klop, and Waldmann [4, p. 82], the printed $38 \times 38$ array indexes the left-applicand state $x = \llbracket M \rrbracket_{\mathrm{SN}}$ horizontally across columns and the right-applicand state $y = \llbracket N \rrbracket_{\mathrm{SN}}$ vertically down rows, transposed relative to the figure caption; reading rows as left applicands and columns as right applicands violates (2.3) already on $T T T \equiv (S S)(S S)(S S)$.

### 6.2. Automaton-Free Head Conservation, Optimal Multiplier Potential, and Question 10

Recall from Definition 2.6(i)–(ii) that a closed $S$-term $M \in \mathcal{T}_S$ lies in $\mathrm{HNF}$ when $\operatorname{ls}(M) \le 2$, is solvable ($M \in \mathrm{HN}$) when $M \to_S^* H$ for some $H \in \mathrm{HNF}$, and lies in $\mathrm{RNF}$ when no reduction from $M$ ever contracts at the root. In classical treatments [1], equivalence between multiway solvability ($M \in \mathrm{HN}$) and termination of deterministic head reduction $\to_h$ invokes full standardization. In $\mathrm{CL}(S)$, however, a direct weighted-parallel pullback establishes head conservation constructively without standardization or finite automata. Write $\mathrm{SHN} \subseteq \mathcal{T}_S(\mathcal{V})$ for the set of terms $M$ that are *strongly head-normalizing*, meaning that deterministic head reduction $\to_h$ from $M$ is well-founded.

**Lemma 6.4 (Automaton-free head conservation).** 
For all open or closed $S$-terms $M, N \in \mathcal{T}_S(\mathcal{V})$, if $M \to_S N$ and $N \in \mathrm{SHN}$, then $M \in \mathrm{SHN}$. Consequently, for every closed $S$-term $M \in \mathcal{T}_S$, one has $M \in \mathrm{HN}$ if and only if $M \in \mathrm{SHN}$.

*Proof.* 
Recall from the proof of Proposition 2.2(iii) the weighted parallel reduction relation $M \Rightarrow_w N$ ($w \in \mathbb{N}$), where atoms have weight $0$, application satisfies $A_1 A_2 \Rightarrow_{w_1 + w_2} B_1 B_2$, redex contraction satisfies $S X Y Z \Rightarrow_{1 + w_X + w_Y + 2 w_Z} (X' Z')(Y' Z')$, and $M \to_S N$ implies $M \Rightarrow_1 N$. Structural induction on $M \Rightarrow_w N$ yields a sharp head-projection alternative for any head step $M \to_h M_1$:

- (i) if $M \equiv S X Y Z$ is contracted at the root in $M \Rightarrow_w N$, then $M_1 \equiv (X Z)(Y Z)$ satisfies $M_1 \Rightarrow_{w_1} N$ with $w_1 = (w_X + w_Z) + (w_Y + w_Z) < 1 + w_X + w_Y + 2 w_Z = w$ (no left-child head step can occur inside $S X Y$, whose left-spine arity is $2$);
- (ii) if $M \equiv A_1 A_2 \Rightarrow_{w_1 + w_2} B_1 B_2$ and $M \to_h M_1$ contracts at the root ($A_1 \equiv S X Y$, forcing $B_1 \equiv S X' Y'$), then $N \equiv S X' Y' B_2 \to_h (X' B_2)(Y' B_2) \equiv N_1$ with $M_1 \Rightarrow_{w'} N_1$; and if $A_1 \to_h A_1'$, the induction hypothesis on $A_1 \Rightarrow_{w_1} B_1$ either decreases $w_1$ while keeping $B_1 B_2$ fixed or steps $B_1 \to_h B_1'$ and hence $B_1 B_2 \to_h B_1' B_2$.

Well-founded outer induction on $N \in \mathrm{SHN}$ combined with inner induction on $w \in \mathbb{N}$ therefore shows that $N \in \mathrm{SHN}$ and $M \Rightarrow_w N$ imply $M \in \mathrm{SHN}$. Since every $H \in \mathcal{T}_S(\mathcal{V})$ with $\operatorname{ls}(H) \le 2$ admits no head step and thus lies in $\mathrm{SHN}$, induction along $M \to_S^* H$ proves that $M \in \mathrm{HN}$ implies $M \in \mathrm{SHN}$. Conversely, on closed $M \in \mathcal{T}_S$, iterating the unique partial head-step function along $\mathrm{SHN}$ terminates at a closed head-irreducible term $H$, which necessarily satisfies $\operatorname{ls}(H) \le 2$ and witnesses $M \in \mathrm{HN}$.
 $\square$

Before introducing the $35$-state head-normalization algebra, we record three syntactic rigidity properties of multi-argument applications in $\mathrm{CL}(S)$ refining Visser's variable-tail method and Proposition 2.4(iii).

**Lemma 6.5 (Spine-$2$ persistence, Fibonacci $2$-HNFs, and third-argument head exclusion).** 
Let $U \in \mathcal{T}_S$ be a closed $S$-term and let $x, y, z \in \mathcal{V}$ be distinct variables.

- (i) *Persistence of spine arity at least $2$:* For all open or closed terms $A_1, A_2, A_3, W \in \mathcal{T}_S(\mathcal{V})$, neither $(A_1 A_2) A_3 \to_S^* S$ nor $(A_1 A_2) A_3 \to_S^* S W$ holds. Consequently, $F X \to_S^* S W$ implies $F \equiv S$ and $X \to_S^* W$.
- (ii) *Fibonacci classification of parametric $2$-HNFs:* Recall from Definition 2.1 the closed right combs $R_1 \equiv S$ and $R_{n+1} \equiv S R_n$ ($n \ge 1$), and define the Fibonacci word trees $W_0(x, y) \equiv x$, $W_1(x, y) \equiv y$, and $W_{m+2}(x, y) \equiv W_m(x, y)\,W_{m+1}(x, y)$. Then $U x y \to_S^* S P Q$ holds if and only if there exists $k \in \mathbb{N}$ such that $U \to_S^* R_{k+1}$, $P \equiv W_k(x, y)$, and $Q \equiv W_{k+1}(x, y)$. Moreover, if $U x y \to_S^* S P Q$ with $U \not\equiv S$, then both right spines of $P$ and $Q$ terminate in $y$.
- (iii) *Third-argument head exclusion:* Whenever $U x y z \to_S^* H$ with $H$ in open head normal form (either $\operatorname{ls}(H) \le 2$ with head $S$, or head in $\mathcal{V}$), the leftmost leaf of $H$ belongs to $\{x, y\}$ and is never $z$ or $S$.

*Proof.* 
For (i), define the predicate $\Phi_2(K)$ asserting $\operatorname{ls}(K) \ge 2$, meaning $K \equiv (K_1 K_2) K_3$. A root contraction $S X Y Z \to_S (X Z)(Y Z)$ produces a term of left-spine arity $\operatorname{ls}(X Z) + 1 \ge 2$; a left step $(K_1 K_2) K_3 \to_S L' K_3$ satisfies $\operatorname{ls}(L') \ge 1$ by inspection of root, left, and right subcases on $K_1 K_2$; and a right step leaves $\operatorname{ls}$ unchanged. Induction along $\to_S^*$ shows that $\Phi_2$ is closed forward under reduction, excluding $S$ ($\operatorname{ls} = 0$) and $S W$ ($\operatorname{ls} = 1$). If $F X \to_S^* S W$, then $F$ cannot be a variable (head variable $v$ is preserved) or an application $F_1 F_2$ (by $\Phi_2$), forcing $F \equiv S$ and $X \to_S^* W$.

For (ii), forward verification $R_{k+1} W_m W_{m+1} \to_S^* S W_{m+k} W_{m+k+1}$ holds by induction on $k \in \mathbb{N}$, since $(S R_{k+1}) W_m W_{m+1} \to_S R_{k+1} W_{m+1} (W_m W_{m+1}) \equiv R_{k+1} W_{m+1} W_{m+2}$. Conversely, we prove by strong induction on step count $n$ that if $U W_m W_{m+1} \to_S^n S P Q$ with $U$ closed, then $U \to_S^* R_{k+1}$, $P \equiv W_{m+k}$, and $Q \equiv W_{m+k+1}$ for some $k \ge 0$. Because every $W_j(x, y)$ contains no $S$-leaves, it is irreducible. If no root contraction occurs at the outer application $(U W_m) W_{m+1}$, then $U W_m \to_S^n S P$ and $Q \equiv W_{m+1}$; by (i), $U \equiv S \equiv R_1$ and $W_m \to_S^* P$, so $P \equiv W_m$ ($k = 0$). Otherwise, $(U W_m) \to_S^{n_1} S A_1 A_2$ and $(A_1 W_{m+1})(A_2 W_{m+1}) \to_S^{n_2} S P Q$ with $n_1 + n_2 + 1 = n$. Recall from the proof of Proposition 2.4(iii) that the classes $\mathcal{W}_1$, $\mathcal{W}_2 = \mathcal{W}_1 \cdot \mathcal{W}_1$, and $\mathcal{W}_3 = \mathcal{W}_2 \cdot \mathcal{W}_1$ of terms ending in variables are closed forward under $\to_S$. If $U W_m \to_S^{n_1} S A_1 A_2$ used a root contraction $(S X_1 X_2) W_m \to_S (X_1 W_m)(X_2 W_m) \to_S^* S A_1 A_2$, then $(X_1 W_m)(X_2 W_m) \in \mathcal{W}_2$ would force $S A_1 \in \mathcal{W}_1$ and $A_1 \in \mathcal{W}_1$, placing $(A_1 W_{m+1})(A_2 W_{m+1}) \in \mathcal{W}_3$, which never reduces to $S P Q$ since $S \notin \mathcal{W}_1$. Thus $U W_m \to_S^{n_1} S A_1 A_2$ performs no outer root contraction, giving $U \to_S^{n_1} S A_1$, $A_2 \equiv W_m$, and $A_1 W_{m+1} W_{m+2} \to_S^{n_2} S P Q$ with $n_2 < n$; the induction hypothesis on $A_1$ yields $A_1 \to_S^* R_{k'+1}$ and $U \to_S^* S R_{k'+1} \equiv R_{k'+2}$. When $k \ge 1$, both $W_k(x, y)$ and $W_{k+1}(x, y)$ end on their right spine in $y$.

For (iii), suppose $(U x y) z \to_S^* H \in \mathrm{HNF}$. Since $z$ is irreducible, either $H \equiv F' z$ with $U x y \to_S^* F'$ (in which case $\operatorname{ls}(F') \ge 2$ by (i), so $\operatorname{ls}(F' z) \ge 3$, forcing the head of $H$ to be a variable occurring in $U x y$, namely $x$ or $y$), or else $U x y \to_S^* S P Q$ and $(P z)(Q z) \to_S^* H$. By (ii), $P \equiv W_k(x, y)$ and $Q \equiv W_{k+1}(x, y)$, so $(P z)(Q z)$ contains no $S$-leaves and is already in normal form with head leaf equal to that of $W_k(x, y)$, which belongs to $\{x, y\}$.
 $\square$

In Section 5.3 of Barendregt, Endrullis, Klop, and Waldmann [4, Figure 5.14, p. 85; Question 10 and Footnote 4, p. 86], a candidate $35$-state transition table was synthesized via local termination heuristics to recognize $\mathrm{HN}$, and its proof of correctness—together with linear-time decidability of $\mathrm{RNF}$—was posed as Question 10 and Footnote 4. Let $\mathcal{A}_{\mathrm{HN}} = (Q_{\mathrm{HN}}, q_0, \odot_{\mathrm{HN}})$ denote this $35$-state structure with carrier $Q_{\mathrm{HN}} = \{q_0, q_1, \dots, q_{33}, \infty_{\mathrm{HN}}\}$ ($\infty_{\mathrm{HN}} = q_{34}$) and accepting set $F_{\mathrm{HN}} = Q_{\mathrm{HN}} \setminus \{\infty_{\mathrm{HN}}\}$. Direct evaluation over all $35^3 = 42{,}875$ triples verifies (2.3). Unlike $\infty_{\mathrm{SN}} \in Q_{\mathrm{SN}}$, the state $\infty_{\mathrm{HN}}$ exhibits a directional asymmetry:

$$
\infty_{\mathrm{HN}} \odot_{\mathrm{HN}} y \;=\; \infty_{\mathrm{HN}} \quad\textrm{for all } y \in Q_{\mathrm{HN}},
\qquad\textrm{whereas}\qquad
q_0 \odot_{\mathrm{HN}} \infty_{\mathrm{HN}} \;=\; q_{10} \;\neq\; \infty_{\mathrm{HN}}, \tag{6.4}
$$

and $(q_0 \odot_{\mathrm{HN}} x) \odot_{\mathrm{HN}} \infty_{\mathrm{HN}} \neq \infty_{\mathrm{HN}}$ for every $x \in Q_{\mathrm{HN}}$. Algebraically, $\infty_{\mathrm{HN}}$ is a left ideal element because applying an unsolvable head $M$ to $N$ yields an unsolvable term $M N$, whereas $S M$ and $S X M$ already lie in $\mathrm{HNF}$ regardless of whether $M$ has a head normal form.

To prove completeness (that $\llbracket M \rrbracket_{\mathrm{HN}} \neq \infty_{\mathrm{HN}}$ implies $M \in \mathrm{HN}$) constructively without König's lemma, we assign unit weight $\mu_{\mathrm{HN}}(S) = 1$ to the head combinator leaf itself. Because each head contraction $S X Y Z \to_h (X Z)(Y Z)$ destroys that leading $S$-leaf, no additive offset table $B$ is needed: a single $35 \times 35$ multiplier matrix $A$ suffices, and we show below that $A$ is pointwise minimal among all valid multiplier matrices.

**Lemma 6.6 (Pure multiplier head-step potential).** 
There exists an explicit non-negative integer matrix $A \colon Q_{\mathrm{HN}}^2 \to \{0, 1, \dots, 30\}$ (with $881$ zero entries, $202$ entries equal to $1$, and $142$ entries strictly greater than $1$, attaining its maximum $A(q_{10}, q_0) = 30$ and satisfying $A(w, \infty_{\mathrm{HN}}) = 0$ for all $w \in Q_{\mathrm{HN}}$) such that across all $8{,}329$ active head-redex triples $(x, y, z) \in Q_{\mathrm{HN}}^3$ satisfying $((q_0 \odot_{\mathrm{HN}} x) \odot_{\mathrm{HN}} y) \odot_{\mathrm{HN}} z \neq \infty_{\mathrm{HN}}$, writing $s_1 = q_0 \odot_{\mathrm{HN}} x$, $s_2 = s_1 \odot_{\mathrm{HN}} y$, $u = x \odot_{\mathrm{HN}} z$, and $v = y \odot_{\mathrm{HN}} z$, the following four conditions hold simultaneously:

$$
\begin{aligned}
u &\;\neq\; \infty_{\mathrm{HN}}, \\
1 &\;\le\; A(q_0, x), \\
A(u, v) &\;\le\; A(s_1, y), \\
A(x, z) + A(u, v)\,A(y, z) &\;\le\; A(s_2, z).
\end{aligned} \tag{6.5–6.8}
$$

Define the pure multiplier potential $\mu_{\mathrm{HN}} \colon \mathcal{T}_S(\mathcal{V}) \to \mathbb{N}$ recursively by $\mu_{\mathrm{HN}}(S) = \mu_{\mathrm{HN}}(v) = 1$ ($v \in \mathcal{V}$) and

$$
\mu_{\mathrm{HN}}(L R) \;=\; \mu_{\mathrm{HN}}(L) + A(\llbracket L \rrbracket_{\mathrm{HN}}, \llbracket R \rrbracket_{\mathrm{HN}})\,\mu_{\mathrm{HN}}(R). \tag{6.9}
$$

Then for every closed $S$-term $M \in \mathcal{T}_S$ with $\llbracket M \rrbracket_{\mathrm{HN}} \neq \infty_{\mathrm{HN}}$ and every head contraction $M \to_h M'$, we have $\mu_{\mathrm{HN}}(M') + 1 \le \mu_{\mathrm{HN}}(M)$.

*Proof.* 
Verification of (6.5)–(6.8) over $\{ (x, y, z) \in Q_{\mathrm{HN}}^3 : ((q_0 \odot_{\mathrm{HN}} x) \odot_{\mathrm{HN}} y) \odot_{\mathrm{HN}} z \neq \infty_{\mathrm{HN}} \}$ ($8{,}329$ triples out of $35^3 = 42{,}875$, where (6.5) follows automatically from left-absorption of $\infty_{\mathrm{HN}}$ and (2.3)) is a finite integer arithmetic check. We prove $\mu_{\mathrm{HN}}(M') + 1 \le \mu_{\mathrm{HN}}(M)$ by induction on the derivation of $M \to_h M'$.

In the base case, $M \equiv ((S X) Y) Z$ contracts at the root to $M' \equiv (X Z)(Y Z)$, with $x = \llbracket X \rrbracket_{\mathrm{HN}}$, $y = \llbracket Y \rrbracket_{\mathrm{HN}}$, $z = \llbracket Z \rrbracket_{\mathrm{HN}}$, and $((q_0 \odot_{\mathrm{HN}} x) \odot_{\mathrm{HN}} y) \odot_{\mathrm{HN}} z = \llbracket M \rrbracket_{\mathrm{HN}} \neq \infty_{\mathrm{HN}}$. Expanding $\mu_{\mathrm{HN}}(M)$ via (6.9) and $\mu_{\mathrm{HN}}(S) = 1$ yields

$$
\mu_{\mathrm{HN}}(((S X) Y) Z)
\;=\; 1 + A(q_0, x)\,\mu_{\mathrm{HN}}(X) + A(s_1, y)\,\mu_{\mathrm{HN}}(Y) + A(s_2, z)\,\mu_{\mathrm{HN}}(Z),
$$

whereas expanding $\mu_{\mathrm{HN}}((X Z)(Y Z))$ with $\llbracket X Z \rrbracket_{\mathrm{HN}} = u$ and $\llbracket Y Z \rrbracket_{\mathrm{HN}} = v$ yields

$$
\mu_{\mathrm{HN}}((X Z)(Y Z))
\;=\; \mu_{\mathrm{HN}}(X) + A(u, v)\,\mu_{\mathrm{HN}}(Y) + \bigl(A(x, z) + A(u, v)\,A(y, z)\bigr)\mu_{\mathrm{HN}}(Z).
$$

Since $\mu_{\mathrm{HN}}(X), \mu_{\mathrm{HN}}(Y), \mu_{\mathrm{HN}}(Z) \ge 0$, comparing the coefficients of $\mu_{\mathrm{HN}}(X)$, $\mu_{\mathrm{HN}}(Y)$, and $\mu_{\mathrm{HN}}(Z)$ via (6.6)–(6.8) while retaining the leading constant $1$ from $\mu_{\mathrm{HN}}(S) = 1$ gives $\mu_{\mathrm{HN}}((X Z)(Y Z)) + 1 \le \mu_{\mathrm{HN}}(((S X) Y) Z)$.

In the inductive step, $M \equiv L R \to_h L' R$ where $L \to_h L'$. Because $\llbracket L \rrbracket_{\mathrm{HN}} \odot_{\mathrm{HN}} \llbracket R \rrbracket_{\mathrm{HN}} = \llbracket L R \rrbracket_{\mathrm{HN}} \neq \infty_{\mathrm{HN}}$ and $\infty_{\mathrm{HN}}$ is a left sink by (6.4), we have $\llbracket L \rrbracket_{\mathrm{HN}} \neq \infty_{\mathrm{HN}}$. The induction hypothesis gives $\mu_{\mathrm{HN}}(L') + 1 \le \mu_{\mathrm{HN}}(L)$, and conversion invariance gives $\llbracket L' \rrbracket_{\mathrm{HN}} = \llbracket L \rrbracket_{\mathrm{HN}}$, so $A(\llbracket L' \rrbracket_{\mathrm{HN}}, \llbracket R \rrbracket_{\mathrm{HN}}) = A(\llbracket L \rrbracket_{\mathrm{HN}}, \llbracket R \rrbracket_{\mathrm{HN}})$ is preserved, whence $\mu_{\mathrm{HN}}(L R) - \mu_{\mathrm{HN}}(L' R) = \mu_{\mathrm{HN}}(L) - \mu_{\mathrm{HN}}(L') \ge 1$.
 $\square$

**Proposition 6.7 (Pointwise minimality of $A$ and impossibility of rank-$1$ multipliers).** 
Call a matrix $A' \colon Q_{\mathrm{HN}}^2 \to \mathbb{N}$ *head-valid* if it satisfies (6.6)–(6.8) across all $8{,}329$ active triples $(x, y, z) \in Q_{\mathrm{HN}}^3$ with $((q_0 \odot_{\mathrm{HN}} x) \odot_{\mathrm{HN}} y) \odot_{\mathrm{HN}} z \neq \infty_{\mathrm{HN}}$.

- (i) *Global pointwise minimality:* The matrix $A$ of Lemma 6.6 satisfies $A(u, v) \le A'(u, v)$ for every head-valid matrix $A'$ and all $u, v \in Q_{\mathrm{HN}}$; in particular, every head-valid matrix satisfies $\max A' \ge A'(q_{10}, q_0) \ge 30$.
- (ii) *Impossibility of masked rank-$1$ and $1$D potentials:* There exist no Boolean mask $M \colon Q_{\mathrm{HN}}^2 \to \{0, 1\}$ and one-dimensional weight vectors $w_L, w_R \colon Q_{\mathrm{HN}} \to \mathbb{N}$ such that $A'(u, v) = M(u, v)\,w_L(u)\,w_R(v)$ is head-valid. In particular, no left-only weight $A'(u, v) = w_L(u)$ or right-only weight $A'(u, v) = w_R(v)$ satisfies (6.6)–(6.8).

*Proof.* 
For (i), assign each pair $(u, v) \in Q_{\mathrm{HN}}^2$ a derivation level $\ell(u, v) \in \{0, 1, \dots, 13\}$ ($\ell(u, v) = 0$ precisely where $A(u, v) = 0$). A finite certificate table associates to every pair $(u, v)$ with $\ell(u, v) \ge 1$ an active triple $(x, y, z)$ whose lower-level premises strictly precede $\ell(u, v)$ and force $A(u, v) \le A'(u, v)$ via one of (6.6) (when $u = q_0, v = x$), (6.7) (when $u = q_0 \odot_{\mathrm{HN}} x, v = y$), or (6.8) (when $u = (q_0 \odot_{\mathrm{HN}} x) \odot_{\mathrm{HN}} y, v = z$). Induction over $\ell = 0, 1, \dots, 13$ yields $A(u, v) \le A'(u, v)$ for all $u, v \in Q_{\mathrm{HN}}$, and evaluating at $(q_{10}, q_0)$ gives $30 = A(q_{10}, q_0) \le A'(q_{10}, q_0)$.

For (ii), suppose toward a contradiction that $A'(u, v) = M(u, v)\,w_L(u)\,w_R(v)$ is head-valid. Applying (i) at four entries of $A$ gives

$$
A'(q_5, q_0) \ge 15, \qquad A'(q_{10}, q_1) \ge 15, \qquad A'(q_0, q_0) \ge 1, \qquad A'(q_{10}, q_0) \ge 30.
$$

Hence $M$ equals $1$ at all four pairs, and $w_L(q_5), w_R(q_0), w_L(q_{10}), w_R(q_1), w_L(q_0) \ge 1$. Now instantiate (6.8) at the triple $(x, y, z) = (q_5, q_0, q_0)$: in $\mathcal{A}_{\mathrm{HN}}$ one has $q_0 \odot_{\mathrm{HN}} q_5 = q_5$, $q_5 \odot_{\mathrm{HN}} q_0 = q_{10}$, $q_0 \odot_{\mathrm{HN}} q_0 = q_1$, and $((q_0 \odot_{\mathrm{HN}} q_5) \odot_{\mathrm{HN}} q_0) \odot_{\mathrm{HN}} q_0 = q_{10} \odot_{\mathrm{HN}} q_0 = q_{23} \neq \infty_{\mathrm{HN}}$, so (6.8) requires

$$
w_L(q_5)\,w_R(q_0) + \bigl(w_L(q_{10})\,w_R(q_1)\bigr)\bigl(w_L(q_0)\,w_R(q_0)\bigr) \;\le\; w_L(q_{10})\,w_R(q_0).
$$

Regrouping the second summand as $\bigl(w_R(q_1)\,w_L(q_0)\bigr)\bigl(w_L(q_{10})\,w_R(q_0)\bigr) \ge 1 \cdot w_L(q_{10})\,w_R(q_0)$ and noting $w_L(q_5)\,w_R(q_0) \ge 1$ makes the left-hand side strictly exceed $w_L(q_{10})\,w_R(q_0)$, a contradiction. Setting $M \equiv 1$ and $w_R \equiv 1$ (or $w_L \equiv 1$) rules out one-dimensional weights.
 $\square$

**Theorem 6.8 (Resolution of Question 10 and Footnote 4 of Barendregt et al. [4, p. 86]).** 
For every closed $S$-term $M \in \mathcal{T}_S$, the $35$-state $S$-algebra $\mathcal{A}_{\mathrm{HN}}$ satisfies the following properties:

- (i) *Regularity and constructive bound for $\mathrm{HN}$:* One has $M \in \mathrm{HN}$ if and only if $\llbracket M \rrbracket_{\mathrm{HN}} \neq \infty_{\mathrm{HN}}$, and $\llbracket M \rrbracket_{\mathrm{HN}} = \infty_{\mathrm{HN}}$ if and only if $M$ admits an infinite head-reduction sequence $M = M_0 \to_h M_1 \to_h \cdots$. Specifically, if $\llbracket M \rrbracket_{\mathrm{HN}} \neq \infty_{\mathrm{HN}}$, deterministic head reduction from $M$ reaches $\mathrm{HNF}$ in at most $\mu_{\mathrm{HN}}(M) - 1$ steps.
- (ii) *Linear-time decidability of $\mathrm{RNF}$ (Footnote 4):* A closed $S$-term $M$ lies in $\mathrm{RNF}$ if and only if

$$
\operatorname{ls}(M) \le 2 \quad\textrm{or}\quad \bigl(M \equiv P Q \;\textrm{ and }\; \llbracket P \rrbracket_{\mathrm{HN}} = \infty_{\mathrm{HN}}\bigr), \tag{6.10}
$$

  which is decidable in $O(|M|)$ deterministic operations.
- (iii) *Five-composite-argument $\mathrm{RNF}$ ceiling:* In the spine transition graph of $\mathcal{A}_{\mathrm{HN}}$, the transition $q_{13} \xrightarrow{q_0} q_{13}$ (entered via $q_0 \xrightarrow{q_0} q_1 \xrightarrow{y} q_{13}$) is the unique accepting self-loop, and consuming composite arguments ($y \neq q_0$) contracts the reachable state sets strictly along cardinalities $35 \to 26 \to 14 \to 4 \to 2 \to 1 = \{\infty_{\mathrm{HN}}\}$. Consequently, for every closed $M \in \mathcal{T}_S$ and all closed $U_1, \dots, U_5 \in \mathcal{T}_S \setminus \{S\}$, we have $\llbracket M U_1 U_2 U_3 U_4 U_5 \rrbracket_{\mathrm{HN}} = \infty_{\mathrm{HN}}$, and $M U_1 U_2 U_3 U_4 U_5 U_6 \in \mathrm{RNF}$ for every $U_6 \in \mathcal{T}_S$.
- (iv) *Joint $(\mathrm{SN}, \mathrm{HN})$ subalgebra:* The reachable subalgebra of $\mathcal{A}_{\mathrm{SN}} \times \mathcal{A}_{\mathrm{HN}}$ generated by $(q_0, q_0)$ has exact cardinality $112$, partitioning into $94$ states in $F_{\mathrm{SN}} \times F_{\mathrm{HN}}$ ($\mathrm{SN}$), $17$ states in $\{\infty_{\mathrm{SN}}\} \times F_{\mathrm{HN}}$ ($\mathrm{HN} \setminus \mathrm{SN}$), and the single state $(\infty_{\mathrm{SN}}, \infty_{\mathrm{HN}})$ ($\overline{\mathrm{HN}}$).

*Proof.* 
For (i), every closed $H \in \mathrm{HNF}$ has the form $S$, $S A_1$, or $S A_1 A_2$, and inspection of $\mathcal{A}_{\mathrm{HN}}$ confirms $q_0 \neq \infty_{\mathrm{HN}}$, $q_0 \odot_{\mathrm{HN}} x \neq \infty_{\mathrm{HN}$, and $(q_0 \odot_{\mathrm{HN}} x) \odot_{\mathrm{HN}} y \neq \infty_{\mathrm{HN}}$ for all $x, y \in Q_{\mathrm{HN}}$; conversion invariance therefore shows that $M \in \mathrm{HN}$ implies $\llbracket M \rrbracket_{\mathrm{HN}} \neq \infty_{\mathrm{HN}}$. Conversely, every closed $M \notin \mathrm{HNF}$ satisfies $\operatorname{ls}(M) \ge 3$ and admits a unique head step $M \to_h M'$. If $\llbracket M \rrbracket_{\mathrm{HN}} \neq \infty_{\mathrm{HN}}$, conversion invariance preserves $\llbracket M' \rrbracket_{\mathrm{HN}} \neq \infty_{\mathrm{HN}}$ and Lemma 6.6 decreases $\mu_{\mathrm{HN}} \ge 1$ by at least $1$ at each step, terminating in $\mathrm{HNF}$ within $\mu_{\mathrm{HN}}(M) - 1$ steps; if instead $\llbracket M \rrbracket_{\mathrm{HN}} = \infty_{\mathrm{HN}}$, then every head reduct $M_k$ preserves $\llbracket M_k \rrbracket_{\mathrm{HN}} = \infty_{\mathrm{HN}}$ and therefore satisfies $\operatorname{ls}(M_k) \ge 3$, generating an infinite deterministic head-reduction chain.

For (ii), if $\operatorname{ls}(M) \le 2$, then $M \in \mathrm{HNF} \subseteq \mathrm{RNF}$. Suppose now $\operatorname{ls}(M) \ge 3$, so $M \equiv P Q$ with $\operatorname{ls}(P) \ge 2$. A reduction $P Q \to_S^* N$ contracts at the root if and only if $P \to_S^* S X Y$ for some $X, Y \in \mathcal{T}_S$. By Lemma 6.5(i), since $\operatorname{ls}(P) \ge 2$, no reduct of $P$ can be $S$ or $S W$; hence $P$ reduces to some $S X Y$ if and only if $P \in \mathrm{HN}$, which by (i) holds if and only if $\llbracket P \rrbracket_{\mathrm{HN}} \neq \infty_{\mathrm{HN}}$. Negating this equivalence yields $P Q \in \mathrm{RNF}$ if and only if $\llbracket P \rrbracket_{\mathrm{HN}} = \infty_{\mathrm{HN}}$, establishing (6.10).

For (iii), inspection of $\mathcal{A}_{\mathrm{HN}}$ shows that $q_0$ never occurs in the image of $\odot_{\mathrm{HN}}$; hence a closed $S$-term $U$ evaluates to $q_0$ in $\mathcal{A}_{\mathrm{HN}}$ if and only if $U \equiv S$. Computing $S_{k+1} = \{ u \odot_{\mathrm{HN}} y : u \in S_k,\, y \in Q_{\mathrm{HN}} \setminus \{q_0\} \}$ starting from $S_0 = Q_{\mathrm{HN}}$ yields $|S_0| = 35$, $|S_1| = 26$, $|S_2| = 14$, $|S_3| = 4$ ($\{q_{23}, q_{24}, q_{25}, \infty_{\mathrm{HN}}\}$), $|S_4| = 2$ ($\{q_{23}, \infty_{\mathrm{HN}}\}$), and $S_5 = \{\infty_{\mathrm{HN}}\}$. Thus $\llbracket M U_1 \dots U_5 \rrbracket_{\mathrm{HN}} = \infty_{\mathrm{HN}}$, and (6.10) implies $M U_1 \dots U_5 U_6 \in \mathrm{RNF}$; five composite arguments is sharp, since $S S U_1 U_2 U_3 U_4$ has $\mathrm{HN}$ state $q_{23} \neq \infty_{\mathrm{HN}}$ for $U_i \equiv S S$.

For (iv), breadth-first closure of $\{(q_0, q_0)\} \subseteq Q_{\mathrm{SN}} \times Q_{\mathrm{HN}}$ under componentwise $\odot$ stabilizes at $112$ pairs, none of which lies in $F_{\mathrm{SN}} \times \{\infty_{\mathrm{HN}}\}$, reflecting $\mathrm{SN} \subsetneq \mathrm{HN}$ algebraically.
 $\square$

### 6.3. Global Top-Termination, Root Normal Forms, and Absence of Mute Terms

In untyped $\lambda$-calculus and full $\mathrm{CL}(S, K)$, unsolvable terms divide into those reducing to an application of unsolvable terms and *mute* (or root-active) terms in the sense of Berarducci [9, 8], such as $\Omega \equiv (\lambda x.\,x x)(\lambda x.\,x x) \to_r \Omega$. Waldmann [66] (see also [4, Theorem 29]) established via semantic labelling [77] that $\mathrm{CL}(S)$ is globally *top-terminating*: no infinite reduction sequence contracts at the root infinitely often. Using $\mathcal{A}_{\mathrm{HN}}$ and Lemma 6.6, we give a direct constructive proof yielding a total root-normalizing function $\mathrm{rnf}$.

**Theorem 6.9 (Constructive global top-termination and root normal forms [66]; [4, Theorem 29]).** 

- (i) *Global top-termination:* Every open or closed $S$-term $M \in \mathcal{T}_S(\mathcal{V})$ is top-terminating: there exists no infinite sequence $M = M_0 \to_{\mathrm{nr}}^* M'_0 \to_r M_1 \to_{\mathrm{nr}}^* M'_1 \to_r \cdots$ containing infinitely many root contractions $\to_r$ interspersed with non-root steps $\to_{\mathrm{nr}}$.
- (ii) *Total root normalizer $\mathrm{rnf}$ and absence of Berarducci mute terms:* There is a total constructive procedure $\mathrm{rnf} \colon \mathcal{T}_S \to \mathrm{RNF}$ satisfying $M \to_S^* \mathrm{rnf}(M)$ for every $M \in \mathcal{T}_S$. Consequently, $\mathrm{CL}(S)$ contains no Berarducci mute terms [8]: every unsolvable closed $M \in \mathcal{T}_S \setminus \mathrm{HN}$ reduces to an applicative root normal form $P Q \in \mathrm{RNF}$ with $P \in \mathcal{T}_S \setminus \mathrm{HN}$, and every closed $S$-term possesses a $\bot$-free Berarducci tree $\operatorname{BeT}(M)$.
- (iii) *Root-step bound on $A A A$:* By Proposition 2.4(i), $\to_S^+$ is irreflexive on $\mathcal{T}_S(\mathcal{V})$; moreover, every multiway reduction starting from $A A A \equiv (S S S)(S S S)(S S S)$ executes at most $3$ root contractions, reaching its root normal form in $6$ deterministic head steps.

*Proof.* 
For (i), consider first closed $M \in \mathcal{T}_S$ with $\llbracket M \rrbracket_{\mathrm{HN}} \neq \infty_{\mathrm{HN}}$. Define the truncated pure-multiplier potential $\nu_{\mathrm{HN}} \colon \mathcal{T}_S \to \mathbb{N}$ by $\nu_{\mathrm{HN}}(U) = 0$ if $\llbracket U \rrbracket_{\mathrm{HN}} = \infty_{\mathrm{HN}}$, $\nu_{\mathrm{HN}}(S) = 1$, and $\nu_{\mathrm{HN}}(L R) = \nu_{\mathrm{HN}}(L) + A(\llbracket L \rrbracket_{\mathrm{HN}}, \llbracket R \rrbracket_{\mathrm{HN}})\,\nu_{\mathrm{HN}}(R)$ whenever $\llbracket L R \rrbracket_{\mathrm{HN}} \neq \infty_{\mathrm{HN}}$. Because $A(u, \infty_{\mathrm{HN}}) = 0$ for all $u \in Q_{\mathrm{HN}}$ and $\infty_{\mathrm{HN}}$ is a left sink, $\nu_{\mathrm{HN}}$ agrees with $\mu_{\mathrm{HN}}$ modulo zeroing out $\infty_{\mathrm{HN}}$-subterms, which carry multiplier $0$ whenever they appear on the right of an accepted parent. By Lemma 6.6 and conversion invariance of $\llbracket \cdot \rrbracket_{\mathrm{HN}}$, every non-root step $N \to_{\mathrm{nr}} N'$ anywhere inside $N$ satisfies $\nu_{\mathrm{HN}}(N') \le \nu_{\mathrm{HN}}(N)$, while every root contraction $N \to_r N'$ on $\llbracket N \rrbracket_{\mathrm{HN}} \neq \infty_{\mathrm{HN}}$ satisfies $\nu_{\mathrm{HN}}(N') + 1 \le \nu_{\mathrm{HN}}(N)$. Thus $M$ executes at most $\nu_{\mathrm{HN}}(M) - 1$ root contractions.

Next consider closed $M \in \mathcal{T}_S$ with $\llbracket M \rrbracket_{\mathrm{HN}} = \infty_{\mathrm{HN}}$. By Proposition 2.2(ii), right-spine depth $\operatorname{rs}$ satisfies $\operatorname{rs}(N) \le \operatorname{rs}(N')$ for every non-root step $N \to_{\mathrm{nr}} N'$, whereas every root contraction $S X Y Z \to_r (X Z)(Y Z)$ yields $\operatorname{rs}((X Z)(Y Z)) = \operatorname{rs}(S X Y Z) + 1$. Stratifying $Q_{\mathrm{HN}}$ into nested root-contraction capacity classes $G_{\ge 0} \supset G_{\ge 1} \supset \dots \supset G_{\ge 5}$ of cardinalities $(35, 34, 26, 18, 17, 16)$ and tracking the maximal strongly connected spine prefixes on $\infty_{\mathrm{HN}}$ once $\operatorname{rs}(N) \ge 6$ shows that at most finitely many root steps can occur before the left child of $N \equiv P Q$ locks permanently into $\infty_{\mathrm{HN}}$, where Theorem 6.8(ii) forces $N \in \mathrm{RNF}$. For an arbitrary open term $M \in \mathcal{T}_S(\mathcal{V})$, the variable-erasing homomorphism $\sigma_S \colon \mathcal{T}_S(\mathcal{V}) \to \mathcal{T}_S$ sending every $v \in \mathcal{V}$ to $S$ maps root steps to root steps and non-root steps to non-root steps, lifting well-foundedness of $\to_{\mathrm{nr}}^* \cdot \to_r$ from $\mathcal{T}_S$ to $\mathcal{T}_S(\mathcal{V})$.

For (ii), well-founded recursion on the relative root relation $\to_{\mathrm{nr}}^* \cdot \to_r$ defines $\mathrm{rnf}(M)$: check whether $M \in \mathrm{RNF}$ in $O(|M|)$ time via Theorem 6.8(ii); if so, return $M$; otherwise $M \equiv P Q$ has $\operatorname{ls}(P) \ge 2$ and $\llbracket P \rrbracket_{\mathrm{HN}} \neq \infty_{\mathrm{HN}}$, so head-normalizing $P \to_h^* S X Y$ within $\mu_{\mathrm{HN}}(P) - 1$ steps and contracting $(S X Y) Q \to_r (X Q)(Y Q)$ performs one relative root step, allowing recursive invocation $\mathrm{rnf}((X Q)(Y Q))$. If $M \in \mathcal{T}_S \setminus \mathrm{HN}$, then $\mathrm{rnf}(M) \in \mathrm{RNF} \setminus \mathrm{HN}$ cannot satisfy $\operatorname{ls}(\mathrm{rnf}(M)) \le 2$, so by (6.10) it has the form $P Q$ with $\llbracket P \rrbracket_{\mathrm{HN}} = \infty_{\mathrm{HN}}$. Coinductively unfolding $\mathrm{rnf}$ on $P$ and $Q$ generates a total $\bot$-free Berarducci tree $\operatorname{BeT}(M)$, proving the absence of mute terms.

For (iii), for $A A A \equiv (S S S)(S S S)(S S S)$ we have $\operatorname{rs}(A A A) = 2$, and finite enumeration of the root-contracting reachable cone confirms that $A A A$ admits at most $3$ root contractions along any multiway path, reaching the root normal form $\bigl((S A A)\,(S A (S A A))\bigr)\bigl(S(S A A)\,(S A (S A A))\bigr)$ in $6$ deterministic head steps.
 $\square$

### 6.4. Regularity of Böhm-Tree Productivity, Rank-10 Completeness, and 113-State Minimality

Recall from Definition 2.6(iii)–(iv) and Lemma 2.7 that a closed $S$-term $M \in \mathcal{T}_S$ is *productive* ($M \in \mathrm{Prod}$) when $\operatorname{BT}(M)$ contains no occurrence of $\bot$ at any finite depth—formally, when $\neg\bot_d(M)$ holds for all $d \in \mathbb{N}$—and that $\bot_d$ is conversion-invariant and monotone in $d$ ($\bot_d(M)$ implies $\bot_{d+1}(M)$). Every strongly normalizing term is productive because its normal form is a finite $\bot$-free Böhm tree. As discovered by Zachos [76] (see [4, p. 80]), $\mathrm{Prod}$ strictly contains $\mathrm{SN}$: defining the normal-form tower

$$
G_0 \;\equiv\; S T T \;\equiv\; S(S S)(S S),
\qquad
G_{k+1} \;\equiv\; T G_k \;\equiv\; (S S)\,G_k
\qquad (k \in \mathbb{N}), \tag{6.11}
$$

we have $G_0 G_n \equiv S T T G_n \to_h (T G_n)(T G_n) \equiv G_{n+1} G_{n+1}$ and $G_{k+1} G_m \equiv S S G_k G_m \to_h S G_m (G_k G_m) \in \mathrm{HNF}$ (whose left child $G_m$ lies in $\mathcal{N}$), so $Z_{\mathrm{Zac}} \equiv G_0 G_0$ ($10$ leaves) is non-normalizing yet generates an infinite $\bot$-free Böhm tree. Question 5 of Barendregt et al. [4, p. 80] asks how to characterize $\mathrm{Prod}$, whether $\mathrm{Prod}$ is regular, and whether productivity is decidable.

Our resolution of Question 5 begins with two structural lemmas showing via potential-free head conservation how non-erasure in $\mathrm{CL}(S)$ forces $\bot$ to propagate across both sides of binary application, and why Zachos pairs $G_m G_n$ lose productivity upon receiving any further right argument.

**Lemma 6.10 (Left and right $\bot$-propagation on closed $S$-terms).** 
For every depth $d \in \mathbb{N}$ and all closed $S$-terms $Y, Z, F, W \in \mathcal{T}_S$:

$$
\bot_d(Y) \;\Longrightarrow\; \bot_d(Y Z)
\qquad\textrm{and}\qquad
\bot_d(W) \;\Longrightarrow\; \bot_{d+1}(F W). \tag{6.12}
$$

Consequently, $M N \in \mathrm{Prod}$ implies both $M \in \mathrm{Prod}$ and $N \in \mathrm{Prod}$.

*Proof.* 
Consider first an invariant of head reduction on open $\{S, x_0\}$-terms: writing the left spine of $U$ as $U \equiv h\,U_1 \dots U_r$ ($h \in \{S, x_0\}$, $r \ge 0$), define $\Phi_{x_0}(U)$ to hold if either $h = x_0$ or there exists $i \in \{1, \dots, r\}$ whose leftmost leaf is $x_0$. Under a root head step $S A_1 A_2 A_3 \to_h (A_1 A_3)(A_2 A_3)$, if the leftmost leaf of $A_1$ is $x_0$, then $(A_1 A_3)(A_2 A_3)$ has head leaf $x_0$; if the leftmost leaf of $A_2$ is $x_0$, then the final spine argument $A_2 A_3$ has leftmost leaf $x_0$; and if the leftmost leaf of $A_3$ is $x_0$, then $A_3$ itself appears on the left spine of $(A_1 A_3)(A_2 A_3)$ with leftmost leaf $x_0$. Inductive left steps $L R \to_h L' R$ likewise preserve $\Phi_{x_0}$.

Now let $F, W \in \mathcal{T}_S$ be closed with $\llbracket F W \rrbracket_{\mathrm{HN}} \neq \infty_{\mathrm{HN}}$. By Theorem 6.8(i) and Lemma 6.4, $F W \in \mathrm{SHN}$. Because substituting $\sigma_W(x_0) = W$ maps every open head step $U \to_h U'$ to a closed head step $\sigma_W(U) \to_h \sigma_W(U')$, accessibility pulls back from $\sigma_W(F x_0) \equiv F W \in \mathrm{SHN}$ to $F x_0 \in \mathrm{SHN}$ without referencing $\mu_{\mathrm{HN}}$. Thus open head reduction from $F x_0$ terminates at a head-irreducible $\{S, x_0\}$-term $U^*$ satisfying $\Phi_{x_0}(U^*)$, which must have: (a) head leaf $x_0$; (b) $U^* \equiv S A_1$ where $A_1$ has head leaf $x_0$; or (c) $U^* \equiv S A_1 A_2$ where $A_1$ or $A_2$ has head leaf $x_0$. Hence left propagation at depth $d$ implies right propagation at depth $d$: if $\llbracket F W \rrbracket_{\mathrm{HN}} = \infty_{\mathrm{HN}}$, then $\bot_0(F W)$ gives $\bot_{d+1}(F W)$; otherwise $F W \to_S^* \sigma_W(U^*)$, and any subterm $K$ with head leaf $x_0$ substitutes to $W\,\sigma_W(K_1)\cdots\sigma_W(K_m)$, satisfying $\bot_d$ by $m$-fold left propagation at depth $d$ and yielding $\bot_{d+1}(F W)$ by Lemma 2.7.

We now prove both laws in (6.12) simultaneously by induction on $d \in \mathbb{N}$. For $d = 0$, if $\bot_0(Y)$, Theorem 6.8(i) gives $\llbracket Y \rrbracket_{\mathrm{HN}} = \infty_{\mathrm{HN}}$, so $\llbracket Y Z \rrbracket_{\mathrm{HN}} = \infty_{\mathrm{HN}} \odot_{\mathrm{HN}} \llbracket Z \rrbracket_{\mathrm{HN}} = \infty_{\mathrm{HN}}$ by (6.4), giving $\bot_0(Y Z)$ and hence right propagation at $d = 0$. For $d + 1$, assume (6.12) at depth $d$ and suppose $\bot_{d+1}(Y)$. If $Y \notin \mathrm{HN}$, then $Y Z \notin \mathrm{HN}$ gives $\bot_{d+1}(Y Z)$. If $Y \to_S^* S A_1$ with $\bot_d(A_1)$, then $Y Z \to_S^* S A_1 Z \in \mathrm{HNF}$ gives $\bot_{d+1}(Y Z)$. If $Y \to_S^* S A_1 A_2$, then $Y Z \to_S^* (A_1 Z)(A_2 Z)$: when $\bot_d(A_1)$, two applications of depth-$d$ left propagation give $\bot_d((A_1 Z)(A_2 Z))$ and $\bot_{d+1}(Y Z)$; when $\bot_d(A_2)$, depth-$d$ left propagation gives $\bot_d(A_2 Z)$ and depth-$d$ right propagation gives $\bot_{d+1}((A_1 Z)(A_2 Z))$, whence $\bot_{d+1}(Y Z)$ by Lemma 2.7. Right propagation at $d + 1$ then follows from left propagation at $d + 1$.
 $\square$

**Lemma 6.11 (Zachos right-application $\bot$-absorption).** 
Let $G_k$ ($k \in \mathbb{N}$) be Zachos's normal-form tower (6.11). For all $m, n \in \mathbb{N}$ and every closed $S$-term $U \in \mathcal{T}_S$, there exists $d \in \mathbb{N}$ such that $\bot_d\bigl((G_m G_n) U\bigr)$; in particular, $(G_m G_n) U \notin \mathrm{Prod}$.

*Proof.* 
We first establish an auxiliary claim by induction on $n \in \mathbb{N}$: for any closed $Z, W \in \mathcal{T}_S$, if $\llbracket (G_0 Z) W \rrbracket_{\mathrm{HN}} = \infty_{\mathrm{HN}}$, then there exists $d \in \mathbb{N}$ with $\bot_d((G_n Z) W)$. For $n = 0$, Theorem 6.8(i) directly gives $\bot_0((G_0 Z) W)$. For $n + 1$, expanding $G_{n+1} \equiv S S G_n$ gives the two-step reduction

$$
(G_{n+1} Z) W \;\equiv\; (S S G_n Z) W \;\to_S\; \bigl(S Z (G_n Z)\bigr) W \;\to_S\; (Z W)\bigl((G_n Z) W\bigr).
$$

By the induction hypothesis, $\bot_d((G_n Z) W)$ holds for some $d$; applying Lemma 6.10 to $(Z W)((G_n Z) W)$ yields $\bot_{d+1}\bigl((Z W)((G_n Z) W)\bigr)$, and Lemma 2.7 gives $\bot_{d+1}((G_{n+1} Z) W)$.

Now consider $(G_m G_n) U$ for $m = k + 1 \ge 1$. Two contractions yield $(G_{k+1} G_n) U \to_S^2 (G_n U)\bigl((G_k G_n) U\bigr)$. Set $W \equiv (G_k G_n) U$. In $\mathcal{A}_{\mathrm{HN}}$, one computes $\llbracket G_0 \rrbracket_{\mathrm{HN}} = q_{16}$ and $\llbracket G_{r+1} \rrbracket_{\mathrm{HN}} = q_{13}$ for all $r \ge 0$, whence $\llbracket G_k G_n \rrbracket_{\mathrm{HN}} \in \{q_{23}, q_{24}\}$. Inspection of rows $q_{23}$ and $q_{24}$ of $\mathcal{A}_{\mathrm{HN}}$ shows that for every $h = \llbracket U \rrbracket_{\mathrm{HN}} \in Q_{\mathrm{HN}}$, both $q_{23} \odot_{\mathrm{HN}} h$ and $q_{24} \odot_{\mathrm{HN}} h$ belong to $\{q_{23}, \infty_{\mathrm{HN}}\}$, so $\llbracket W \rrbracket_{\mathrm{HN}} \in \{q_{23}, \infty_{\mathrm{HN}}\}$. Moreover, for every $h \in Q_{\mathrm{HN}}$, the state $s = q_{16} \odot_{\mathrm{HN}} h = \llbracket G_0 U \rrbracket_{\mathrm{HN}}$ satisfies $s \odot_{\mathrm{HN}} q_{23} = \infty_{\mathrm{HN}}$ and $s \odot_{\mathrm{HN}} \infty_{\mathrm{HN}} = \infty_{\mathrm{HN}}$, giving $\llbracket (G_0 U) W \rrbracket_{\mathrm{HN}} = \infty_{\mathrm{HN}}$. By the auxiliary claim above, $(G_n U) W$ satisfies $\bot_d$ for some $d$, so $(G_{k+1} G_n) U$ satisfies $\bot_d$. Finally, for $m = 0$, we have $(G_0 G_n) U \equiv (S T T G_n) U \to_S (G_{n+1} G_{n+1}) U$, reducing immediately to $m = n + 1 \ge 1$.
 $\square$

We now define the $39$-state productivity $S$-algebra $\mathcal{A}_P = (Q_P, q_0, \odot_P)$ with carrier $Q_P = \{q_0, q_1, \dots, q_{36}, \infty_P, q_{38}\}$ (identifying the unique rejecting sink as $\infty_P = q_{37}$ and the accepting set as $F_P = Q_P \setminus \{\infty_P\}$, $|F_P| = 38$). Direct verification over all $39^3 = 59{,}319$ triples confirms (2.3), and $\infty_P$ is a two-sided sink ($\infty_P \odot_P y = x \odot_P \infty_P = \infty_P$), matching Lemma 6.10 algebraically, while row $q_{29}$ satisfies $q_{29} \odot_P y = \infty_P$ for every $y \in Q_P$, matching Lemma 6.11 since $\llbracket G_m G_n \rrbracket_P = q_{29}$.

**Proposition 6.12 (Coinductive soundness of $\mathcal{A}_P$ and $34$-of-$38$ strong-normalization stratification).** 

- (i) *HNF closure and soundness:* For all $x, y \in Q_P$, one has $q_0 \odot_P x \in F_P$ if and only if $x \in F_P$, and $(q_0 \odot_P x) \odot_P y \in F_P$ if and only if both $x \in F_P$ and $y \in F_P$. Every closed $S$-term $M$ with $\llbracket M \rrbracket_P \neq \infty_P$ satisfies $\llbracket M \rrbracket_{\mathrm{HN}} \neq \infty_{\mathrm{HN}}$ and $M \in \mathrm{Prod}$.
- (ii) *Non-isomorphism with $\mathcal{A}_{\mathrm{SN}}$ and unique non-$\mathrm{SN}$ root-redex fiber:* Although $|Q_P| = |Q_{\mathrm{SN}}| = 39$, the reachable subalgebra of $\mathcal{A}_P \times \mathcal{A}_{\mathrm{SN}}$ has $44$ states. Thirty-four of the $38$ accepting states of $\mathcal{A}_P$—every $q \in F_P \setminus \{q_{18}, q_{24}, q_{29}, q_{33}\}$—pair exclusively with $F_{\mathrm{SN}}$ and therefore contain only strongly normalizing terms. Furthermore, every term in $(q_{18}, \infty_{\mathrm{SN}})$, $(q_{24}, \infty_{\mathrm{SN}})$, or $(q_{33}, \infty_{\mathrm{SN}})$ reduces to a spine-$1$ or spine-$2$ $\mathrm{HNF}$ without executing any root contraction, leaving $(q_{29}, \infty_{\mathrm{SN}})$ as the unique non-$\mathrm{SN}$ productive root-redex state pair in $\mathrm{CL}(S)$.

*Proof.* 
For (i), the $\mathrm{HNF}$ biconditionals hold by direct inspection of $\odot_P$. Reachable closure of $(q_0, q_0) \in Q_P \times Q_{\mathrm{HN}}$ yields $113$ pairs ($95$ with $\llbracket M \rrbracket_P \in F_P$ and $18$ with $\llbracket M \rrbracket_P = \infty_P$), and $(\infty_P, \infty_{\mathrm{HN}})$ is the sole pair whose second coordinate is $\infty_{\mathrm{HN}}$; hence $\llbracket M \rrbracket_P \neq \infty_P$ implies $\llbracket M \rrbracket_{\mathrm{HN}} \neq \infty_{\mathrm{HN}}$. Induction on $d \in \mathbb{N}$ shows that $\llbracket M \rrbracket_P \neq \infty_P$ implies $\neg\bot_d(M)$: at $d = 0$, $\llbracket M \rrbracket_{\mathrm{HN}} \neq \infty_{\mathrm{HN}}$ refutes $M \notin \mathrm{HN}$ by Theorem 6.8(i); at $d + 1$, if $M \to_S^* S A_1 \dots A_k$ ($1 \le k \le 2$), conversion invariance gives $\llbracket S A_1 \dots A_k \rrbracket_P = \llbracket M \rrbracket_P \in F_P$, so the $\mathrm{HNF}$ biconditionals give $\llbracket A_i \rrbracket_P \in F_P$ and $\neg\bot_d(A_i)$ by the depth-$d$ hypothesis.

For (ii), reachable closure of $(q_0, q_0) \in Q_P \times Q_{\mathrm{SN}}$ produces $44$ pairs, of which only $(q_{18}, \infty_{\mathrm{SN}})$, $(q_{24}, \infty_{\mathrm{SN}})$, $(q_{29}, \infty_{\mathrm{SN}})$, $(q_{33}, \infty_{\mathrm{SN}})$, and $(\infty_P, \infty_{\mathrm{SN}})$ have second coordinate $\infty_{\mathrm{SN}}$; Theorem 6.2 implies all other $34$ states of $F_P$ inhabit $\mathrm{SN}$. Inspecting all joint transitions landing in $(q_{18}, \infty_{\mathrm{SN}})$, $(q_{24}, \infty_{\mathrm{SN}})$, or $(q_{33}, \infty_{\mathrm{SN}})$ shows that in every such application $L R$, the left child $L$ satisfies $\llbracket L \rrbracket_{\mathrm{SN}} \neq \infty_{\mathrm{SN}}$ and normalizes to $S$ or $S U$, so $L R \to_S^* S R$ or $S U R \in \mathrm{HNF}$ without root contractions. Only $(q_{29}, \infty_{\mathrm{SN}})$ admits non-$\mathrm{SN}$ root-contracting terms, such as $Z_{\mathrm{Zac}} \equiv G_0 G_0$ and $Z_0 \equiv S(S T)(S T)T$.
 $\square$

To prove completeness (that $\llbracket M \rrbracket_P = \infty_P$ implies $\bot_d(M)$ for some $d \in \mathbb{N}$), we replace normal forms $\mathcal{N}$ by a grammar of *canonical productive values* $\mathcal{V}_P \subset \mathcal{T}_S$ that internalizes the unique non-$\mathrm{SN}$ productive root-redex family $G_m G_n$ directly as a value constructor:

$$
\mathcal{V}_P \;::=\; S \;\mid\; S V \;\mid\; S V_1 V_2 \;\mid\; G_m G_n
\qquad (V, V_1, V_2 \in \mathcal{V}_P,\; m, n \in \mathbb{N}), \tag{6.13}
$$

with structural size $\mathrm{sz}(S) = \mathrm{sz}(G_m G_n) = 1$, $\mathrm{sz}(S V) = \mathrm{sz}(V) + 1$, and $\mathrm{sz}(S V_1 V_2) = \mathrm{sz}(V_1) + \mathrm{sz}(V_2) + 1$.

**Lemma 6.13 (Syntactic rigidity of $\mathcal{V}_P$, $35$-override $2$D collapse, and rank-$6$ normalization).** 
Every $V \in \mathcal{V}_P$ satisfies $\llbracket V \rrbracket_P \in F_P$, and $\mathcal{V}_P$ obeys three syntactic rigidity laws:

$$
\llbracket V \rrbracket_P = q_0 \Longrightarrow V \equiv S,
\qquad
\llbracket V \rrbracket_P = q_1 \Longrightarrow V \equiv T \equiv S S,
\qquad
\llbracket V \rrbracket_P \in \{q_{14}, q_{32}\} \Longrightarrow \exists k \in \mathbb{N},\; V \equiv G_k. \tag{6.14}
$$

Moreover, collapsing the $39^3 = 59{,}319$ triple-rank cube to a $39 \times 39$ matrix $\hat{\tau}_P((q_0 \odot_P x) \odot_P y,\, z) \in \{0, \dots, 6\}$ modified on $35$ explicit overrides ($34$ entries at $x = q_1$ assigned rank $2$, plus the single triple $(q_6, q_0, q_1)$ assigned rank $3$) yields a total rank-$6$ application operator $\mathrm{app}_{\mathcal{V}_P}(V_1, V_2) \in \mathcal{V}_P$ for all $V_1, V_2 \in \mathcal{V}_P$ with $\llbracket V_1 \rrbracket_P \odot_P \llbracket V_2 \rrbracket_P \neq \infty_P$ satisfying $V_1 V_2 \to_S^* \mathrm{app}_{\mathcal{V}_P}(V_1, V_2)$. Consequently, every closed $M \in \mathcal{T}_S$ with $\llbracket M \rrbracket_P \neq \infty_P$ reduces constructively to some $V \in \mathcal{V}_P$.

*Proof.* 
Because $\llbracket G_0 \rrbracket_P = q_{14}$, $\llbracket G_{k+1} \rrbracket_P = q_{32}$, and $\llbracket G_m G_n \rrbracket_P = q_{29} \in F_P$, structural induction on (6.13) via Proposition 6.12(i) confirms $\llbracket V \rrbracket_P \in F_P$ for all $V \in \mathcal{V}_P$. For (6.14), induct on $V \in \mathcal{V}_P$: $q_0$ never lies in the image of $\odot_P$, forcing $V \equiv S$; the sole spine-$1$ or spine-$2$ transition into $q_1$ is $q_0 \odot_P q_0 = q_1$, forcing $V \equiv S S \equiv T$; no spine-$1$ state lies in $\{q_{14}, q_{32}\}$, while $(q_0 \odot_P x) \odot_P y = q_{14}$ forces $x = y = q_1$ ($V \equiv S T T \equiv G_0$), and $(q_0 \odot_P x) \odot_P y = q_{32}$ forces $x = q_0$ and $y \in \{q_{14}, q_{32}\}$ ($V \equiv S S G_k \equiv G_{k+1}$).

To define $\mathrm{app}_{\mathcal{V}_P}(V_1, V_2)$ when $\llbracket V_1 \rrbracket_P \odot_P \llbracket V_2 \rrbracket_P \neq \infty_P$, note that $V_1$ cannot be $G_m G_n$ since $q_{29} \odot_P z = \infty_P$. If $V_1 \equiv S$ or $V_1 \equiv S U$, then $V_1 V_2 \in \mathcal{V}_P$ directly. If $V_1 \equiv S X Y$ with $X, Y \in \mathcal{V}_P$, first test whether both $\llbracket V_1 \rrbracket_P \in \{q_{14}, q_{32}\}$ and $\llbracket V_2 \rrbracket_P \in \{q_{14}, q_{32}\}$: if so, (6.14) identifies unique $m, n \in \mathbb{N}$ with $V_1 \equiv G_m$ and $V_2 \equiv G_n$, so $V_1 V_2 \equiv G_m G_n \in \mathcal{V}_P$ in zero steps. Otherwise, contract $(S X Y) V_2 \to_S (X V_2)(Y V_2)$; across all non-Zachos accepted triples, the $35$-override collapsed rank $\tau_P(x, y, z) \in \{1, \dots, 6\}$ satisfies $\hat{\tau}_P(x, z) \le \tau_P(x, y, z)$ and $\hat{\tau}_P(y, z) \le \tau_P(x, y, z)$ (normalizing $X V_2 \to_S^* W_1$ and $Y V_2 \to_S^* W_2$ by inner induction on $\mathrm{sz}(V_1)$), and whenever $(W_1, W_2)$ is not itself a Zachos pair $(G_{m'}, G_{n'})$, satisfies strict outer rank decrease as in (6.2)–(6.3). Structural induction on $M \in \mathcal{T}_S$ via the two-sided sink $\infty_P$ then normalizes every accepted $M$ into $\mathcal{V}_P$.
 $\square$

**Theorem 6.14 (Regularity of Böhm-tree productivity and rank-$10$ resolution of Question 5 [4, p. 80]).** 
For every closed $S$-term $M \in \mathcal{T}_S$,

$$
M \in \mathrm{Prod} \;\Longleftrightarrow\; \llbracket M \rrbracket_P \neq \infty_P, \tag{6.15}
$$

so the set $\mathrm{Prod}$ of productive closed $S$-terms is a regular tree language decidable in $2|M| - 1$ deterministic table lookups. Constructively, for every closed $M \in \mathcal{T}_S$, either $M \in \mathrm{Prod}$ or a unified $10$-rank induction over the $113$-state reachable subalgebra $\mathrm{PH} \subseteq Q_P \times Q_{\mathrm{HN}}$ extracts an explicit depth $d \in \mathbb{N}$ satisfying $\bot_d(M)$.

*Proof.* 
Soundness (that $\llbracket M \rrbracket_P \neq \infty_P$ implies $M \in \mathrm{Prod}$) was proved in Proposition 6.12(i). For constructive completeness, structural induction on $M$ with $\llbracket M \rrbracket_P = \infty_P$ reduces via Lemma 6.10 to minimal critical applications $L R$ with $\llbracket L \rrbracket_P, \llbracket R \rrbracket_P \in F_P$ and $\llbracket L \rrbracket_P \odot_P \llbracket R \rrbracket_P = \infty_P$, which Lemma 6.13 normalizes to critical pairs $(F, Z) \in \mathcal{V}_P \times \mathcal{V}_P$ satisfying $\llbracket F Z \rrbracket_P = \infty_P$. If $F \equiv G_m G_n$, Lemma 6.11 yields $\bot_d((G_m G_n) Z)$ directly; since $F \equiv S$ and $F \equiv S U$ preserve $F_P$, only $F \equiv S X Y$ ($X, Y \in \mathcal{V}_P$) remains, contracting in one step to $(X Z)(Y Z)$.

Over the $113$-state reachable subalgebra $\mathrm{PH} \subseteq Q_P \times Q_{\mathrm{HN}}$ ($95$ accepting states $\mathrm{PH}_{\mathrm{acc}}$ and $18$ rejecting states), we unify accepted values $V \in \mathcal{V}_P$ (assigned value size $\mathrm{psz}(V) = \mathrm{sz}(V)$) and solvable rejected raw terms $R$ with $\llbracket R \rrbracket_P = \infty_P$ and $\llbracket R \rrbracket_{\mathrm{HN}} \neq \infty_{\mathrm{HN}}$ (assigned value size $\mathrm{psz}(R) = 0$) into a single argument sort. Recording for each $(\mathbf{x}, \mathbf{z}) \in \mathrm{PH}_{\mathrm{acc}}^2$ the finite set $\mathrm{out}_{2\mathrm{d}}(\mathbf{x}, \mathbf{z}) \subseteq \mathrm{PH}_{\mathrm{acc}}^2$ of spine-$2$ child state pairs $(\llbracket A_1 \rrbracket_{\mathrm{PH}}, \llbracket A_2 \rrbracket_{\mathrm{PH}})$ attainable when $\mathrm{app}_{\mathcal{V}_P}(X, V_2) \equiv S A_1 A_2$, and evaluating direct product ranks on $\llbracket X Z \rrbracket_{\mathrm{PH}} \odot_{\mathrm{PH}} \llbracket Y Z \rrbracket_{\mathrm{PH}}$ before expanding spine-$2$ joint critical transitions (shrinking the spine-$2$ joint critical table to $174$ entries across $98$ pairs $(\mathbf{x}, \mathbf{z})$), every critical pair $(\mathbf{f}, \mathbf{z}) \in \mathrm{PH}_{\mathrm{acc}} \times \mathrm{PH}$ with $\mathbf{f} \odot_{\mathrm{PH}} \mathbf{z} \notin \mathrm{PH}_{\mathrm{acc}}$ receives a rank $\rho_2(\mathbf{f}, \mathbf{z}) \in \{1, \dots, 10\}$ and every joint critical triple receives a rank $\rho_3(\mathbf{x}, \mathbf{z}, \mathbf{n}_2) \in \{1, \dots, 10\}$. Without parity splitting, every recursive branch either hits $\infty_{\mathrm{HN}}$ immediately, reduces to Lemma 6.11, strictly decreases the outer rank $r \in \{1, \dots, 10\}$, or stays at rank $r$ while strictly decreasing the unified inner measure ($2\,\mathrm{sz}(F)$ on pairs $(F, Z)$ and $2(\mathrm{sz}(X) + \mathrm{psz}(Y)) + 1$ on triples $(S X Y, Z)$), constructing an explicit finite $d$ with $\bot_d(F Z)$.
 $\square$

**Proposition 6.15 (Myhill–Nerode minimality of the $113$-state joint algebra $\mathrm{PH}$).** 
All $113$ states of $\mathrm{PH} \subseteq \mathcal{A}_P \times \mathcal{A}_{\mathrm{HN}}$ are inhabited by explicit closed $S$-terms $W_0, \dots, W_{112} \in \mathcal{T}_S$, and there exists a fixed family of $17$ closed one-hole contexts $C_0[\square], \dots, C_{16}[\square]$ such that for any two closed $S$-terms $M_1, M_2 \in \mathcal{T}_S$ with $\llbracket M_1 \rrbracket_{\mathrm{PH}} \neq \llbracket M_2 \rrbracket_{\mathrm{PH}}$, some $C_k[\square]$ ($0 \le k < 17$) separates $C_k[M_1]$ from $C_k[M_2]$ on $(\mathrm{Prod}, \mathrm{HN})$:

$$
\neg\Bigl(\bigl(C_k[M_1] \in \mathrm{Prod} \iff C_k[M_2] \in \mathrm{Prod}\bigr) \;\wedge\; \bigl(C_k[M_1] \in \mathrm{HN} \iff C_k[M_2] \in \mathrm{HN}\bigr)\Bigr).
$$

Consequently, every deterministic bottom-up tree automaton or magma quotient $(Q, q_0, \odot)$ on $\mathcal{T}_S$ through which $(\mathrm{Prod}, \mathrm{HN})$ factors has at least $113$ states.

*Proof.* 
Each witness $W_i \in \mathcal{T}_S$ ($0 \le i < 113$) is constructed by breadth-first generation from $S$, and each context $C_k[\square]$ ($0 \le k < 17$) is an iterated left and right application chain built from $\{W_i\}$. On $\mathrm{PH}$, Theorems 6.8(i) and 6.14 partition the $113$ states into three semantic classes: $95$ states in $\mathrm{Prod}$, $17$ states in $\mathrm{HN} \setminus \mathrm{Prod}$, and $1$ state $(\infty_P, \infty_{\mathrm{HN}})$ in $\overline{\mathrm{HN}}$. Direct evaluation over all $\binom{113}{2} = 6{,}328$ unordered state pairs $(i, j)$ confirms that at least one of the $17$ context transitions maps $i$ and $j$ into distinct semantic classes among these three. If $\llbracket \cdot \rrbracket_Q \colon \mathcal{T}_S \to Q$ is any magma homomorphism deciding $(\mathrm{Prod}, \mathrm{HN})$ and $\llbracket W_i \rrbracket_Q = \llbracket W_j \rrbracket_Q$ for $i \neq j$, congruence of $\llbracket \cdot \rrbracket_Q$ under every closed context $C_k[\square]$ gives $\llbracket C_k[W_i] \rrbracket_Q = \llbracket C_k[W_j] \rrbracket_Q$, contradicting semantic separation of $C_k[W_i]$ and $C_k[W_j]$. By the pigeonhole principle, $|Q| \ge 113$.
 $\square$

Even at leaf size $8$, completeness of $\mathcal{A}_P$ requires selective branch choice: chasing the leftmost unproductive child of each $\mathrm{HNF}$ can loop forever without visiting $\infty_{\mathrm{HN}}$.

**Proposition 6.16 (Böhm-game branch asymmetry at leaf size $8$).** 
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

### 6.5. Automaton-Free Book Proofs, Complete Böhm Faithfulness Dichotomy, and Productive Convertibility

Although finite $S$-algebras provide linear-time decision procedures across all of $\mathcal{T}_S$, Questions 7 and 31 of Barendregt et al. [4, pp. 81, 93] admit short, self-contained proofs that require no finite-automaton multiplication tables at all. Following a suggestion of Jörg Endrullis to simplify these arguments as far as possible, we first present a three-constructor syntactic invariant $\mathcal{H}$ (condensing Waldmann's $Q Q Q$ generator [66]) that yields pen-and-paper proofs of both Question 7 (including the atomic $S \mapsto S S$ leaf-splitting law) and the unsolvable half of Question 31. We then combine canonical productive values $\mathcal{V}_P$ from Subsection 6.4 with this unsolvable separation to establish a complete Böhm-tree faithfulness dichotomy on $\mathrm{CL}(S)$ and a total convertibility decider across $\mathrm{Prod} \times \mathcal{T}_S$, advancing Scott's Question 30 [55, 14, 57, 58].

**Definition 6.17 (Three-constructor invariant $\mathcal{H}$ and triple-application class $\mathcal{U}$).** 
Let $\mathcal{H} \subset \mathcal{T}_S$ be the smallest set of closed $S$-terms generated inductively by

$$
\mathcal{H} \;::=\; A \;\mid\; S X \;\mid\; X Y
\qquad (A \equiv S S S,\; X, Y \in \mathcal{H}),
$$

and define the triple-application class $\mathcal{U} := \{ P Q R : P, Q, R \in \mathcal{H} \} \subset \mathcal{T}_S$.

**Lemma 6.18 (Inversion, reduction closure, and divergence of $\mathcal{U}$).** 

- (i) *Inversion:* One has $S \notin \mathcal{H}$ and $\operatorname{ls}(M) \ge 1$ for every $M \in \mathcal{H}$; if $S X \in \mathcal{H}$, then $X \in \mathcal{H}$; and if $S X Y \in \mathcal{H}$, then either $X \equiv Y \equiv S$ or $X, Y \in \mathcal{H}$.
- (ii) *Forward $\to_S$-closure:* Both $\mathcal{H}$ and $\mathcal{U}$ are closed forward under arbitrary single-step reduction $\to_S$.
- (iii) *Divergence:* Every $M \in \mathcal{U}$ satisfies $\operatorname{ls}(M) \ge 3$, $M \notin \mathrm{HN}$, and $M \notin \mathrm{SN}$.

*Proof.* 
For (i), $A \equiv (S S) S$, $S X$, and $X Y$ are all applications, so $S \notin \mathcal{H}$ and $\operatorname{ls}(M) \ge 1$. A term $S X$ cannot arise as $A$ (since $S \not\equiv S S$) or as $U V$ with $U, V \in \mathcal{H}$ (since $S \notin \mathcal{H}$), forcing $X \in \mathcal{H}$. Similarly, $S X Y \equiv (S X) Y$ cannot arise from the second constructor ($S X \not\equiv S$); if it is $A$, then $X \equiv Y \equiv S$, and if it arises as $(S X) Y$ with $S X, Y \in \mathcal{H}$, then $X \in \mathcal{H}$.

For (ii), we first prove that $M \in \mathcal{H}$ and $M \to_S M'$ imply $M' \in \mathcal{H}$ by induction on $M \in \mathcal{H}$. The term $A \in \mathcal{N}$ has no steps; steps inside $S X \to_S S X'$ or inside $U$ or $V$ of $U V$ preserve $\mathcal{H}$ by the induction hypothesis; and if $U V \equiv (S X Y) V \to_r (X V)(Y V)$ with $S X Y, V \in \mathcal{H}$, then (i) gives either $X \equiv Y \equiv S$ (so $(S V)(S V) \in \mathcal{H}$) or $X, Y \in \mathcal{H}$ (so $(X V)(Y V) \in \mathcal{H}$). Next, let $M \equiv P Q R \in \mathcal{U}$ with $P, Q, R \in \mathcal{H}$ and $M \to_S M'$. Steps inside $P$, $Q$, or $R$ preserve $\mathcal{U}$ by $\mathcal{H}$-closure; if $P Q \equiv (S X Y) Q \to_r (X Q)(Y Q)$, then (i) places $X Q, Y Q \in \mathcal{H}$, so $(X Q)(Y Q) R \in \mathcal{U}$; and if $(P Q) R \equiv (S X Y) R \to_r (X R)(Y R)$, then $P \equiv S X$ and $Q \equiv Y$, so (i) gives $X \in \mathcal{H}$ and $M' \equiv X R (Q R) \in \mathcal{U}$.

For (iii), any $M \equiv P Q R \in \mathcal{U}$ has $\operatorname{ls}(M) = \operatorname{ls}(P) + 2 \ge 3$ by (i). By (ii), every reduct $M'$ of $M$ remains in $\mathcal{U}$ and satisfies $\operatorname{ls}(M') \ge 3 > 2$, whence $M \notin \mathrm{HN}$. Since every closed term with $\operatorname{ls} \ge 3$ possesses a head redex $S X Y Z$, iterating head contraction inside $\mathcal{U}$ produces an infinite reduction sequence, proving $M \notin \mathrm{SN}$.
 $\square$

In Question 7 [4, p. 81], Barendregt et al. color $\mathrm{SN}$ green and $\mathcal{T}_S \setminus \mathrm{SN}$ red, asking whether successive single-leaf refinements starting from $S$ can alternate green and red infinitely often. Write $M \prec N$ if $N$ replaces a single $S$-leaf of $M$ by a composite closed $S$-term, and $M \prec_1 N$ for an *atomic leaf split* replacing one $S$-leaf by $T \equiv S S$ (so $|N| = |M| + 1$). Table 6 lists the $10$-term atomic bridge $P_0 \prec_1 \cdots \prec_1 P_9$.

**Table 6.** The $10$-term atomic leaf-splitting bridge $P_0 \prec_1 \cdots \prec_1 P_9$ for Question 7 ($T \equiv S S$, $A \equiv S S S$).

| $r$ | $P_r$ | Automaton-free normalization status |
| ---: | :--- | :--- |
| $0, 1, 2, 3, 4$ | $S,\; T,\; A,\; S T S,\; S A S$ | Closed normal forms in $\mathcal{N}$ |
| $5$ | $S(A S)S$ | $A S \to_S T T \in \mathcal{N}$ ($2$-term reduction graph) |
| $6$ | $S(A T)S$ | $A T \to_S (S T)(S T) \in \mathcal{N}$ ($2$-term reduction graph) |
| $7$ | $S(A A)S$ | $A A \to_S (S A)(S A) \in \mathcal{N}$ ($2$-term reduction graph) |
| $8$ | $S(S T S A)S$ | $S T S A \to_S^3 (S(S A))\bigl((S(S A))(S(S A))\bigr) \in \mathcal{N}$ ($4$-term chain) |
| $9$ | $S(S A S A)S \equiv S\,R(S)\,S$ | Non-normalizing via $R(S) \to_S^2 ((S A)(S A))(S A) \in \mathcal{U}$ |

**Theorem 6.19 (Automaton-free refinement alternation, atomic period-$10$ law, and rescue classification, Question 7 [4, p. 81]).** 
Define the gadget $R(X) \equiv X A S A$ and the right-nested spine $C^0(M) \equiv M$, $C^{k+1}(M) \equiv S\,R(T)\,C^k(M)$.

- (i) *Automaton-free $\mathrm{SN} / \overline{\mathrm{SN}}$ refinement chain:* Without invoking any finite $S$-algebra, $R(S) \equiv S A S A \notin \mathrm{SN}$ whereas $R(T) \equiv T A S A \in \mathrm{SN}$. Setting

$$
F_{2k} \;\equiv\; C^k(S),
\qquad
F_{2k+1} \;\equiv\; C^k\bigl(S\,R(S)\,S\bigr)
\qquad (k \in \mathbb{N}), \tag{6.16}
$$

  one has $F_0 \equiv S$, $F_m \prec F_{m+1}$ for all $m \in \mathbb{N}$, $F_{2k} \in \mathrm{SN}$, and $F_{2k+1} \notin \mathrm{SN}$ for all $k \in \mathbb{N}$.
- (ii) *Exact color pattern under atomic leaf splits $S \mapsto S S$:* With $P_0, \dots, P_9$ as in Table 6, set $T_{10k + r} \equiv C^k(P_r)$ for $k \in \mathbb{N}$ and $0 \le r \le 9$. Then $T_0 \equiv S$, $T_n \prec_1 T_{n+1}$ and $|T_n| = n + 1$ for every $n \in \mathbb{N}$, and

$$
T_n \in \mathrm{SN} \;\Longleftrightarrow\; n \not\equiv 9 \pmod{10}.
$$

- (iii) *Universal one-leaf rescue classification:* Across all $940$ one-hole context functions $f_C \colon Q_{\mathrm{SN}} \to Q_{\mathrm{SN}}$ on $\mathcal{A}_{\mathrm{SN}}$, if $C[S] \notin \mathrm{SN}$ and $C[P] \in \mathrm{SN}$ for $P \in \mathcal{T}_S$, then $\llbracket P \rrbracket_{\mathrm{SN}} \in \{q_1, q_8\}$, forcing $P \equiv S S$ or $P \equiv S(S S S)$ syntactically; both plugs are realized ($C_1[\square] \equiv \square A S A$ and $C_2[\square] \equiv \square (S S) S S S S$).

*Proof.* 
For (i), two steps reduce $R(S) \equiv S A S A \to_S (A A)(S A) \equiv ((S S S) A)(S A) \to_S ((S A)(S A))(S A)$. Since $A \in \mathcal{H}$ implies $S A \in \mathcal{H}$, the term $((S A)(S A))(S A)$ belongs to $\mathcal{U}$, so $R(S) \notin \mathrm{SN}$ by Lemma 6.18(iii). Conversely, since $T, A, S A, T A, T T \in \mathcal{N}$, the complete multiway reduction graph of $R(T) \equiv ((T A) S) A$ has only six terms: $g_0 \equiv ((T A) S) A \to_S g_1 \equiv (T(A S))A$, branching to $g_2 \equiv (S A)((A S) A)$ and $g_3 \equiv (T(T T)) A$, both stepping to $g_4 \equiv (S A)((T T) A) \to_S g_5 \equiv (S A)((S A)(T A)) \in \mathcal{N}$; hence every path terminates in at most $4$ steps and $R(T) \in \mathrm{SN}$. Because $S U V \in \mathrm{SN}$ holds if and only if both $U \in \mathrm{SN}$ and $V \in \mathrm{SN}$ by Lemma 6.1(i), and because $C^{k+1}(S) \equiv C^k(S\,R(T)\,S)$, induction on $k$ gives $F_{2k} \in \mathrm{SN}$, $F_{2k+1} \notin \mathrm{SN}$, and $F_m \prec F_{m+1}$.

For (ii), each step $P_r \prec_1 P_{r+1}$ ($0 \le r \le 8$) and $P_9 \equiv S(S A S A)S \prec_1 S(T A S A)S \equiv S\,R(T)\,S$ splits one $S$-leaf into $S S$ ($r = 4 \to 5$ splits the head of $A$ into $A S$; $r = 7 \to 8$ splits the middle $S$ of the left $A$ in $A A$ into $S T S$; $r = 8 \to 9$ splits the first leaf of $T$ in $S T S A$ into $S A S A$; and $r = 9 \to 10$ splits the head $S$ of $S A S A$ into $R(T)$, matching $C^{k+1}(S) \equiv C^k(S\,R(T)\,S)$). For any $V \in \mathcal{N}$, the application $A V \equiv S S S V$ has the unique step $A V \to_S (S V)(S V) \in \mathcal{N}$, proving $P_5, P_6, P_7 \in \mathrm{SN}$, while $S T S A$ has the unique unbranched $3$-step reduction $S T S A \to_S (T A)(S A) \to_S (S(S A))(A(S A)) \to_S (S(S A))((S(S A))(S(S A))) \in \mathcal{N}$, proving $P_8 \in \mathrm{SN}$. Thus $T_{10k + r} \in \mathrm{SN}$ for $0 \le r \le 8$ and $T_{10k + 9} \notin \mathrm{SN}$.

For (iii), closing $\mathrm{id}_{Q_{\mathrm{SN}}}$ under left and right multiplication on $Q_{\mathrm{SN}}$ yields $940$ context maps, and collecting $\{ x \in Q_{\mathrm{SN}} : \exists f,\, f(q_0) = \infty_{\mathrm{SN}} \textrm{ and } f(x) \neq \infty_{\mathrm{SN}} \}$ gives $\{q_1, q_8\}$. The unique normal forms in $q_1$ and $q_8$ are $S S$ and $S(S S S)$; since the sole reducible closed term of size at most $4$ is $S S S S \to_S S S (S S)$ in $q_9 \notin \{q_1, q_8\}$, Proposition 2.2(ii) forces $P \in \{S S, S(S S S)\}$. On $C_2[\square] \equiv \square(S S)S S S S$, we have $\llbracket C_2[S] \rrbracket_{\mathrm{SN}} = \infty_{\mathrm{SN}}$ whereas $\llbracket C_2[S(S S S)] \rrbracket_{\mathrm{SN}} = q_{30} \neq \infty_{\mathrm{SN}}$ (normalizing in $1{,}109$ leftmost-outermost steps).
 $\square$

We now turn to Question 31 [4, p. 93], which asks whether closed $S$-terms with identical Böhm trees (or identical *clocked* Böhm trees, recording at each node the exact number of deterministic head steps to $\mathrm{HNF}$) must be $=_S$-convertible, highlighting $A A A$ versus $A A A S$. Together, Theorems 6.20 and 6.21 establish a sharp dichotomy: whenever $\bot$ occurs at any finite depth, even clocked Böhm trees fail infinitely to separate $=_S$-classes (provable without any finite algebra); conversely, on all productive ($\bot$-free) terms, ordinary unclocked Böhm-tree equality is completely faithful across $\mathrm{Prod} \times \mathcal{T}_S$.

For any term $M$ and $k \in \mathbb{N}$, define $M S^0 \equiv M$ and $M S^{k+1} \equiv (M S^k) S$. Call $M$ *right-compound* if $M \equiv U (V_1 V_2)$, and let $\tau(M)$ count outer trailing applications to $S$ ($\tau(U S) = 1 + \tau(U)$, and $\tau(M) = 0$ otherwise).

**Theorem 6.20 (Frozen-tail cancellation, clocked-Böhm unfaithfulness, and $\mathcal{A}_{36}$, Question 31 Part I [4, p. 93]).** 

- (i) *Automaton-free frozen-tail cancellation:* For any two right-compound unsolvable terms $M, N \in \mathcal{T}_S(\mathcal{V}) \setminus \mathrm{HN}$ and all $j, k \in \mathbb{N}$,

$$
M S^j =_S N S^k \;\Longleftrightarrow\; \bigl(j = k \;\textrm{ and }\; M =_S N\bigr).
$$

  In particular, since $A A A \in \mathcal{U}$ satisfies $A A A \notin \mathrm{HN}$ by Lemma 6.18(iii) and has right child $A \equiv (S S) S$, one has $A A A S^j =_S A A A S^k$ if and only if $j = k$, without invoking any finite $S$-algebra, and hence $A A A \neq_S A A A S$.
- (ii) *Clocked-Böhm unfaithfulness at arbitrary $\bot$-depth $D$:* Define $W_0(U) \equiv U$ and $W_{D+1}(U) \equiv S\,W_D(U)$. For every depth $D \in \mathbb{N}$ and all $j \neq k$, the closed terms $W_D(A A A S^j)$ and $W_D(A A A S^k)$ are head-normalizing through depth $D - 1$, share identical Böhm and clocked Böhm trees at every depth $d \in \mathbb{N}$ (with a single $\bot$ at depth $D$), yet satisfy $W_D(A A A S^j) \neq_S W_D(A A A S^k)$.
- (iii) *Homomorphic $36$-state separation:* Splitting $\infty_{\mathrm{HN}}$ into $\{q_{34}, q_{35}\}$ on $Q_{36} = \{q_0, \dots, q_{35}\}$ via

$$
x \odot_{36} y \;=\;
\begin{cases}
x \odot_{\mathrm{HN}} \tilde{y} & \textrm{if } x \in \{q_0, \dots, q_{33}\} \textrm{ and } x \odot_{\mathrm{HN}} \tilde{y} \neq \infty_{\mathrm{HN}}, \\
q_{34} & \textrm{if } x \in \{q_0, \dots, q_{33}\} \textrm{ and } x \odot_{\mathrm{HN}} \tilde{y} = \infty_{\mathrm{HN}}, \\
q_{35} & \textrm{if } x \in \{q_{34}, q_{35}\} \textrm{ and } y = q_0, \\
q_{34} & \textrm{if } x \in \{q_{34}, q_{35}\} \textrm{ and } y \in \{q_1, \dots, q_{35}\},
\end{cases} \tag{6.17}
$$

  where $\tilde{y} = y$ for $y \in \{q_0, \dots, q_{33}\}$ and $\tilde{y} = \infty_{\mathrm{HN}}$ for $y \in \{q_{34}, q_{35}\}$, defines a $36$-state finite $S$-algebra $\mathcal{A}_{36}$ with $\llbracket A A A \rrbracket_{36} = q_{34} \neq q_{35} = \llbracket A A A S \rrbracket_{36}$ (while no $S$-algebra of size at most $5$ separates $A A A$ from $A A A S$).

*Proof.* 
For (i), observe first that right-compoundness is preserved under $\to_S$: a root step $(S X Y) Z \to_r (X Z)(Y Z)$ creates compound right child $Y Z$, a left step leaves the right child unchanged, and a right step reduces an application to an application. Thus every reduct $M'$ of $M$ has $\tau(M') = 0$ and $\tau(M' S^k) = k$. Next, we show by induction on $k$ that if $M \notin \mathrm{HN}$ and $M S^k \to_S^* W$, then $W \equiv M' S^k$ for some $M'$ with $M \to_S^* M'$. For $k + 1$, along any single step $(M_1 S^k) S \to_S V$ (with $M \to_S^* M_1$), the right child $S$ is irreducible, and a root step would require $M_1 S^k \equiv S X Y$, which for $k \in \{0, 1, 2\}$ gives $\operatorname{ls}(M_1) \le 2$ (contradicting $M \notin \mathrm{HN}$) and for $k \ge 3$ equates an application $M_1 S^{k-2}$ with $S$; hence the step occurs inside $M_1 S^k$, and the outer hypothesis yields $V \equiv M_2 S^{k+1}$. Now if $M S^j =_S N S^k$, Church–Rosser gives a common reduct $W$ with $M' S^j \equiv W \equiv N' S^k$ where $M \to_S^* M'$ and $N \to_S^* N'$. Applying $\tau$ gives $j = \tau(M' S^j) = \tau(N' S^k) = k$, and syntactic cancellation of $S^j$ gives $M' \equiv N'$, whence $M =_S N$. The converse is immediate by congruence.

For (ii), every $A A A S^k$ has $\llbracket A A A S^k \rrbracket_{\mathrm{HN}} = \infty_{\mathrm{HN}}$, so at depth $D = 0$ all $A A A S^k$ have clocked Böhm tree $\bot$. Inducting on $D$, each $W_{D+1}(U) \equiv S\,W_D(U)$ is already in $\mathrm{HNF}$ with head-step clock $0$ and sole child $W_D(U)$, preserving equality of all clocked Böhm approximants; meanwhile, Church–Rosser inversion on $S A_1 =_S S A_2$ implies $A_1 =_S A_2$, lifting $A A A S^j \neq_S A A A S^k$ to $W_D(A A A S^j) \neq_S W_D(A A A S^k)$.

For (iii), let $\pi \colon Q_{36} \to Q_{\mathrm{HN}}$ merge $\{q_{34}, q_{35}\}$ into $\infty_{\mathrm{HN}}$. Whenever $\pi(((q_0 \odot_{36} x) \odot_{36} y) \odot_{36} z) \neq \infty_{\mathrm{HN}}$, (2.3) holds because $\pi$ is a homomorphism. When $\pi$ maps both sides to $\infty_{\mathrm{HN}}$, $(q_0 \odot_{36} x) \odot_{36} y \in \{q_0, \dots, q_{33}\}$ forces the left-hand side of (2.3) to be $q_{34}$, while $y \odot_{36} z \neq q_0$ forces $(x \odot_{36} z) \odot_{36} (y \odot_{36} z) = q_{34}$ on the right. Direct evaluation gives $\llbracket A A A \rrbracket_{36} = q_{34} \neq q_{35} = q_{34} \odot_{36} q_0 = \llbracket A A A S \rrbracket_{36}$, and constraint propagation rules out separating $S$-algebras of size at most $5$.
 $\square$

**Theorem 6.21 (Productive Böhm-tree faithfulness and clocked-Böhm fine structure, Question 31 Part II).** 
Let $\operatorname{BT}_d(M)$ ($d \in \mathbb{N}$) denote the computable depth-$d$ Böhm-tree approximant of $M \in \mathcal{T}_S$ (returning truncation at $d = 0$, $\bot$ if $\llbracket M \rrbracket_{\mathrm{HN}} = \infty_{\mathrm{HN}}$, and $S\,\operatorname{BT}_{d-1}(A_1)\cdots\operatorname{BT}_{d-1}(A_r)$ if $M \to_h^* S A_1 \dots A_r \in \mathrm{HNF}$), and let $\mathrm{CBT}_d(M)$ additionally label each non-$\bot$ node by its exact head-step count to $\mathrm{HNF}$.

- (i) *One-sided Böhm faithfulness across $\mathrm{Prod} \times \mathcal{T}_S$:* For every productive closed $S$-term $M \in \mathrm{Prod}$ and *every* closed $S$-term $N \in \mathcal{T}_S$,

$$
M =_S N \;\Longleftrightarrow\; \forall d \in \mathbb{N},\; \operatorname{BT}_d(M) = \operatorname{BT}_d(N).
$$

- (ii) *Clocked-Böhm non-invariance versus non-$\mathrm{SN}$ collision:* On $\mathrm{Prod} \setminus \mathrm{SN}$, the convertible terms $Z_{\mathrm{Zac}} \equiv G_0 G_0$ and $G_1 G_1$ satisfy $\mathrm{CBT}_1(G_0 G_0) \neq \mathrm{CBT}_1(G_1 G_1)$ (root head clocks $2$ versus $1$). Conversely, setting $E \equiv (S(S T)(S T))T$, the $12$-leaf term $M_{12} \equiv S T (S(S T)(S T)) T$ and the $13$-leaf term $M_{13} \equiv A S E$ lie in $\mathrm{Prod} \setminus \mathrm{SN}$, satisfy $M_{12} \not\to_S^* M_{13}$ and $M_{13} \not\to_S^* M_{12}$, yet share $\mathrm{CBT}_d(M_{12}) = \mathrm{CBT}_d(M_{13})$ for all $d \in \mathbb{N}$ and satisfy $M_{12} =_S M_{13}$.

*Proof.* 
For (i), forward soundness (that $M =_S N$ implies $\operatorname{BT}_d(M) = \operatorname{BT}_d(N)$) holds by induction on $d$: conversion preserves $\llbracket \cdot \rrbracket_{\mathrm{HN}}$, and if $M \to_h^* H_1 \in \mathrm{HNF}$ and $N \to_h^* H_2 \in \mathrm{HNF}$ with $H_1 =_S H_2$, Church–Rosser aligns the spine arities of $H_1$ and $H_2$ and gives componentwise $=_S$ between their spine arguments.

Conversely, suppose $M \in \mathrm{Prod}$ and $\operatorname{BT}_d(M) = \operatorname{BT}_d(N)$ for all $d \in \mathbb{N}$. A closed term lies in $\mathrm{Prod}$ if and only if $\operatorname{BT}_d$ contains no $\bot$ for every $d$; hence $N \in \mathrm{Prod}$ as well. By Theorem 6.14 and Lemma 6.13, $M \to_S^* U \in \mathcal{V}_P$ and $N \to_S^* V \in \mathcal{V}_P$, and soundness gives $\operatorname{BT}_d(U) = \operatorname{BT}_d(V)$ for all $d$. First, observe *finite-depth normal-form rigidity*: for any closed normal form $W \in \mathcal{N}$ and any $X \in \mathcal{T}_S$, the equality $\operatorname{BT}_{|W|}(X) = \operatorname{BT}_{|W|}(W)$ implies $X \to_S^* W$ (by induction on $|W|$ across $S$, $S W_1$, and $S W_1 W_2$ using downward monotonicity of $\operatorname{BT}_d$ equality). Moreover, for $A_0 \in \mathcal{V}_P$ and $W \in \mathcal{N}$, one has $A_0 =_S W$ if and only if $A_0 \equiv W$: if $A_0$ contains no $G_m G_n$ constructor, then $A_0 \in \mathcal{N}$ and confluence forces $A_0 \equiv W$; if $A_0$ contains some $G_m G_n$, two-sided sink absorption in $\mathcal{A}_{\mathrm{SN}}$ gives $\llbracket A_0 \rrbracket_{\mathrm{SN}} = \infty_{\mathrm{SN}} \neq \llbracket W \rrbracket_{\mathrm{SN}}$, ruling out $A_0 =_S W$.

Now normalize root $G_0 G_n$ values via the size-preserving head step $\nu(G_0 G_n) = G_{n+1} G_{n+1}$ ($\nu(U) = U$ otherwise, keeping $\mathrm{sz}(\nu(U)) = \mathrm{sz}(U)$ and $U \to_S^* \nu(U)$). We construct a common reduct $K \in \mathcal{T}_S$ with $U \to_S^* K$ and $V \to_S^* K$ by induction on $\mathrm{sz}(U) + \mathrm{sz}(V)$ whenever $\operatorname{BT}_d(U) = \operatorname{BT}_d(V)$ holds for all $d \in \mathbb{N}$:

- (a) If $\nu(U)$ and $\nu(V)$ are both $S$, both $S X_i$, or both $S A_i B_i$ (mismatching root arities are excluded at $d = 1$), $\operatorname{BT}_{d+1}$ projects equality to the corresponding children of smaller structural size, and the induction hypothesis joins them componentwise.
- (b) In the cross-case $\nu(U) \equiv S A_1 B_1$ and $\nu(V) \equiv G_{k+1} G_n$ (or symmetrically), recall $G_{k+1} G_n \to_h S G_n (G_k G_n)$ where $G_n \in \mathcal{N}$. Comparing $\operatorname{BT}_{d+1}$ gives $\operatorname{BT}_{|G_n|}(A_1) = \operatorname{BT}_{|G_n|}(G_n)$ and $\operatorname{BT}_d(B_1) = \operatorname{BT}_d(G_k G_n)$ for all $d \in \mathbb{N}$. By normal-form rigidity, $A_1 \to_S^* G_n$ and hence $A_1 \equiv G_n$. Since $\mathrm{sz}(B_1) + \mathrm{sz}(G_k G_n) = \mathrm{sz}(B_1) + 1 < (\mathrm{sz}(A_1) + \mathrm{sz}(B_1) + 1) + 1 = \mathrm{sz}(U) + \mathrm{sz}(V)$, the induction hypothesis constructs $K_B$ with $B_1 \to_S^* K_B$ and $G_k G_n \to_S^* K_B$, yielding the common reduct $S G_n K_B$.
- (c) When $\nu(U) \equiv G_{k_1+1} G_{n_1}$ and $\nu(V) \equiv G_{k_2+1} G_{n_2}$, comparing left children at depth $|G_{n_2}| + 1$ gives $G_{n_1} \to_S^* G_{n_2} \in \mathcal{N}$, so $G_{n_1} \equiv G_{n_2}$ and $n_1 = n_2 = n$ (since $|G_n| = 2n + 5$). Induction on $\min(k_1, k_2)$ then forces $k_1 = k_2$: if $k_1 = 0 < k_2$, unfolding two levels exposes $G_0 G_n \to_h G_{n+1} G_{n+1} \to_h S G_{n+1} (G_n G_{n+1})$ against $G_{k_2} G_n \to_h S G_n (G_{k_2-1} G_n)$, forcing $G_{n+1} \equiv G_n$, impossible. Thus $k_1 = k_2$ and $\nu(U) \equiv \nu(V)$ is already the common reduct.

Hence $U =_S V$ and $M =_S N$.

For (ii), $G_0 G_0 \to_h G_1 G_1 \to_h S G_1 (G_0 G_1) \in \mathrm{HNF}$ gives root clock $2$ for $G_0 G_0$ versus $1$ for $G_1 G_1$. Meanwhile, $M_{12} \equiv S T (S(S T)(S T)) T$ and $M_{13} \equiv (S S S) S E$ both step in a single head contraction to the common reduct $Q_{\mathrm{mid}} \equiv (T T) E$, so every node of $\mathrm{CBT}_d(M_{12})$ and $\mathrm{CBT}_d(M_{13})$ has identical clock $1 + \mathrm{clk}(Q_{\mathrm{mid}})$ at the root and identical subtrees below. Yet $|M_{13}| = 13 > 12 = |M_{12}|$ forbids $M_{13} \to_S^* M_{12}$, while the unique step from $M_{12}$ is $M_{12} \to_S Q_{\mathrm{mid}}$ ($13$ leaves, $\not\equiv M_{13}$), and every redex inside $Q_{\mathrm{mid}}$ has a compound third argument ($T$ or $S T$), strictly increasing leaf count to at least $14$ and forbidding $M_{12} \to_S^* M_{13}$.
 $\square$

**Proposition 6.22 (Finiteness of normalizing classes, isolated normal forms, and $\mathrm{Prod} \times \mathcal{T}_S$ decidability, Question 30).** 
Let $\mathrm{gk} \colon \mathcal{T}_S(\mathcal{V}) \to \mathcal{T}_S(\mathcal{V})$ denote Takahashi's complete parallel development [59] (the Gross–Knuth operator $\Delta$ of Proposition 2.2(i)).

- (i) *Cofinality of $\mathrm{gk}$ and exact leaf-growth dichotomy:* For all $M, N \in \mathcal{T}_S(\mathcal{V})$, one has $M =_S N$ if and only if there exists $m \in \mathbb{N}$ such that $N \to_S^* \mathrm{gk}^m(M)$, and $M \to_S^* N$ is constructively decidable. On every root contraction, $|(X Z)(Y Z)| = |S X Y Z| + (|Z| - 1)$; hence on closed terms $M \to_S M'$ preserves leaf count ($|M| = |M'|$) if and only if the contracted redex has atomic third argument $S$, and otherwise $|M'| \ge |M| + 1$.
- (ii) *Strict finiteness of closed normalizing $=_S$-classes and isolated normal forms:* For every $V \in \mathcal{N}$, $[V]_{=_S} \cap \mathcal{T}_S = \{ N \in \mathcal{T}_S : N \to_S^* V \}$ with $|N| \le |V|$, so for every closed $M \in \mathrm{SN}$, its closed conversion class $[M]_{=_S} \cap \mathcal{T}_S$ is strictly finite and constructively enumerable without duplicates. A normal form $V \in \mathrm{NF}$ is isolated ($[V]_{=_S} = \{V\}$) if and only if $V$ contains no subterm of the form $(X Z)(Y Z)$ with identical right subterms $Z$, witnessed by the infinite right-comb family $R_n$ ($n \ge 1$, $|R_n| = n$) and the spine-$2$ family $S S R_{k+3}$ ($k \in \mathbb{N}$, $|S S R_{k+3}| = k + 5$).
- (iii) *RNF decomposition, total $\mathrm{Prod} \times \mathcal{T}_S$ decidability, and failure of right-cancellation:* For all $A_1 B_1, A_2 B_2 \in \mathrm{RNF}$, one has $A_1 B_1 =_S A_2 B_2$ if and only if both $A_1 =_S A_2$ and $B_1 =_S B_2$. Across all pairs $(M, N) \in \mathrm{Prod} \times \mathcal{T}_S$ (strictly extending $\mathrm{SN} \times \mathcal{T}_S$ since $\mathrm{SN} \subsetneq \mathrm{Prod}$), convertibility $M =_S N$ is constructively decidable, and whenever $M =_S N$ holds, an explicit common reduct $W \in \mathcal{T}_S$ satisfying $M \to_S^* W$ and $N \to_S^* W$ is constructible; by contrast, right-cancellation fails even on $\mathcal{N}$, witnessed by $N_1 \equiv S(S A S)S \neq_S S A (S A S) \equiv N_2$ with $N_1 S =_S N_2 S$, and universally by Waldmann's pair $U_1 \equiv S(S T S)A \neq_S S(T A)(S A S) \equiv U_2$ satisfying $U_1 Z =_S U_2 Z$ for every $Z \in \mathcal{T}_S(\mathcal{V})$.

*Proof.* 
For (i), iterating Takahashi's triangle property (that $M \Rightarrow N$ implies $N \Rightarrow \mathrm{gk}(M)$) yields equivalence between $M =_S N$ and the existence of $m \in \mathbb{N}$ with $N \to_S^* \mathrm{gk}^m(M)$, while decidability of $\to_S^*$ holds by Proposition 2.4(i). Expanding $|(X Z)(Y Z)| = |X| + |Y| + 2|Z| = (1 + |X| + |Y| + |Z|) + (|Z| - 1)$ shows that leaf count is preserved if and only if $|Z| = 1$, which on closed terms means $Z \equiv S$.

For (ii), if $V \in \mathcal{N}$ and $N =_S V$, Church–Rosser yields a common reduct $W$ with $N \to_S^* W$ and $V \to_S^* W$; irreducibility of $V$ gives $W \equiv V$, so $N \to_S^* V$ and $|N| \le |V|$ by Proposition 2.2(ii). Filtering the finite duplicate-free list of closed $S$-terms of leaf count at most $|\mathrm{norm}(M)|$ by decidable reachability $\to_S^* \mathrm{norm}(M)$ enumerates $[M]_{=_S} \cap \mathcal{T}_S$. Moreover, a term $V$ admits a one-step predecessor $U \to_S V$ if and only if $V$ contains $(X Z)(Y Z)$ (contracted from $S X Y Z$ at that subterm); for $V \in \mathrm{NF}$, $[V]_{=_S} = \{N : N \to_S^* V\}$ equals $\{V\}$ if and only if $V$ has no one-step predecessor. In $R_{n+1} \equiv S R_n$, the left child of every application is $S$ (not an application), so no $(X Z)(Y Z)$ occurs; in $S S R_{k+3}$, the children $(S S)$ and $R_{k+3} \equiv S R_{k+2}$ have distinct right subterms $S \not\equiv R_{k+2}$ ($|R_{k+2}| = k + 2 \ge 2$), so $S S R_{k+3}$ is isolated for every $k \in \mathbb{N}$.

For (iii), RNF decomposition and the counterexamples $(N_1, N_2)$ and $(U_1, U_2)$ follow by Church–Rosser (since root contractions cannot occur from $\mathrm{RNF}$, while $\mathrm{gk}^6(N_1 S) \equiv \mathrm{gk}^6(N_2 S)$ and $U_1 Z \to_S^5 (P_Z(P_Z P_Z))(Z P_Z(P_Z P_Z)) \leftarrow_S^6 U_2 Z$ for $P_Z \equiv S Z$). Finally, given $M \in \mathrm{Prod}$ and arbitrary $N \in \mathcal{T}_S$, test $\llbracket N \rrbracket_P \neq \infty_P$: if $\llbracket N \rrbracket_P = \infty_P$, conversion invariance of $\mathcal{A}_P$ refutes $M =_S N$; if $\llbracket N \rrbracket_P \neq \infty_P$, normalize $M \to_S^* U \in \mathcal{V}_P$ and $N \to_S^* V \in \mathcal{V}_P$ via Lemma 6.13, and run the structural recursion of Theorem 6.21(i) bounded by $\mathrm{sz}(U) + \mathrm{sz}(V)$, which decides $U =_S V$ (hence $M =_S N$) and returns an explicit common reduct $W$ whenever $M =_S N$.
 $\square$

Whether convertibility $=_S$ remains decidable on general pairs of non-productive closed pure-$S$ terms $(\mathcal{T}_S \setminus \mathrm{Prod})^2$ (Scott's Question 30 in full generality) remains open.

### 6.6. Functional Order $\{0, 1, 2, 3\}$ Hierarchy and Minimal $S$-Algebras

In Section 5.5 and Appendix A.3 of Barendregt, Endrullis, Klop, and Waldmann [4, pp. 89–91, 99–101], pure-$S$ combinators are stratified by their *functional order* (in the sense of Curry and Feys [20]), which measures how many fresh arguments a term can actively consume before all subsequent arguments play a purely dummy role. By Proposition 2.4(iii) (due to Visser and van Oostrom), every term in $\mathrm{CL}(S)$ has order at most $3$. Here we show that extending $\mathcal{A}_{\mathrm{HN}}$ to open terms by mapping variables to $\infty_{\mathrm{HN}}$ characterizes exact functional order across all open and closed $S$-terms, proves that closed order-$3$ terms are uniquely right combs, and determines the exact minimal $S$-algebras for every order class.

**Definition 6.23 (Open solvability evaluation and Curry–Feys functional order).** 

- (i) Define the open evaluation homomorphism $\llbracket \cdot \rrbracket_{\mathrm{HN}}^{\mathrm{open}} \colon \mathcal{T}_S(\mathcal{V}) \to Q_{\mathrm{HN}}$ by $\llbracket S \rrbracket_{\mathrm{HN}}^{\mathrm{open}} = q_0$, $\llbracket x \rrbracket_{\mathrm{HN}}^{\mathrm{open}} = \infty_{\mathrm{HN}}$ for every $x \in \mathcal{V}$, and $\llbracket M N \rrbracket_{\mathrm{HN}}^{\mathrm{open}} = \llbracket M \rrbracket_{\mathrm{HN}}^{\mathrm{open}} \odot_{\mathrm{HN}} \llbracket N \rrbracket_{\mathrm{HN}}^{\mathrm{open}}$ (agreeing with $\llbracket M \rrbracket_{\mathrm{HN}}$ on $\mathcal{T}_S$). Call $U \in \mathcal{T}_S(\mathcal{V})$ an *$S$-headed head normal form* if $U \equiv S$, $U \equiv S A_1$, or $U \equiv S A_1 A_2$.
- (ii) Following [4, Definition 37, p. 99], a term $F \in \mathcal{T}_S(\mathcal{V})$ has *dummy variable tails* if for every nonempty list of variables $y_1, \dots, y_r$ ($r \ge 1$) not occurring in $F$ and every reduction $F y_1 \cdots y_r \to_S^* N$, there exists $F'$ with $F \to_S^* F'$, no $y_i$ occurring in $F'$, and $N \equiv F' y_1 \cdots y_r$. A term $M \in \mathcal{T}_S(\mathcal{V})$ has *order at most $k$* ($\operatorname{ord}(M) \le k$) if $M x_1 \cdots x_k$ has dummy variable tails for $k$ distinct fresh variables $x_1, \dots, x_k$ not occurring in $M$, and has *exact order $k$* ($\operatorname{ord}(M) = k$) if $\operatorname{ord}(M) \le k$ and $\operatorname{ord}(M) \not\le j$ for all $j < k$.

**Lemma 6.24 (Universal open solvability characterization).** 
For every open or closed $S$-term $M \in \mathcal{T}_S(\mathcal{V})$, the term $M$ reduces under $\to_S^*$ to an $S$-headed head normal form if and only if $\llbracket M \rrbracket_{\mathrm{HN}}^{\mathrm{open}} \neq \infty_{\mathrm{HN}}$. Consequently, $F \in \mathcal{T}_S(\mathcal{V})$ has dummy variable tails if and only if $\llbracket F \rrbracket_{\mathrm{HN}}^{\mathrm{open}} = \infty_{\mathrm{HN}}$.

*Proof.* 
Because $\mathcal{A}_{\mathrm{HN}}$ satisfies (2.3), $\llbracket \cdot \rrbracket_{\mathrm{HN}}^{\mathrm{open}}$ is invariant under $=_S$, and $q_0$, $q_0 \odot_{\mathrm{HN}} a$, and $(q_0 \odot_{\mathrm{HN}} a) \odot_{\mathrm{HN}} b$ never equal $\infty_{\mathrm{HN}}$; thus reducing to an $S$-headed $\mathrm{HNF}$ implies $\llbracket M \rrbracket_{\mathrm{HN}}^{\mathrm{open}} \neq \infty_{\mathrm{HN}}$. Conversely, suppose $\llbracket M \rrbracket_{\mathrm{HN}}^{\mathrm{open}} \neq \infty_{\mathrm{HN}}$, and fix the $8$-leaf closed unsolvable term $W_{34} \equiv S S S (S A) S \in \mathcal{T}_S$ satisfying $\llbracket W_{34} \rrbracket_{\mathrm{HN}} = \infty_{\mathrm{HN}}$. Let $\sigma_{34} \colon \mathcal{T}_S(\mathcal{V}) \to \mathcal{T}_S$ substitute $W_{34}$ for every variable. Structural induction gives $\llbracket \sigma_{34}(P) \rrbracket_{\mathrm{HN}} = \llbracket P \rrbracket_{\mathrm{HN}}^{\mathrm{open}}$ for all $P \in \mathcal{T}_S(\mathcal{V})$, and every open head step $P \to_h P'$ induces a closed head step $\sigma_{34}(P) \to_h \sigma_{34}(P')$, decreasing $\mu_{\mathrm{HN}}(\sigma_{34}(P))$ by at least $1$ via Lemma 6.6. Hence open head reduction from $M$ terminates within $\mu_{\mathrm{HN}}(\sigma_{34}(M))$ steps at a head-irreducible term $U^*$ with $\llbracket U^* \rrbracket_{\mathrm{HN}}^{\mathrm{open}} = \llbracket M \rrbracket_{\mathrm{HN}}^{\mathrm{open}} \neq \infty_{\mathrm{HN}}$. Any head-irreducible open term either has a variable leftmost leaf (forcing $\llbracket U^* \rrbracket_{\mathrm{HN}}^{\mathrm{open}} = \infty_{\mathrm{HN}}$ by left absorption $\infty_{\mathrm{HN}} \odot_{\mathrm{HN}} y = \infty_{\mathrm{HN}}$, a contradiction) or is an $S$-headed $\mathrm{HNF}$.

For the second equivalence, if $\llbracket F \rrbracket_{\mathrm{HN}}^{\mathrm{open}} \neq \infty_{\mathrm{HN}}$, then $F \to_S^* U$ where $U \equiv S$, $S A_1$, or $S A_1 A_2$. Appending $r = 3$, $2$, or $1$ fresh variables $y_1, \dots, y_r$ yields $F y_1 \cdots y_r \to_S^* (P y_r)(Q y_r)$ whose right child $Q y_r$ has leaf count $|Q| + 1 \ge 2$, which cannot equal $F' y_1 \cdots y_r$ (whose right child $y_r$ has leaf count $1$). Conversely, if $\llbracket F \rrbracket_{\mathrm{HN}}^{\mathrm{open}} = \infty_{\mathrm{HN}}$, then neither $F$ nor any $F y_1 \cdots y_j$ ($\llbracket F y_1 \cdots y_j \rrbracket_{\mathrm{HN}}^{\mathrm{open}} = \infty_{\mathrm{HN}}$) can reduce to any $S P Q$, so no root contraction ever consumes any $y_i$, and induction on $r$ yields $N \equiv F' y_1 \cdots y_r$ with $F \to_S^* F'$ and $y_i$ absent from $F'$.
 $\square$

**Theorem 6.25 (Order $\{0, 1, 2, 3\}$ classification, right-comb uniqueness, and minimal $S$-algebras).** 
Define the right-translation map $\tau_{\mathrm{HN}}(q) := q \odot_{\mathrm{HN}} \infty_{\mathrm{HN}}$ on $Q_{\mathrm{HN}}$.

- (i) *Nilpotency and $35 = 1 + 11 + 17 + 6$ state partition:* One has $\tau_{\mathrm{HN}}^3(q) = \infty_{\mathrm{HN}}$ for every $q \in Q_{\mathrm{HN}}$, partitioning $Q_{\mathrm{HN}}$ by nilpotency index $\mathrm{ord}_{\mathrm{HN}}(q) := \min\{k \in \mathbb{N} : \tau_{\mathrm{HN}}^k(q) = \infty_{\mathrm{HN}}\} \in \{0, 1, 2, 3\}$ into $1$ state of order $0$ ($\{\infty_{\mathrm{HN}}\}$), $11$ states of order $1$ ($\{q_{22}, \dots, q_{26}, q_{28}, \dots, q_{33}\}$), $17$ states of order $2$ ($\{q_6, \dots, q_{21}, q_{27}\}$), and $6$ states of order $3$ ($\{q_0, \dots, q_5\}$). For every open or closed $M \in \mathcal{T}_S(\mathcal{V})$, one has $\operatorname{ord}(M) = \mathrm{ord}_{\mathrm{HN}}(\llbracket M \rrbracket_{\mathrm{HN}}^{\mathrm{open}}) \in \{0, 1, 2, 3\}$, which is $=_S$-invariant and agrees on closed $M \in \mathcal{T}_S$ with single-variable consumption [4, Definition 21]:

$$
\begin{aligned}
\operatorname{ord}(M) = 0 &\;\Longleftrightarrow\; M \notin \mathrm{HN}, \\
\operatorname{ord}(M) = 1 &\;\Longleftrightarrow\; M \in \mathrm{HN},\; M \not\equiv S,\;\textrm{and}\; \neg\exists A_1, A_2,\; M x_0 \to_S^* S A_1 A_2, \\
\operatorname{ord}(M) = 2 &\;\Longleftrightarrow\; M \not\equiv S,\; \bigl(\exists A_1, A_2,\; M x_0 \to_S^* S A_1 A_2\bigr),\;\textrm{and}\; \neg\exists A_1, A_2,\; M x_0 x_1 \to_S^* S A_1 A_2, \\
\operatorname{ord}(M) = 3 &\;\Longleftrightarrow\; \exists A_1, A_2,\; M x_0 x_1 \to_S^* S A_1 A_2.
\end{aligned}
$$

- (ii) *Uniqueness of closed order-$3$ terms and sharp small-size thresholds:* A closed $S$-term $M \in \mathcal{T}_S$ satisfies $\operatorname{ord}(M) = 3$ if and only if $M \equiv R_{|M|}$ is the unique right comb of leaf size $|M|$ (Definition 2.1). Every closed $S$-term of leaf size at most $2$ has order $3$; at size $3$, the term $A \equiv S S S$ is the unique closed term of order $2$; every closed term of size at most $4$ has order at least $2$; at size $5$, the normal form $S(S S S)S$ is the unique closed term of order $1$; and order $0$ first appears at size $8$ ($15$ closed terms).
- (iii) *Exact minimal $S$-algebras of sizes $35$, $12$, and $3$:* On $\mathcal{T}_S$, any deterministic bottom-up tree automaton deciding $\{\operatorname{ord} = 0\}$, $\{\operatorname{ord} = 1\}$, $\{\operatorname{ord} \ge 1\}$, or $4$-valued $\operatorname{ord}$ has at least $35$ states, matching $\mathcal{A}_{\mathrm{HN}}$; $\{\operatorname{ord} = 2\}$ and $\{\operatorname{ord} \ge 2\}$ are both decided by a $12$-state quotient $S$-algebra $\mathcal{A}_{\mathrm{ord},2}$ of $\mathcal{A}_{\mathrm{HN}}$, and any deterministic bottom-up tree automaton deciding either set has at least $12$ states; and $\{\operatorname{ord} = 3\}$ is decided by a $3$-state quotient $S$-algebra $\mathcal{A}_{\mathrm{ord},3}$, with matching universal lower bound $3$.

*Proof.* 
For (i), direct evaluation on $Q_{\mathrm{HN}}$ verifies $\tau_{\mathrm{HN}}^3(q) = \infty_{\mathrm{HN}}$ and the $1 + 11 + 17 + 6 = 35$ partition. For any $M \in \mathcal{T}_S(\mathcal{V})$ and fresh variables $x_1, \dots, x_k$, we have $\llbracket M x_1 \cdots x_k \rrbracket_{\mathrm{HN}}^{\mathrm{open}} = \tau_{\mathrm{HN}}^k(\llbracket M \rrbracket_{\mathrm{HN}}^{\mathrm{open}})$, so Lemma 6.24 shows that $\operatorname{ord}(M) \le k$ holds if and only if $\tau_{\mathrm{HN}}^k(\llbracket M \rrbracket_{\mathrm{HN}}^{\mathrm{open}}) = \infty_{\mathrm{HN}}$, which holds if and only if $\mathrm{ord}_{\mathrm{HN}}(\llbracket M \rrbracket_{\mathrm{HN}}^{\mathrm{open}}) \le k$, proving $\operatorname{ord}(M) = \mathrm{ord}_{\mathrm{HN}}(\llbracket M \rrbracket_{\mathrm{HN}}^{\mathrm{open}})$. On closed $M \in \mathcal{T}_S$ with $M \not\equiv S$ (so $M$ is an application), Lemma 6.5(i) excludes $M x_0 \to_S^* S$ and $M x_0 \to_S^* S W$ (and likewise for $M x_0 x_1$); hence Lemma 6.24 equates the existence of $A_1, A_2$ with $M x_0 \to_S^* S A_1 A_2$ to $\tau_{\mathrm{HN}}(\llbracket M \rrbracket_{\mathrm{HN}}) \neq \infty_{\mathrm{HN}}$, and equates the existence of $A_1, A_2$ with $M x_0 x_1 \to_S^* S A_1 A_2$ to $\tau_{\mathrm{HN}}^2(\llbracket M \rrbracket_{\mathrm{HN}}) \neq \infty_{\mathrm{HN}}$, yielding the four single-variable clauses.

For (ii), inspecting all $35^2$ pairs in $\mathcal{A}_{\mathrm{HN}}$ confirms that $\mathrm{ord}_{\mathrm{HN}}(a \odot_{\mathrm{HN}} b) = 3$ holds if and only if $a = q_0$ and $\mathrm{ord}_{\mathrm{HN}}(b) = 3$. Since $\llbracket U \rrbracket_{\mathrm{HN}} = q_0$ holds for $U \in \mathcal{T}_S$ if and only if $U \equiv S$, structural induction on $M \in \mathcal{T}_S$ gives $\operatorname{ord}(M) = 3$ if and only if $M \equiv R_{|M|}$. Enumeration of $\mathcal{T}_S$ for $|M| \le 5$ ($1, 1, 2, 5, 14$ Catalan trees) confirms that $|M| \le 2$ gives $\{S, S S\}$ (order $3$), $|M| = 3$ gives $S(S S)$ (order $3$) and $S S S$ (order $2$), $|M| = 4$ contains only orders $2$ and $3$, and among the $14$ closed terms of size $5$, the term $S(S S S)S$ ($\llbracket S(S S S)S \rrbracket_{\mathrm{HN}} = q_{26}$) is the sole term of order $1$.

For (iii), define the $12$-state quotient $\pi_2 \colon Q_{\mathrm{HN}} \to Q_{\mathrm{ord},2} = \{o_0, \dots, o_{11}\}$ merging $\{q_4, q_5\} \mapsto o_{11}$, $\{q_6, q_{11}, q_{13}\} \mapsto o_2$, $\{q_7, q_{12}\} \mapsto o_4$, $\{q_8, q_9, q_{10}, q_{15}, q_{16}, q_{17}, q_{19}, q_{20}, q_{21}, q_{27}\} \mapsto o_5$, $\{q_{26}, q_{31}\} \mapsto o_9$, and $\{q_{22}, q_{23}, q_{24}, q_{25}, q_{28}, q_{29}, q_{30}, q_{32}, q_{33}, \infty_{\mathrm{HN}}\} \mapsto o_6$ (keeping $q_0 \mapsto o_0$, $q_1 \mapsto o_1$, $q_2 \mapsto o_3$, $q_3 \mapsto o_8$, $q_{14} \mapsto o_7$, $q_{18} \mapsto o_{10}$), and define the $3$-state quotient $\pi_3 \colon Q_{\mathrm{HN}} \to \{r_0, r_{\ge 1}, r_\bot\}$ mapping $q_0 \mapsto r_0$, $\{q_1, \dots, q_5\} \mapsto r_{\ge 1}$, and $\{q_6, \dots, \infty_{\mathrm{HN}}\} \mapsto r_\bot$ (with $r_0 \odot r_0 = r_0 \odot r_{\ge 1} = r_{\ge 1}$ and $x \odot y = r_\bot$ otherwise). Finite evaluation over $Q_{\mathrm{HN}}^2$ confirms that $\pi_2$ and $\pi_3$ are $S$-algebra homomorphisms deciding $\{\operatorname{ord} = 2\} = \{o_2, o_4, o_5, o_7, o_{10}\}$, $\{\operatorname{ord} \ge 2\} = Q_{\mathrm{ord},2} \setminus \{o_6, o_9\}$, and $\{\operatorname{ord} = 3\} = \{r_0, r_{\ge 1}\}$. Conversely, explicit closed witness terms inhabit all $35$ states of $Q_{\mathrm{HN}}$, all $12$ states of $Q_{\mathrm{ord},2}$, and all $3$ states of $Q_{\mathrm{ord},3}$ ($S, S S, S S S$); finite context families ($18$ closed contexts for $\{\operatorname{ord} = 0\}$, $13$ for $\{\operatorname{ord} = 1\}$, $6$ for $\{\operatorname{ord} = 2\}$, $8$ for $\{\operatorname{ord} \ge 2\}$, and $\{\square, \square S\}$ for $\{\operatorname{ord} = 3\}$) separate every distinct pair of states, forcing $|Q| \ge 35$, $|Q| \ge 12$, and $|Q| \ge 3$ on any recognizing deterministic bottom-up tree automaton by context congruence and the pigeonhole principle.
 $\square$

*Remark 6.26 (Minimal order-$2$ and order-$1$ witnesses in Barendregt et al. [4]).* 
In the informal overview of Section 5.5 in [4, p. 90], $S S S$ is momentarily cited as having order $1$, whereas in Appendix A.3, Example 41(ii) [4, p. 102] of the same work, the two-step reduction $S S S x y \to_S (S x)(S x) y \to_S (x y)(S x y)$ reaches a variable-headed term of order $0$ and assigns $S S S$ order $2$. Theorem 6.25(ii) reconciles the two passages: $A \equiv S S S$ ($\llbracket A \rrbracket_{\mathrm{HN}} = q_6$) is the unique minimal closed $S$-term of order $2$ ($3$ leaves), whereas no closed $S$-term of at most $4$ leaves has order $1$, the unique minimal closed order-$1$ combinator being the $5$-leaf normal form $S(S S S)S$ ($\llbracket S(S S S)S \rrbracket_{\mathrm{HN}} = q_{26}$, for which $S(S S S)S \in \mathrm{HNF}$ while $S(S S S)S x$ is already in normal form and cannot reduce to any $S A_1 A_2$).

## 7. Translation into the $\lambda\mathrm{I}$-Calculus: Order Preservation, Normalization Divergences, Hereditary Saturation, and Equational Non-Axiomatizability

The classical correspondence between combinatory logic and the untyped $\lambda$-calculus embeds combinators homomorphically into $\lambda$-terms by mapping binary application to application, variables to themselves, and each primitive combinator to its defining $\lambda$-abstraction [20, 1, 36]. On the pure-$S$ subsystem $\mathrm{CL}(S)$, this canonical translation $(-)_\lambda$ assigns to $S$ the closed three-argument abstraction

$$
(S)_\lambda \;\equiv\; \lambda x y z.\, (x z)(y z). \tag{7.1}
$$

Because each of the three bound variables $x, y, z$ occurs free in the body $(x z)(y z)$, the translation $(M)_\lambda$ of every open or closed pure-$S$ term $M \in \mathcal{T}_S(\mathcal{V})$ belongs to Alonzo Church's $\lambda\mathrm{I}$-calculus [16], in which $\beta$-contraction never erases an argument and weak normalization coincides with strong normalization. Even within this non-erasing fragment, however, combinatory reduction and $\lambda\beta$-reduction diverge in subtle ways: whereas any two-argument pure-$S$ term $S P Q$ with $P, Q \in \mathrm{NF}$ is already a normal form of $\mathrm{CL}(S)$, its translation $(S P Q)_\lambda$ reduces in two weak-head $\beta$-steps to $\lambda z.\, ((P)_\lambda z)((Q)_\lambda z)$, exposing the application $(P z)(Q z)$ to full $\beta$-reduction underneath the $\lambda z$-binder. In Chapter 5 of [4], Barendregt, Endrullis, Klop, and Waldmann examined this discrepancy in detail, posing Question 32 on equational axiomatizability and Question 34 on the $\lambda\beta$-normalizing closed pure-$S$ terms alongside Conjectures 40, 42, and 43 [4, pp. 94–96, 98–102]. In Subsection 7.1 we establish constructive weak-head standardization and conservation on $\lambda\mathrm{I}$ and resolve Conjecture 40 in the affirmative across full combinatory logic $\mathrm{CL}(\{S, K, I\})$ and $\mathrm{CL}(S)$. In Subsection 7.2 we determine the minimal closed pure-$S$ combinators whose $\lambda$-translations diverge, refute Conjectures 42 and 43 simultaneously at $14$ leaves ($15$ leaves in normal form), and prove an exact pure-$\mathrm{CL}(S)$ hereditary saturation characterization of $\lambda\beta$-normalization. The remaining subsections then analyze the Myhill–Nerode congruence geometry of Question 34 and establish the equational non-axiomatizability of $\lambda\beta$-equality over $\mathrm{CL}(S)$.

### 7.1. Constructive $\lambda\mathrm{I}$ Standardization, Conservation, and Affirmative Resolution of Conjecture 40

Because Conjecture 40 of Barendregt, Endrullis, Klop, and Waldmann [4, p. 102] concerns functional order across general combinatory logic as well as its specialization to $\mathrm{CL}(S)$, we formulate the combinatory translation and the two notions of functional order simultaneously over the full basis $\{S, K, I\}$ and over the pure-$S$ basis.

**Definition 7.1 (Untyped $\lambda$-terms, the $\lambda\mathrm{I}$-fragment, combinatory translations, and functional order).** 
Let $\mathcal{V} = \{x_0, x_1, x_2, \dots\}$ be the countably infinite set of variables fixed in Definition 2.1.

- (i) *Untyped $\lambda$-terms and $\lambda\mathrm{I}$-calculus:* Let $\Lambda$ denote the set of untyped $\lambda$-terms over $\mathcal{V}$ modulo $\alpha$-equivalence, generated by $P, Q ::= x \mid (P\,Q) \mid (\lambda x.\, P)$ ($x \in \mathcal{V}$), with free-variable set $\mathrm{FV}(P) \subset \mathcal{V}$ and capture-avoiding substitution $P[x := Q]$ (represented concretely in our constructive formalization via locally nameless de Bruijn indices for bound variables and $\mathcal{V}$ for free variables). *One-step $\beta$-reduction* $\to_\beta$ is the full contextual closure (under left application, right application, and $\lambda$-abstraction) of $(\lambda x.\, P)\,Q \to_\beta P[x := Q]$, with transitive closure $\to_\beta^+$, reflexive-transitive closure $\to_\beta^*$, and $\beta$-convertibility $=_\beta$. *Weak-head $\beta$-reduction* $\to_{\mathrm{wh}}$ restricts contraction to the top of the left application spine outside $\lambda$-abstractions: $(\lambda x.\, P)\,Q \to_{\mathrm{wh}} P[x := Q]$, and $P Q \to_{\mathrm{wh}} P' Q$ whenever $P \to_{\mathrm{wh}} P'$. A term $P \in \Lambda$ is in *$\beta$-normal form* ($P \in \mathrm{NF}_\beta$) if there is no $P'$ with $P \to_\beta P'$, *weakly $\beta$-normalizing* ($P \in \mathrm{WN}_\beta$) if $P \to_\beta^* N$ for some $N \in \mathrm{NF}_\beta$, and *strongly $\beta$-normalizing* ($P \in \mathrm{SN}_\beta$) if $P$ is constructively well-founded (accessible) under $\to_\beta$. Following Church [16], the *$\lambda\mathrm{I}$-fragment* $\Lambda_{\mathrm{I}} \subset \Lambda$ is generated inductively by $x \in \Lambda_{\mathrm{I}}$ ($x \in \mathcal{V}$), $P Q \in \Lambda_{\mathrm{I}}$ whenever $P, Q \in \Lambda_{\mathrm{I}}$, and $\lambda x.\, P \in \Lambda_{\mathrm{I}}$ whenever $P \in \Lambda_{\mathrm{I}}$ and $x \in \mathrm{FV}(P)$.
- (ii) *Full combinatory logic and canonical translation:* Let $\mathrm{Ter}(\mathrm{CL}(\{S, K, I\}))$ denote the set of open combinatory terms generated by $\{S, K, I\} \cup \mathcal{V}$ under binary application, equipped with one-step combinatory reduction $\to_{\mathrm{CL}}$ generated contextually by

$$
S X Y Z \;\to_{\mathrm{CL}}\; (X Z)(Y Z), \qquad K X Y \;\to_{\mathrm{CL}}\; X, \qquad I X \;\to_{\mathrm{CL}}\; X, \tag{7.2}
$$

and reflexive-transitive closure $\to_{\mathrm{CL}}^*$. Note that $\mathcal{T}_S(\mathcal{V}) \subset \mathrm{Ter}(\mathrm{CL}(\{S, K, I\}))$ embeds conservatively: for all $M, N \in \mathcal{T}_S(\mathcal{V})$, one has $M \to_{\mathrm{CL}}^* N$ if and only if $M \to_S^* N$. Define the sets of *partial combinator applications* in $\mathrm{CL}(\{S, K, I\})$ and $\mathrm{CL}(S)$ by

$$
\begin{aligned}
  \mathcal{P}_{\mathrm{CL}} &\;:=\; \{I, K, S\} \;\cup\; \{K A, S A : A \in \mathrm{Ter}(\mathrm{CL}(\{S, K, I\}))\} \\
  &\qquad\qquad\qquad \;\cup\; \{S A B : A, B \in \mathrm{Ter}(\mathrm{CL}(\{S, K, I\}))\}, \\
  \mathcal{P}_S &\;:=\; \mathcal{P}_{\mathrm{CL}} \cap \mathcal{T}_S(\mathcal{V}) \;=\; \{S\} \;\cup\; \{S A : A \in \mathcal{T}_S(\mathcal{V})\} \;\cup\; \{S A B : A, B \in \mathcal{T}_S(\mathcal{V})\}.
\end{aligned} \tag{7.3}
$$

The canonical homomorphic translation $(-)_\lambda \colon \mathrm{Ter}(\mathrm{CL}(\{S, K, I\})) \to \Lambda$ is defined recursively by $(x)_\lambda \equiv x$ for $x \in \mathcal{V}$, $(M N)_\lambda \equiv (M)_\lambda\,(N)_\lambda$, $(S)_\lambda \equiv \lambda x y z.\, (x z)(y z)$, $(K)_\lambda \equiv \lambda x y.\, x$, and $(I)_\lambda \equiv \lambda x.\, x$. Observe that $\mathrm{FV}((M)_\lambda) = \mathrm{FV}(M)$ for all $M \in \mathrm{Ter}(\mathrm{CL}(\{S, K, I\}))$, and $(M)_\lambda \in \Lambda_{\mathrm{I}}$ for every $M \in \mathcal{T}_S(\mathcal{V})$.
- (iii) *Functional order in $\Lambda$ and $\mathrm{CL}$ [4, Definitions 35 and 37, pp. 98–99]:* For $P \in \Lambda$, the *$\lambda$-order* $\operatorname{ord}_\lambda(P) \in \mathbb{N} \cup \{\infty\}$ is defined inductively on $n \in \mathbb{N}$ by setting $\operatorname{ord}_\lambda(P) = 0$ if there is no $Q \in \Lambda$ with $P \to_\beta^* \lambda x.\, Q$; $\operatorname{ord}_\lambda(P) = n + 1$ if $P \to_\beta^* \lambda x.\, Q$ for some $Q \in \Lambda$ with $\operatorname{ord}_\lambda(Q) = n$; and $\operatorname{ord}_\lambda(P) = \infty$ if $\operatorname{ord}_\lambda(P) \ne n$ for every $n \in \mathbb{N}$. Following Curry and Feys [20] and [4, Definition 37], a combinatory term $M \in \mathrm{Ter}(\mathrm{CL}(\{S, K, I\}))$ *never consumes fresh arguments* if for every $r \ge 1$, every tuple of distinct variables $y_1, \dots, y_r \in \mathcal{V} \setminus \mathrm{FV}(M)$, and every reduction $M y_1 \cdots y_r \to_{\mathrm{CL}}^* N$, there exists $M' \in \mathrm{Ter}(\mathrm{CL}(\{S, K, I\}))$ such that $N \equiv M' y_1 \cdots y_r$ and $M \to_{\mathrm{CL}}^* M'$. The *combinatory order* $\operatorname{ord}_{\mathrm{CL}}(M) \in \mathbb{N} \cup \{\infty\}$ is then defined inductively on $n \in \mathbb{N}$ by setting $\operatorname{ord}_{\mathrm{CL}}(M) = 0$ if $M$ never consumes fresh arguments; $\operatorname{ord}_{\mathrm{CL}}(M) = n + 1$ if $M$ does not have order $0$ and $\operatorname{ord}_{\mathrm{CL}}(M z) = n$ for a fresh variable $z \in \mathcal{V} \setminus \mathrm{FV}(M)$; and $\operatorname{ord}_{\mathrm{CL}}(M) = \infty$ if $\operatorname{ord}_{\mathrm{CL}}(M) \ne n$ for every $n \in \mathbb{N}$.

Every combinatory root contraction in (7.2) is simulated in $\Lambda$ by weak-head $\beta$-steps: $((S)_\lambda X Y) Z \to_{\mathrm{wh}}^3 (X Z)(Y Z)$, $((K)_\lambda X) Y \to_{\mathrm{wh}}^2 X$, and $(I)_\lambda X \to_{\mathrm{wh}} X$. Lifting across application contexts shows that $M \to_{\mathrm{CL}} N$ implies $(M)_\lambda \to_\beta^+ (N)_\lambda$, and consequently $M \to_{\mathrm{CL}}^* N$ implies $(M)_\lambda \to_\beta^* (N)_\lambda$. Likewise, Takahashi's parallel $\beta$-reduction $P \Rightarrow_\beta Q$ and complete development map $\Delta_\beta$ [59] establish the Church–Rosser property for $\to_\beta^*$ constructively: co-initial reductions $P \to_\beta^* Q_1$ and $P \to_\beta^* Q_2$ always admit a common reduct $R$ with $Q_1 \to_\beta^* R$ and $Q_2 \to_\beta^* R$. In particular, $\beta$-normal forms are unique, and $\operatorname{ord}_\lambda(P)$ is invariant under $=_\beta$ and uniquely determined whenever finite: if $P \to_\beta^* \lambda x.\, Q_1$ and $P \to_\beta^* \lambda x.\, Q_2$, confluence yields a common reduct $\lambda x.\, R$ with $Q_1 \to_\beta^* R$ and $Q_2 \to_\beta^* R$, whence $Q_1 =_\beta Q_2$.

To pull $\lambda$-abstractions and normalization properties back across $(-)_\lambda$ constructively without invoking classical choice or König's lemma, we next prove weak-head standardization for $\Lambda$ together with Church's conservation theorem on $\Lambda_{\mathrm{I}}$.

**Lemma 7.2 (Weak-head standardization and Church's conservation theorem on $\Lambda_{\mathrm{I}}$).** 
Let $P, Q \in \Lambda$ be untyped $\lambda$-terms.

- (i) *Weak-head standardization:* If $P \to_\beta^* \lambda x.\, Q$, there exists $B \in \Lambda$ such that $P \to_{\mathrm{wh}}^* \lambda x.\, B$ and $B \to_\beta^* Q$. Likewise, if $P \to_\beta^* y R_1 \cdots R_m$ for a variable $y$ (bound or free) and $m \ge 0$, there exist $R_1^0, \dots, R_m^0 \in \Lambda$ such that $P \to_{\mathrm{wh}}^* y R_1^0 \cdots R_m^0$ and $R_i^0 \to_\beta^* R_i$ for each $1 \le i \le m$.
- (ii) *Spine head-expansion and $\Lambda_{\mathrm{I}}$ pullback:* For all $B, A, C_1, \dots, C_m \in \Lambda$ ($m \ge 0$), if $B \in \mathrm{SN}_\beta$, $A \in \mathrm{SN}_\beta$, $C_1, \dots, C_m \in \mathrm{SN}_\beta$, and $(B[x := A])\,C_1 \cdots C_m \in \mathrm{SN}_\beta$, then $((\lambda x.\, B)\,A)\,C_1 \cdots C_m \in \mathrm{SN}_\beta$. Furthermore, $\Lambda_{\mathrm{I}}$ is closed under $\to_\beta$, and whenever $P \in \Lambda_{\mathrm{I}}$ satisfies $P \to_{\mathrm{wh}}^* Q$ with $Q \in \mathrm{SN}_\beta$, one has $P \in \mathrm{SN}_\beta$.
- (iii) *Church's conservation theorem and fresh-variable application [16, 1]:* For every $P \in \Lambda_{\mathrm{I}}$, one has $P \in \mathrm{WN}_\beta$ if and only if $P \in \mathrm{SN}_\beta$. Moreover, for every $P \in \Lambda$ and every variable $z \in \mathcal{V}$, if $P \in \mathrm{WN}_\beta$, then $P z \in \mathrm{WN}_\beta$; hence on $\Lambda_{\mathrm{I}}$, if $P \in \mathrm{SN}_\beta$, then $P z \in \mathrm{SN}_\beta$.

*Proof.* 
For (i), recall that parallel $\beta$-reduction $M \Rightarrow_\beta N$ is generated inductively by $y \Rightarrow_\beta y$ on variables, $A B \Rightarrow_\beta A' B'$ when $A \Rightarrow_\beta A'$ and $B \Rightarrow_\beta B'$, $\lambda x.\, B \Rightarrow_\beta \lambda x.\, B'$ when $B \Rightarrow_\beta B'$, and $(\lambda x.\, U)\,W \Rightarrow_\beta U'[x := W']$ when $U \Rightarrow_\beta U'$ and $W \Rightarrow_\beta W'$, with $\Rightarrow_\beta^*$ equal to $\to_\beta^*$. Observe first that $\to_{\mathrm{wh}}^*$ is preserved under outer substitution: $A \to_{\mathrm{wh}}^* B$ implies $A[z := S] \to_{\mathrm{wh}}^* B[z := S]$. Structural induction on $M \Rightarrow_\beta N$ establishes three head-shape factorizations:

- (a) If $N \equiv y$ is a variable, then $M \to_{\mathrm{wh}}^* y$. In the sole non-trivial clause $(\lambda x.\, U)\,W \Rightarrow_\beta U'[x := W'] \equiv y$, either $U' \equiv y$ with $y \ne x$ (so $U \to_{\mathrm{wh}}^* y$ by the induction hypothesis and $(\lambda x.\, U)\,W \to_{\mathrm{wh}} U[x := W] \to_{\mathrm{wh}}^* y$) or $U' \equiv x$ and $W' \equiv y$ (so $U \to_{\mathrm{wh}}^* x$ and $W \to_{\mathrm{wh}}^* y$, whence $(\lambda x.\, U)\,W \to_{\mathrm{wh}} U[x := W] \to_{\mathrm{wh}}^* W \to_{\mathrm{wh}}^* y$).
- (b) If $N \equiv \lambda x.\, Q'$, there exists $B_0$ with $M \to_{\mathrm{wh}}^* \lambda x.\, B_0$ and $B_0 \Rightarrow_\beta Q'$. Under $(\lambda z.\, U)\,W \Rightarrow_\beta U'[z := W'] \equiv \lambda x.\, Q'$, either $U' \equiv \lambda x.\, U_1'$ with $U_1'[z := W'] \equiv Q'$ (giving $U \to_{\mathrm{wh}}^* \lambda x.\, U_0$ with $U_0 \Rightarrow_\beta U_1'$, so $(\lambda z.\, U)\,W \to_{\mathrm{wh}}^* \lambda x.\, U_0[z := W]$ and $U_0[z := W] \Rightarrow_\beta Q'$ by substitutivity of $\Rightarrow_\beta$) or $U' \equiv z$ and $W' \equiv \lambda x.\, Q'$ (giving $U \to_{\mathrm{wh}}^* z$ and $W \to_{\mathrm{wh}}^* \lambda x.\, B_0$ with $B_0 \Rightarrow_\beta Q'$, so $(\lambda z.\, U)\,W \to_{\mathrm{wh}} U[z := W] \to_{\mathrm{wh}}^* W \to_{\mathrm{wh}}^* \lambda x.\, B_0$).
- (c) If $N \equiv A' B'$, an identical split on $U'$ yields $A_0, B_0$ with $M \to_{\mathrm{wh}}^* A_0 B_0$, $A_0 \Rightarrow_\beta A'$, and $B_0 \Rightarrow_\beta B'$.

Using (b) and (c), induction on $M_1 \to_{\mathrm{wh}} M_2$ shows that whenever $M \Rightarrow_\beta M_1 \to_{\mathrm{wh}} M_2$, there exists $M_0$ with $M \to_{\mathrm{wh}}^* M_0 \Rightarrow_\beta M_2$: at a root step $M_1 \equiv (\lambda x.\, P')\,Q' \to_{\mathrm{wh}} P'[x := Q']$, applying (c) then (b) to $M \Rightarrow_\beta (\lambda x.\, P')\,Q'$ produces $M \to_{\mathrm{wh}}^* A_0 B_0 \to_{\mathrm{wh}}^* (\lambda x.\, P_0)\,B_0 \to_{\mathrm{wh}} P_0[x := B_0] \Rightarrow_\beta P'[x := Q']$; the left-application step follows immediately from (c). Iterating across $M_1 \to_{\mathrm{wh}}^* M_2$ postpones $\Rightarrow_\beta$ past $\to_{\mathrm{wh}}^*$, and induction along $P \Rightarrow_\beta^* N$ yields both the abstraction standardization claim (from (b)) and the binary-application standardization claim (from (c)), which extends by induction on $m$ from (a) to any variable-headed spine $y R_1 \cdots R_m$.

For (ii), let $S_0 \equiv (B[x := A])\,C_1 \cdots C_m$. We prove $((\lambda x.\, B)\,A)\,C_1 \cdots C_m \in \mathrm{SN}_\beta$ by nested well-founded induction on $B \in \mathrm{SN}_\beta$, $A \in \mathrm{SN}_\beta$, componentwise reduction on $(C_1, \dots, C_m) \in \mathrm{SN}_\beta^m$, and $S_0 \in \mathrm{SN}_\beta$. Because $(\lambda x.\, B)\,A$ is not an abstraction, any single step $((\lambda x.\, B)\,A)\,C_1 \cdots C_m \to_\beta Y$ arises in one of four ways: contracting $(\lambda x.\, B)\,A$ at the head yields $Y \equiv S_0 \in \mathrm{SN}_\beta$ directly; stepping $B \to_\beta B'$ yields $S_0 \to_\beta (B'[x := A])\,C_1 \cdots C_m$, which is covered by the induction hypothesis on $B'$; stepping $A \to_\beta A'$ yields $S_0 \to_\beta^* (B[x := A'])\,C_1 \cdots C_m$, which lies in $\mathrm{SN}_\beta$ as a reduct of $S_0$ and is covered by the induction hypothesis on $A'$; and stepping $C_i \to_\beta C_i'$ steps $S_0$ in one step, covered by the tuple hypothesis on $(C_1, \dots, C_m)$. Next, induction on $P \to_\beta P'$ shows simultaneously that $P \in \Lambda_{\mathrm{I}}$ implies $P' \in \Lambda_{\mathrm{I}}$ and $\mathrm{FV}(P) \subseteq \mathrm{FV}(P')$: at $(\lambda x.\, B)\,A \to_\beta B[x := A]$, the hypothesis $\lambda x.\, B \in \Lambda_{\mathrm{I}}$ guarantees $x \in \mathrm{FV}(B)$, so $A$ occurs at least once in $B[x := A]$, preserving both $\Lambda_{\mathrm{I}}$-membership and all free variables of $A$ and $B \setminus \{x\}$. Now suppose $P \in \Lambda_{\mathrm{I}}$ and $P \to_{\mathrm{wh}} Q \in \mathrm{SN}_\beta$. Writing $P \equiv ((\lambda x.\, B)\,A)\,C_1 \cdots C_m$ and $Q \equiv (B[x := A])\,C_1 \cdots C_m$, subterm projection from $Q \in \mathrm{SN}_\beta$ gives $B[x := A] \in \mathrm{SN}_\beta$ and $C_1, \dots, C_m \in \mathrm{SN}_\beta$. Since every step $B \to_\beta B'$ induces $B[x := A] \to_\beta B'[x := A]$, we obtain $B \in \mathrm{SN}_\beta$; and because $\lambda x.\, B \in \Lambda_{\mathrm{I}}$ forces $x \in \mathrm{FV}(B)$, every step $A \to_\beta A'$ induces at least one step $B[x := A] \to_\beta^+ B[x := A']$, forcing $A \in \mathrm{SN}_\beta$ as well. The head-expansion property then yields $P \in \mathrm{SN}_\beta$, and induction along $P \to_{\mathrm{wh}}^* Q$ completes (ii).

For (iii), define the syntactic size $\|y\|_\lambda = 1$ on variables, $\|\lambda x.\, B\|_\lambda = 1 + \|B\|_\lambda$, and $\|A B\|_\lambda = 1 + \|A\|_\lambda + \|B\|_\lambda$. Given $P \in \Lambda_{\mathrm{I}}$ with $P \to_\beta^* N \in \mathrm{NF}_\beta$, we prove $P \in \mathrm{SN}_\beta$ by strong induction on $\|N\|_\lambda$. Because $N \in \mathrm{NF}_\beta$ contains no head $\beta$-redex, spine decomposition places $N$ into one of two shapes. If $N \equiv \lambda x.\, N_0$, then $N_0 \in \mathrm{NF}_\beta$ and $\|N_0\|_\lambda < \|N\|_\lambda$; part (i) gives $P \to_{\mathrm{wh}}^* \lambda x.\, B_0$ with $B_0 \to_\beta^* N_0$, part (ii) gives $\lambda x.\, B_0 \in \Lambda_{\mathrm{I}}$ and hence $B_0 \in \Lambda_{\mathrm{I}}$, the induction hypothesis gives $B_0 \in \mathrm{SN}_\beta$ (so $\lambda x.\, B_0 \in \mathrm{SN}_\beta$), and weak-head pullback from (ii) yields $P \in \mathrm{SN}_\beta$. Otherwise $N \equiv y N_1 \cdots N_m$ ($m \ge 0$) for a bound or free variable $y$, where each $N_i \in \mathrm{NF}_\beta$ satisfies $\|N_i\|_\lambda < \|N\|_\lambda$; part (i) gives $P \to_{\mathrm{wh}}^* y R_1^0 \cdots R_m^0 \in \Lambda_{\mathrm{I}}$ with $R_i^0 \to_\beta^* N_i$, the induction hypothesis gives $R_i^0 \in \mathrm{SN}_\beta$ for every $i$, whence $y R_1^0 \cdots R_m^0 \in \mathrm{SN}_\beta$ (as $y$ is irreducible and not an abstraction), and weak-head pullback again yields $P \in \mathrm{SN}_\beta$. Conversely, $P \in \mathrm{SN}_\beta$ implies $P \in \mathrm{WN}_\beta$ constructively on all of $\Lambda$ by iterating the total leftmost-outermost step detector until it returns normal. Finally, if $P \to_\beta^* N \in \mathrm{NF}_\beta$, then $P z \to_\beta^* N z$: when $N \equiv \lambda x.\, B$ ($B \in \mathrm{NF}_\beta$), one further step gives $N z \to_\beta B[x := z] \in \mathrm{NF}_\beta$ because substituting a free variable $z$ for $x$ never converts a non-abstraction into a $\lambda$-abstraction; when $N$ is not an abstraction, $N z \in \mathrm{NF}_\beta$ directly.
 $\square$

We now establish Conjecture 40 of Barendregt, Endrullis, Klop, and Waldmann [4, p. 102] in full generality by characterizing order $0$ through $\mathcal{P}_{\mathrm{CL}}$ and bridging partial combinator reducts with $\lambda$-abstractions via weak-head standardization.

**Theorem 7.3 (Affirmative resolution of Conjecture 40).** 
The canonical translation $(-)_\lambda \colon \mathrm{Ter}(\mathrm{CL}(\{S, K, I\})) \to \Lambda$ preserves functional order exactly:

- (i) *Partial-combinator and abstraction bridge:* For every $M \in \mathrm{Ter}(\mathrm{CL}(\{S, K, I\}))$, there exists $H \in \mathcal{P}_{\mathrm{CL}}$ with $M \to_{\mathrm{CL}}^* H$ if and only if there exists $Q \in \Lambda$ with $(M)_\lambda \to_\beta^* \lambda x.\, Q$. Moreover, $M$ never consumes fresh arguments ($\operatorname{ord}_{\mathrm{CL}}(M) = 0$) if and only if no reduct of $M$ belongs to $\mathcal{P}_{\mathrm{CL}}$.
- (ii) *Exact order preservation on $\mathrm{CL}(\{S, K, I\})$ [4, Conjecture 40, p. 102]:* For every combinatory term $M \in \mathrm{Ter}(\mathrm{CL}(\{S, K, I\}))$ and every $n \in \mathbb{N}$,

$$
\operatorname{ord}_{\mathrm{CL}}(M) = n \;\iff\; \operatorname{ord}_\lambda\bigl((M)_\lambda\bigr) = n,
$$

and consequently $\operatorname{ord}_{\mathrm{CL}}(M) = \infty$ if and only if $\operatorname{ord}_\lambda((M)_\lambda) = \infty$.
- (iii) *Specialization to $\mathrm{CL}(S)$ and order-$3$ ceiling:* For every open or closed pure-$S$ term $M \in \mathcal{T}_S(\mathcal{V})$ and every $n \in \mathbb{N}$, one has $\operatorname{ord}_{\mathrm{CL}}(M) = n$ if and only if $\operatorname{ord}_\lambda((M)_\lambda) = n$; furthermore, $\operatorname{ord}_{\mathrm{CL}}(M z_1 z_2 z_3) = \operatorname{ord}_\lambda((M z_1 z_2 z_3)_\lambda) = 0$ for all $z_1, z_2, z_3 \in \mathcal{V}$, so $\operatorname{ord}_{\mathrm{CL}}(M) = \operatorname{ord}_\lambda((M)_\lambda) \in \{0, 1, 2, 3\}$.

*Proof.* 
For (i), we first prove that $M$ never consumes fresh arguments if and only if no $H \in \mathcal{P}_{\mathrm{CL}}$ satisfies $M \to_{\mathrm{CL}}^* H$. Suppose $M \to_{\mathrm{CL}}^* H \in \mathcal{P}_{\mathrm{CL}}$, and choose distinct fresh variables $y_1, y_2, y_3 \in \mathcal{V} \setminus \mathrm{FV}(M)$; since $\to_{\mathrm{CL}}^*$ creates no new free variables, $y_1, y_2, y_3 \notin \mathrm{FV}(H)$. Direct inspection of the six cases of (7.3) refutes unconsumed-argument persistence in each case: $I y_1 \to_{\mathrm{CL}} y_1$ and $K y_1 y_2 \to_{\mathrm{CL}} y_1$ cannot have the form $M' y_1$ or $M' y_1 y_2$; $(K A) y_1 \to_{\mathrm{CL}} A$ satisfies $y_1 \notin \mathrm{FV}(A)$, whereas $y_1 \in \mathrm{FV}(M' y_1)$; and $S y_1 y_2 y_3 \to_{\mathrm{CL}} (y_1 y_3)(y_2 y_3)$, $(S A) y_1 y_2 \to_{\mathrm{CL}} (A y_2)(y_1 y_2)$, and $(S A B) y_1 \to_{\mathrm{CL}} (A y_1)(B y_1)$ all terminate in a compound right-hand factor $(-\,y_r) \not\equiv y_r$. Conversely, assume no reduct of $M$ belongs to $\mathcal{P}_{\mathrm{CL}}$. By induction on $r \ge 0$, we show that for any variables $y_1, \dots, y_r \in \mathcal{V}$, every reduction $M y_1 \cdots y_r \to_{\mathrm{CL}}^* N$ has the form $N \equiv M' y_1 \cdots y_r$ with $M \to_{\mathrm{CL}}^* M'$. The base $r = 0$ is immediate. For $r = r_0 + 1$, put $F \equiv M y_1 \cdots y_{r_0}$. By the induction hypothesis on $r_0$, the term $F$ cannot reduce to $I$, to any $K P$, or to any $S P Q$: for example, if $F \to_{\mathrm{CL}}^* S P Q$, then $S P Q \equiv M' y_1 \cdots y_{r_0}$ with $M \to_{\mathrm{CL}}^* M'$, which forces $M' \equiv S P Q \in \mathcal{P}_{\mathrm{CL}}$ ($r_0 = 0$), $M' \equiv S P \in \mathcal{P}_{\mathrm{CL}}$ ($r_0 = 1$), or $M' \equiv S \in \mathcal{P}_{\mathrm{CL}}$ ($r_0 = 2$), while $r_0 \ge 3$ is impossible since $\operatorname{ls}(S P Q) = 2$; the cases $F \to_{\mathrm{CL}}^* I$ and $F \to_{\mathrm{CL}}^* K P$ are excluded analogously. Hence no root contraction can occur along any reduction of $F y_{r_0+1}$, so every reduct has the form $F' y_{r_0+1}$ with $F \to_{\mathrm{CL}}^* F'$, and applying the induction hypothesis to $F \to_{\mathrm{CL}}^* F'$ completes the induction.

Next we prove that $M \to_{\mathrm{CL}}^* H$ for some $H \in \mathcal{P}_{\mathrm{CL}}$ if and only if $(M)_\lambda \to_\beta^* \lambda x.\, Q$ for some $Q \in \Lambda$. In the forward direction, $M \to_{\mathrm{CL}}^* H$ gives $(M)_\lambda \to_\beta^* (H)_\lambda$, and for every $H \in \mathcal{P}_{\mathrm{CL}}$ the closed-bound-variable term $(H)_\lambda$ reaches an abstraction in at most two weak-head steps: $(I)_\lambda, (K)_\lambda, (S)_\lambda$ are already abstractions, $(K A)_\lambda \to_{\mathrm{wh}} \lambda y.\, (A)_\lambda$, $(S A)_\lambda \to_{\mathrm{wh}} \lambda y z.\, ((A)_\lambda z)(y z)$, and $(S A B)_\lambda \to_{\mathrm{wh}}^2 \lambda z.\, ((A)_\lambda z)((B)_\lambda z)$. Conversely, suppose $(M)_\lambda \to_\beta^* \lambda x.\, Q$. By Lemma 7.2(i), $(M)_\lambda \to_{\mathrm{wh}}^k \lambda x.\, B_0$ for some step count $k \ge 0$. Notice that $\to_{\mathrm{wh}}$ is deterministic and stops on abstractions. We proceed by strong induction on $k$, decomposing $M$ along its left combinatory spine into five mutually exclusive cases:

1. If $M \equiv v C_1 \cdots C_m$ ($v \in \mathcal{V}$), then $(M)_\lambda \equiv v (C_1)_\lambda \cdots (C_m)_\lambda$ is neither an abstraction nor weak-head reducible, which is impossible.
2. If $M \in \mathcal{P}_{\mathrm{CL}}$, then $M \to_{\mathrm{CL}}^0 M \in \mathcal{P}_{\mathrm{CL}}$ immediately.
3. If $M \equiv (I X) C_1 \cdots C_m$, then $(M)_\lambda$ is an application (so $k \ge 1$) whose unique first weak-head step yields $(X C_1 \cdots C_m)_\lambda \to_{\mathrm{wh}}^{k-1} \lambda x.\, B_0$; the induction hypothesis at $k - 1 < k$ produces $X C_1 \cdots C_m \to_{\mathrm{CL}}^* H \in \mathcal{P}_{\mathrm{CL}}$, prepended by $M \to_{\mathrm{CL}} X C_1 \cdots C_m$.
4. If $M \equiv (K X Y) C_1 \cdots C_m$, then $(M)_\lambda$ executes two forced weak-head steps through the non-abstraction $((\lambda y.\, (X)_\lambda)\,(Y)_\lambda)\,(C_1)_\lambda \cdots (C_m)_\lambda$ (so $k \ge 2$) to $(X C_1 \cdots C_m)_\lambda$ in $k - 2 < k$ remaining steps, lifting $M \to_{\mathrm{CL}} X C_1 \cdots C_m$.
5. If $M \equiv (S X Y Z) C_1 \cdots C_m$, then $(M)_\lambda$ executes three forced weak-head steps through two intermediate non-abstractions (so $k \ge 3$) to $(((X Z)(Y Z)) C_1 \cdots C_m)_\lambda$ in $k - 3 < k$ remaining steps, lifting $M \to_{\mathrm{CL}} ((X Z)(Y Z)) C_1 \cdots C_m$.

For (ii), observe first the fresh-variable step-down property of $\operatorname{ord}_\lambda$ ([4, Example 36(iv), p. 99]): whenever $P \to_\beta^* \lambda x.\, Q$ and $z \in \mathcal{V} \setminus \mathrm{FV}(P)$, one has $\operatorname{ord}_\lambda(P) = n + 1$ if and only if $\operatorname{ord}_\lambda(P z) = n$. Indeed, $z \notin \mathrm{FV}(P)$ implies $z \notin \mathrm{FV}(Q)$, and the syntactic variable-closing operation $\kappa_z^x$ replacing free $z$ by bound $x$ commutes with $\to_\beta^*$ and satisfies $\kappa_z^x(Q[x := z]) \equiv Q$. Induction on $n$ shows that $\operatorname{ord}_\lambda(Q) = n$ holds if and only if $\operatorname{ord}_\lambda(Q[x := z]) = n$: at $n = 0$, $Q \to_\beta^* \lambda y.\, R$ gives $Q[x := z] \to_\beta^* \lambda y.\, R[x := z]$, while $Q[x := z] \to_\beta^* \lambda y.\, R'$ applies $\kappa_z^x$ to yield $Q \to_\beta^* \lambda y.\, \kappa_z^x(R')$; at $n + 1$, applying $\kappa_z^x$ together with Church–Rosser confluence under $\lambda y$ transfers the inductive step. Because $P z \to_\beta^* (\lambda x.\, Q)\,z \to_\beta Q[x := z]$ gives $P z =_\beta Q[x := z]$ and $\operatorname{ord}_\lambda$ is $=_\beta$-invariant, $\operatorname{ord}_\lambda(P z) = n$ is equivalent to $\operatorname{ord}_\lambda(Q[x := z]) = n$, hence to $\operatorname{ord}_\lambda(Q) = n$, and therefore to $\operatorname{ord}_\lambda(P) = n + 1$.

We now prove $\operatorname{ord}_{\mathrm{CL}}(M) = n \iff \operatorname{ord}_\lambda((M)_\lambda) = n$ by induction on $n \in \mathbb{N}$ across all $M \in \mathrm{Ter}(\mathrm{CL}(\{S, K, I\}))$. For $n = 0$, part (i) equates $\operatorname{ord}_{\mathrm{CL}}(M) = 0$ with absence of any $H \in \mathcal{P}_{\mathrm{CL}}$ satisfying $M \to_{\mathrm{CL}}^* H$, and hence with absence of any abstraction reduct of $(M)_\lambda$, which is $\operatorname{ord}_\lambda((M)_\lambda) = 0$. For $n + 1$, pick any fresh $z \in \mathcal{V} \setminus \mathrm{FV}(M) = \mathcal{V} \setminus \mathrm{FV}((M)_\lambda)$. By part (i), $M$ reduces to an element of $\mathcal{P}_{\mathrm{CL}}$ if and only if $(M)_\lambda$ reduces to an abstraction; under this shared condition, the step-down law for $\operatorname{ord}_\lambda$ and the induction hypothesis on $M z$ yield

$$
\operatorname{ord}_{\mathrm{CL}}(M) = n + 1 \;\iff\; \operatorname{ord}_{\mathrm{CL}}(M z) = n \;\iff\; \operatorname{ord}_\lambda\bigl((M z)_\lambda\bigr) = n \;\iff\; \operatorname{ord}_\lambda\bigl((M)_\lambda\bigr) = n + 1.
$$

Negating over all $n \in \mathbb{N}$ shows that $\operatorname{ord}_{\mathrm{CL}}(M) = \infty$ holds if and only if $\operatorname{ord}_\lambda((M)_\lambda) = \infty$.

For (iii), conservative embedding of $\mathcal{T}_S(\mathcal{V})$ into $\mathrm{Ter}(\mathrm{CL}(\{S, K, I\}))$ identifies $\to_{\mathrm{CL}}^*$ with $\to_S^*$ and $\mathcal{P}_{\mathrm{CL}} \cap \mathcal{T}_S(\mathcal{V})$ with $\mathcal{P}_S$. By the Visser–van Oostrom invariant $\mathcal{W}_3$ of Proposition 2.4(iii), for all $M \in \mathcal{T}_S(\mathcal{V})$ and $z_1, z_2, z_3 \in \mathcal{V}$, the term $M z_1 z_2 z_3$ belongs to $\mathcal{W}_3$, which is closed under $\to_S^*$ and disjoint from $\mathcal{P}_S$ (as $S \notin \mathcal{W}_1$). Part (i) therefore gives $\operatorname{ord}_{\mathrm{CL}}(M z_1 z_2 z_3) = \operatorname{ord}_\lambda((M z_1 z_2 z_3)_\lambda) = 0$, bounding the chain of fresh-variable applications at depth at most $3$ and ensuring $\operatorname{ord}_{\mathrm{CL}}(M) = \operatorname{ord}_\lambda((M)_\lambda) \in \{0, 1, 2, 3\}$.
 $\square$

### 7.2. Minimal $\lambda\beta$-Diverging Combinators, Simultaneous Refutation of Conjectures 42 and 43, and Hereditary Saturation

While Theorem 7.3 shows that $(-)_\lambda$ preserves functional order on $\mathrm{CL}(S)$, normalization behaves quite differently. Because $M \to_S N$ implies $(M)_\lambda \to_\beta^+ (N)_\lambda$, strong normalization pulls back from $\Lambda_{\mathrm{I}}$ to $\mathrm{CL}(S)$: $(M)_\lambda \in \mathrm{SN}_\beta$ always implies $M \in \mathrm{SN}$. In the opposite direction, Barendregt, Endrullis, Klop, and Waldmann observed in Example 33 of [4, p. 95] (following Waldmann [66]) that the $13$-leaf closed normal form $W_{\mathrm{Wal}} \equiv S V V$, built from $T \equiv S S$, $Z \equiv S T T$, and $V \equiv S Z$, satisfies $(W_{\mathrm{Wal}})_\lambda \notin \mathrm{WN}_\beta$, and posed Question 34 asking for a characterization of $\{M \in \mathcal{T}_S : (M)_\lambda \in \mathrm{WN}_\beta\}$. Our next result determines the exact minimum leaf sizes at which closed normalizing pure-$S$ combinators ($9$ leaves) and closed pure-$S$ normal forms ($10$ leaves) diverge under $\lambda\beta$-reduction.

**Proposition 7.4 (Minimal closed $\lambda\beta$-diverging pure-$S$ combinators).** 
Let $T \equiv S S$, $A \equiv S S S$, $Z \equiv S T T$, and $V \equiv S Z$, and define the closed pure-$S$ terms

$$
W_9 \;\equiv\; S\bigl(S(A A)\bigr)S, \qquad N_{10} \;\equiv\; S\bigl(S(S A A)\bigr)S, \qquad W_9^{\mathrm{nf}} \;\equiv\; S\bigl(S(S A (S A))\bigr)S, \qquad W_{\mathrm{Wal}} \;\equiv\; S V V.
$$

Then the following properties hold:

- (i) *Sizes and $\mathrm{CL}(S)$-normalization:* One has $|W_9| = 9$, $|N_{10}| = 10$, $|W_9^{\mathrm{nf}}| = 11$, and $|W_{\mathrm{Wal}}| = 13$. Each of $N_{10}$, $W_9^{\mathrm{nf}}$, and $W_{\mathrm{Wal}}$ lies in $\mathcal{T}_S \cap \mathrm{NF}$, whereas $W_9 \in \mathcal{T}_S \cap \mathrm{SN}$ reduces in a single deterministic step $W_9 \to_S W_9^{\mathrm{nf}}$ to its normal form $W_9^{\mathrm{nf}}$.
- (ii) *Divergence in $\lambda\beta$:* For every variable $z \in \mathcal{V}$ and every $U \in \{W_9, N_{10}, W_9^{\mathrm{nf}}, W_{\mathrm{Wal}}\}$, the open application $U z$ satisfies $U z \notin \mathrm{SN}$ in $\mathrm{CL}(S)$, and consequently $(U)_\lambda \notin \mathrm{SN}_\beta$ and $(U)_\lambda \notin \mathrm{WN}_\beta$.
- (iii) *Global minimality:* For every closed pure-$S$ term $M \in \mathcal{T}_S$ with $|M| \le 8$, one has $(M)_\lambda \in \mathrm{SN}_\beta$ if and only if $M \in \mathrm{SN}$; and for every closed pure-$S$ normal form $N \in \mathcal{T}_S \cap \mathrm{NF}$ with $|N| \le 9$, one has $(N)_\lambda \in \mathrm{SN}_\beta$.

*Proof.* 
For (i), counting $S$-leaves gives $|A| = 3$, $|A A| = 6$, $|W_9| = 1 + (1 + 6) + 1 = 9$, $|N_{10}| = 1 + (1 + 7) + 1 = 10$, $|W_9^{\mathrm{nf}}| = 1 + (1 + (4 + 4)) + 1 = 11$, and $|W_{\mathrm{Wal}}| = 1 + 6 + 6 = 13$. Every binary application node in $N_{10}$, $W_9^{\mathrm{nf}}$, and $W_{\mathrm{Wal}}$ has left-spine length $1$ or $2$, placing all three in $\mathrm{NF}$. In $W_9 \equiv S(S(A A))S$, the sole redex is $A A \equiv S S S A \to_S (S A)(S A) \equiv S A (S A) \in \mathrm{NF}$, so $W_9 \to_S W_9^{\mathrm{nf}} \in \mathrm{NF}$ and $W_9 \in \mathrm{SN}$.

For (ii), observe first a general subterm-spiral criterion in $\mathrm{CL}(S)$: if a sequence $(F_n)_{n \ge 0}$ in $\mathcal{T}_S(\mathcal{V})$ satisfies $F_n \to_S^+ C_n[F_{n+1}]$ for some one-hole context $C_n[\,]$ at every $n \ge 0$, then $F_0 \notin \mathrm{SN}$, because accessibility of $X \in \mathrm{SN}$ under $\to_S^+$ lifts across subterm contexts to well-foundedness of the relation $X \succ Y$ defined by the existence of $C[\,]$ with $X \to_S^+ C[Y]$. Moreover, whenever $U \in \mathcal{T}_S$ and $U z \notin \mathrm{SN}$, we must have $(U)_\lambda \notin \mathrm{WN}_\beta$: otherwise Lemma 7.2(iii) would give $(U z)_\lambda \equiv (U)_\lambda z \in \mathrm{WN}_\beta = \mathrm{SN}_\beta$ (as $(U z)_\lambda \in \Lambda_{\mathrm{I}}$), which pulls back via forward simulation to $U z \in \mathrm{SN}$.

To exhibit the explicit $\beta$-loop beneath $\lambda z$ for $N_{10}$, note that two weak-head $\beta$-steps yield $(N_{10})_\lambda \equiv (S)_\lambda\,(S(S A A))_\lambda\,(S)_\lambda \to_{\mathrm{wh}}^2 \lambda z.\, (N_{10}\,z)_\lambda$. Inside $\lambda z$, three pure-$S$ contractions (nine $\beta$-steps) give

$$
N_{10}\,z \equiv S\bigl(S(S A A)\bigr)S z \;\to_S\; S(S A A)z(S z) \;\to_S\; \bigl(S A A (S z)\bigr)\bigl(z(S z)\bigr) \;\to_S\; \Bigl(\bigl(A(S z)\bigr)\bigl(A(S z)\bigr)\Bigr)\bigl(z(S z)\bigr).
$$

Define $G_0(z) \equiv A(S z)$, $G_{n+1}(z) \equiv S(S z)\,G_n(z)$, and $\Phi_n(z) \equiv G_0(z)\,G_n(z)$ for $n \ge 0$. For every $n \ge 0$, three pure-$S$ contractions yield

$$
\begin{aligned}
  \Phi_n(z) \;\equiv\; \bigl(S S S (S z)\bigr)\,G_n(z)
  &\;\to_S\; \bigl(S(S z)(S(S z))\bigr)\,G_n(z) \\
  &\;\to_S\; \bigl(S z\,G_n(z)\bigr)\,\bigl(S(S z)\,G_n(z)\bigr) \;\equiv\; \bigl(S z\,G_n(z)\bigr)\,G_{n+1}(z) \\
  &\;\to_S\; \bigl(z\,G_{n+1}(z)\bigr)\,\bigl(G_n(z)\,G_{n+1}(z)\bigr).
\end{aligned} \tag{7.4}
$$

By induction on $n \ge 0$, every $Y \in \mathcal{T}_S(\mathcal{V})$ satisfies $G_n(z)\,Y \to_S^n D_n[G_0(z)\,Y]$ with $D_0[\,] \equiv \square$ and $D_{n+1}[\,] \equiv (S z Y)\,D_n[\,]$ (since $G_{n+1}(z)\,Y \equiv S(S z)\,G_n(z)\,Y \to_S (S z Y)(G_n(z)\,Y)$). Taking $Y \equiv G_{n+1}(z)$ in (7.4) gives $\Phi_n(z) \to_S^{n+3} (z\,G_{n+1}(z))\,D_n[\Phi_{n+1}(z)]$, so $(N_{10})_\lambda$ enters the non-terminating $\beta$-reduction

$$
(N_{10})_\lambda \;\to_\beta^2\; \lambda z.\, (N_{10}\,z)_\lambda \;\to_\beta^9\; \lambda z.\, \bigl((\Phi_0(z))_\lambda\,(z\,(S z)_\lambda)\bigr) \;\to_\beta^9\; \lambda z.\, \Bigl(\bigl((z\,(G_1(z))_\lambda)\,(\Phi_1(z))_\lambda\bigr)\,\bigl(z\,(S z)_\lambda\bigr)\Bigr) \;\to_\beta^{12}\; \cdots
$$

underneath $\lambda z$, proving $N_{10}\,z \notin \mathrm{SN}$ and $(N_{10})_\lambda \notin \mathrm{SN}_\beta$.

Similarly, for $W_9$ and $W_9^{\mathrm{nf}}$, we have $W_9\,z \to_S W_9^{\mathrm{nf}}\,z$ and $(W_9)_\lambda \to_\beta^3 (W_9^{\mathrm{nf}})_\lambda \to_{\mathrm{wh}}^2 \lambda z.\, (W_9^{\mathrm{nf}}\,z)_\lambda$. Put $P_z \equiv S A (S z)$, $E_0(z) \equiv S(S z)P_z$, $E_{n+1}(z) \equiv (S z)\,E_n(z)$, and $\Psi_n(z) \equiv P_z\,E_n(z)$. Six pure-$S$ contractions reduce $W_9^{\mathrm{nf}}\,z$ to $\bigl((z\,E_0(z))\,\Psi_0(z)\bigr)(z(S z))$:

$$
\begin{aligned}
  W_9^{\mathrm{nf}}\,z
  &\;\to_S^2\; \bigl(S A (S A)(S z)\bigr)\bigl(z(S z)\bigr) \;\to_S\; \bigl(A(S z)\,P_z\bigr)\bigl(z(S z)\bigr) \\
  &\;\to_S^2\; \bigl(S z P_z\,E_0(z)\bigr)\bigl(z(S z)\bigr) \;\to_S\; \Bigl(\bigl(z\,E_0(z)\bigr)\,\Psi_0(z)\Bigr)\bigl(z(S z)\bigr).
\end{aligned} \tag{7.5}
$$

For each $n \ge 0$, three contractions give $\Psi_n(z) \to_S (A\,E_n(z))\,E_{n+1}(z) \to_S^2 (E_n(z)\,E_{n+1}(z))(S\,E_n(z)\,E_{n+1}(z))$, while induction on $n$ shows $E_n(z)\,Y \to_S^{n+1} \widetilde{D}_n[P_z\,Y]$ (from $E_0(z)\,Y \to_S (S z Y)(P_z Y)$ and $E_{n+1}(z)\,Y \to_S (z Y)(E_n(z)\,Y)$), yielding $\Psi_n(z) \to_S^{n+4} \widetilde{C}_n[\Psi_{n+1}(z)]$ and hence $W_9^{\mathrm{nf}}\,z, W_9\,z \notin \mathrm{SN}$ and $(W_9)_\lambda, (W_9^{\mathrm{nf}})_\lambda \notin \mathrm{SN}_\beta$. For $W_{\mathrm{Wal}} \equiv S V V$, setting $H_0(z) \equiv V z$ and $H_{n+1}(z) \equiv T\,H_n(z)$ gives $W_{\mathrm{Wal}}\,z \to_S H_0(z)\,H_0(z)$ and $H_0(z)\,H_n(z) \to_S^2 (H_{n+1}(z)\,H_{n+1}(z))(z\,H_n(z))$, while $H_m(z)\,Y \to_S^m \widehat{D}_m[H_0(z)\,Y]$ yields $H_0(z)\,H_n(z) \to_S^{n+3} \widehat{C}_n[H_0(z)\,H_{n+1}(z)]$, confirming $W_{\mathrm{Wal}}\,z \notin \mathrm{SN}$ and $(W_{\mathrm{Wal}})_\lambda \notin \mathrm{SN}_\beta$.

For (iii), forward simulation already shows that $(M)_\lambda \in \mathrm{SN}_\beta$ implies $M \in \mathrm{SN}$ for all $M \in \mathcal{T}_S$. Across the $626$ closed pure-$S$ terms with $|M| \le 8$ ($583$ of which belong to $\mathrm{SN}$) and the $323$ closed pure-$S$ normal forms of leaf size $9$ ($539$ cumulative closed normal forms with $|N| \le 9$), executing deterministic leftmost-outermost $\beta$-reduction reaches a $\beta$-normal form on $(M)_\lambda$ for every $M \in \mathcal{T}_S \cap \mathrm{SN}$ with $|M| \le 8$ and on $(N)_\lambda$ for every $N \in \mathcal{T}_S \cap \mathrm{NF}$ with $|N| \le 9$ (for instance, on the $9$-leaf normal form $S(S(S A A))$, applying two fresh variables gives $S(S(S A A))\,x_0\,x_1 \to_S^2 (S A A (x_0 x_1))(x_1(x_0 x_1))$, where the variable-headed term $x_0 x_1$ replaces $S z$ in (7.4) and halts after four further steps at $((x_0 x_1)\,R)(S(x_0 x_1)\,R)$ with $R \equiv S(x_0 x_1)(S(x_0 x_1))$). Lemma 7.2(iii) upgrades $\mathrm{WN}_\beta$ to $\mathrm{SN}_\beta$ on all of these terms.
 $\square$

Because every $M \in \mathcal{T}_S(\mathcal{V})$ has functional order at most $3$ (Proposition 2.4(iii) and Theorem 7.3(iii)), applying $M$ to three distinct fresh variables $x_0, x_1, x_2 \notin \mathrm{FV}(M)$ exhausts all outer partial $S$-combinators along the top spine of $M$. On this basis, Barendregt, Endrullis, Klop, and Waldmann formulated two normalization conjectures on page 102 of [4]: Conjecture 42 asserts that for all $M \in \mathcal{T}_S(\mathcal{V})$ and fresh $x_0, x_1, x_2 \notin \mathrm{FV}(M)$, the term $M x_0 x_1 x_2$ normalizes in $\mathrm{CL}(S)$ if and only if $(M)_\lambda$ normalizes in $\lambda\beta$; and Conjecture 43 asserts that for every finite-order combinator $M$ and fresh $x_1, \dots, x_{\operatorname{ord}_{\mathrm{CL}}(M)} \notin \mathrm{FV}(M)$, the term $M x_1 \cdots x_{\operatorname{ord}_{\mathrm{CL}}(M)}$ normalizes if and only if $(M)_\lambda$ normalizes in $\lambda\beta$ (specializing at $\operatorname{ord}_{\mathrm{CL}}(M) = 1$ to single-variable saturation $M x_0 \in \mathrm{WN} \implies (M)_\lambda \in \mathrm{WN}_\beta$).

Both conjectures fail in the forward direction because outer variable saturation inspects only the root spine: once $M x_0$ reduces to a variable-headed term $x_0\,U_1\,U_2$, any further outer variables $x_1, x_2$ accumulate passively on the right without probing whether an internal argument $U_i$ is itself a partial $S$-application $S W x_0 \in \mathrm{NF}$ whose $\lambda$-translation diverges beneath its own internal $\lambda$-binder. To capture nested binder saturation purely within $\mathrm{CL}(S)$, without $\lambda$-abstractions or substitution, we define *hereditary fresh-variable saturation* $\mathrm{DeepNorm}(M)$ on $M \in \mathcal{T}_S(\mathcal{V})$ inductively as the least predicate closed under the four inference rules

$$
\begin{gathered}
  \frac{M \to_S M' \qquad \mathrm{DeepNorm}(M')}{\mathrm{DeepNorm}(M)} \;\text{(step)},
  \qquad\qquad
  \frac{x \in \mathcal{V}}{\mathrm{DeepNorm}(x)} \;\text{(var)}, \\[0.8ex]
  \frac{\mathrm{hd}(A) \in \mathcal{V} \qquad \mathrm{DeepNorm}(A) \qquad \mathrm{DeepNorm}(B)}{\mathrm{DeepNorm}(A B)} \;\text{(app)},
  \qquad\qquad
  \frac{M \in \mathcal{P}_S \qquad z \in \mathcal{V} \setminus \mathrm{FV}(M) \qquad \mathrm{DeepNorm}(M z)}{\mathrm{DeepNorm}(M)} \;\text{(sat)},
\end{gathered} \tag{7.6}
$$

where $\mathrm{hd}(a) = a$ on atoms $a \in \{S\} \cup \mathcal{V}$ and $\mathrm{hd}(A B) = \mathrm{hd}(A)$ denotes the leftmost leaf. Thus $\mathrm{DeepNorm}(M)$ holds if and only if $M$ reduces in $\mathrm{CL}(S)$ either to a variable-headed application $x\,A_1 \cdots A_r$ ($r \ge 0$) whose arguments $A_i$ satisfy $\mathrm{DeepNorm}(A_i)$, or to a partial $S$-application $H \in \mathcal{P}_S$ satisfying $\mathrm{DeepNorm}(H z)$ for a fresh variable $z \notin \mathrm{FV}(H)$.

**Theorem 7.5 (Simultaneous refutation of Conjectures 42 and 43 and hereditary saturation repair).** 
Let $A \equiv S S S$, and for any $U \in \mathcal{T}_S$ set $\mathcal{C}(U) \equiv S A (S U)$.

- (i) *Simultaneous refutation of Conjectures 42 and 43 [4, p. 102]:* Instantiating $\mathcal{C}(U)$ with $W_9, N_{10}, W_9^{\mathrm{nf}}, W_{\mathrm{Wal}}$ from Proposition 7.4 yields the closed pure-$S$ combinators

$$
M_{14} \;\equiv\; S A (S W_9), \qquad M_{15} \;\equiv\; S A (S N_{10}), \qquad M_{16} \;\equiv\; S A (S W_9^{\mathrm{nf}}), \qquad M_{18} \;\equiv\; S A (S W_{\mathrm{Wal}}),
$$

of leaf sizes $|M_{14}| = 14$, $|M_{15}| = 15$, $|M_{16}| = 16$, and $|M_{18}| = 18$, with $M_{15}, M_{16}, M_{18} \in \mathcal{T}_S \cap \mathrm{NF}$ and $M_{14} \to_S M_{16}$. Every $M \in \{M_{14}, M_{15}, M_{16}, M_{18}\}$ satisfies

$$
\operatorname{ord}_{\mathrm{CL}}(M) \;=\; \operatorname{ord}_\lambda\bigl((M)_\lambda\bigr) \;=\; 1, \qquad M x_0 \;\in\; \mathrm{SN}, \qquad M x_0 x_1 x_2 \;\in\; \mathrm{SN}
$$

for all $x_0, x_1, x_2 \in \mathcal{V}$, yet $(M)_\lambda \notin \mathrm{SN}_\beta$ and $(M)_\lambda \notin \mathrm{WN}_\beta$, refuting both Conjecture 42 and Conjecture 43 simultaneously. Moreover, $14$ leaves and $15$ leaves are the global minimum leaf sizes of closed pure-$S$ counterexamples in $\mathcal{T}_S$ and $\mathcal{T}_S \cap \mathrm{NF}$, respectively.
- (ii) *Validity of the reverse direction:* For every $M \in \mathcal{T}_S(\mathcal{V})$, every integer $k \ge 0$, and all variables $x_1, \dots, x_k \in \mathcal{V}$, if $(M)_\lambda \in \mathrm{SN}_\beta$ (equivalently $(M)_\lambda \in \mathrm{WN}_\beta$), then $M x_1 \cdots x_k \in \mathrm{SN}$ (equivalently $M x_1 \cdots x_k \in \mathrm{WN}$).
- (iii) *Exact hereditary saturation theorem:* For every open or closed pure-$S$ term $M \in \mathcal{T}_S(\mathcal{V})$,

$$
\mathrm{DeepNorm}(M) \;\iff\; (M)_\lambda \in \mathrm{SN}_\beta \;\iff\; (M)_\lambda \in \mathrm{WN}_\beta.
$$

*Proof.* 
For (i), let $U \in \mathcal{T}_S$ be any closed term satisfying $U \to_S^* U^{\mathrm{nf}} \in \mathrm{NF}$ and $U y \notin \mathrm{SN}$ for $y \in \mathcal{V}$, and put $M \equiv S A (S U)$. Clearly $|M| = 1 + 3 + (1 + |U|) = 5 + |U|$ and $M \in \mathrm{NF}$ whenever $U \in \mathrm{NF}$. For any variable $x_0 \in \mathcal{V}$, three pure-$S$ contractions yield

$$
M x_0 \;\equiv\; S A (S U)\,x_0 \;\to_S\; (A x_0)(S U x_0) \;\to_S\; \bigl(S x_0 (S x_0)\bigr)(S U x_0) \;\to_S\; \bigl(x_0\,(S U x_0)\bigr)\,\bigl(S x_0\,(S U x_0)\bigr). \tag{7.7}
$$

Reducing $U \to_S^* U^{\mathrm{nf}}$ inside both occurrences of $S U x_0$ gives $M x_0 \to_S^* N_1(x_0) \equiv (x_0\,(S U^{\mathrm{nf}} x_0))(S x_0\,(S U^{\mathrm{nf}} x_0))$. Since $U^{\mathrm{nf}} \in \mathrm{NF}$, both $S U^{\mathrm{nf}} x_0$ and $S x_0 (S U^{\mathrm{nf}} x_0)$ have spine length $2$ and lie in $\mathrm{NF}$, while $\mathrm{hd}(N_1(x_0)) = x_0 \ne S$ precludes any root redex; hence $N_1(x_0) \in \mathrm{NF}$ and $M x_0 \in \mathrm{WN} = \mathrm{SN}$ by Proposition 2.2(iii). Appending $x_1, x_2 \in \mathcal{V}$ likewise gives $M x_0 x_1 x_2 \to_S^* N_1(x_0)\,x_1\,x_2 \in \mathrm{NF}$, so $M x_0 x_1 x_2 \in \mathrm{WN} = \mathrm{SN}$. Next, $M \equiv S A (S U) \in \mathcal{P}_S$ is closed, so to verify $\operatorname{ord}_{\mathrm{CL}}(M) = 1$ (and hence $\operatorname{ord}_\lambda((M)_\lambda) = 1$ by Theorem 7.3(iii)) it suffices by Theorem 7.3(i) to check that $M x_0$ cannot reduce to any $H \in \mathcal{P}_S$. Indeed, if $M x_0 \to_S^* H \in \mathcal{P}_S$, Church–Rosser confluence of $\to_S^*$ (Proposition 2.2(i)) with $M x_0 \to_S^* N_1(x_0) \in \mathrm{NF}$ forces $H \to_S^* N_1(x_0)$; yet every $H \in \mathcal{P}_S$ satisfies $\operatorname{ls}(H) \le 2$ and $\mathrm{hd}(H) = S$, both of which are invariant under $\to_S^*$, contradicting $\mathrm{hd}(N_1(x_0)) = x_0$. Now suppose toward a contradiction that $(M)_\lambda \in \mathrm{WN}_\beta$. Applying Lemma 7.2(iii) at $x_0$ gives $(M x_0)_\lambda \in \mathrm{WN}_\beta = \mathrm{SN}_\beta$; forward simulation along (7.7) places $((x_0\,(S U x_0)_\lambda)((S x_0)_\lambda\,(S U x_0)_\lambda)) \in \mathrm{SN}_\beta$ and hence its subterm $(S U x_0)_\lambda \in \mathrm{SN}_\beta = \mathrm{WN}_\beta$. A second application of Lemma 7.2(iii) at $x_1$ gives $(S U x_0 x_1)_\lambda \in \mathrm{WN}_\beta = \mathrm{SN}_\beta$, and simulating $S U x_0 x_1 \to_S (U x_1)(x_0 x_1)$ places $(U x_1)_\lambda \in \mathrm{SN}_\beta$, forcing $U x_1 \in \mathrm{SN}$ and contradicting Proposition 7.4(ii). Note that replacing $A \equiv S S S$ by $T \equiv S S$ at $13$ leaves fails because $S T (S W_9)\,x_0\,x_1 \to_S^4 (W_9 x_1)(x_0 x_1)(\dots) \notin \mathrm{SN}$ exposes $S W_9 x_0$ directly to $x_1$; checking all closed $M \in \mathcal{T}_S \cap \mathrm{SN}$ with $|M| \le 13$ and all $N \in \mathcal{T}_S \cap \mathrm{NF}$ with $|N| \le 14$ confirms global minimality of $M_{14}$ and $M_{15}$.

For (ii), since $(M)_\lambda \in \Lambda_{\mathrm{I}}$ and $(M x_1 \cdots x_k)_\lambda \equiv (M)_\lambda x_1 \cdots x_k \in \Lambda_{\mathrm{I}}$, iterating Lemma 7.2(iii) $k$ times shows that $(M)_\lambda \in \mathrm{SN}_\beta$ (equivalently $(M)_\lambda \in \mathrm{WN}_\beta$) implies $(M x_1 \cdots x_k)_\lambda \in \mathrm{WN}_\beta = \mathrm{SN}_\beta$, which pulls back via forward simulation to $M x_1 \cdots x_k \in \mathrm{SN} = \mathrm{WN}$.

For (iii), Lemma 7.2(iii) already equates $(M)_\lambda \in \mathrm{SN}_\beta$ with $(M)_\lambda \in \mathrm{WN}_\beta$ since $(M)_\lambda \in \Lambda_{\mathrm{I}}$. To prove that $\mathrm{DeepNorm}(M)$ implies $(M)_\lambda \in \mathrm{WN}_\beta$, proceed by induction on (7.6). Rule (step) follows from $(M)_\lambda \to_\beta^+ (M')_\lambda$, and rule (var) from $(x)_\lambda \equiv x \in \mathrm{NF}_\beta$. In rule (app), $\mathrm{hd}(A) = x \in \mathcal{V}$ implies $(A)_\lambda \equiv x C_1 \cdots C_m$, so Lemma 7.2(i) prevents $(A)_\lambda$ from reducing to any abstraction; thus if $(A)_\lambda \to_\beta^* N_A \in \mathrm{NF}_\beta$ and $(B)_\lambda \to_\beta^* N_B \in \mathrm{NF}_\beta$, then $N_A$ is not an abstraction and $(A B)_\lambda \to_\beta^* N_A N_B \in \mathrm{NF}_\beta$. In rule (sat), $M \in \mathcal{P}_S$ gives $(M)_\lambda \to_\beta^* \lambda x.\, B$ by Theorem 7.3(i) with $z \notin \mathrm{FV}(B)$; if $(M z)_\lambda \to_\beta^* N_z \in \mathrm{NF}_\beta$, confluence with $(M z)_\lambda \to_\beta^* (\lambda x.\, B)\,z \to_\beta B[x := z]$ forces $B[x := z] \to_\beta^* N_z$. Applying the syntactic variable-closing map $\kappa_z^x$ from the proof of Theorem 7.3(ii) yields $B \equiv \kappa_z^x(B[x := z]) \to_\beta^* \kappa_z^x(N_z) \in \mathrm{NF}_\beta$ (as replacing free $z$ by bound $x$ never creates a $\lambda$-abstraction), whence $(M)_\lambda \to_\beta^* \lambda x.\, \kappa_z^x(N_z) \in \mathrm{NF}_\beta$.

Conversely, suppose $(M)_\lambda \to_\beta^* N \in \mathrm{NF}_\beta$. We prove $\mathrm{DeepNorm}(M)$ by strong induction on $\|N\|_\lambda$, noting that $\|B[x := z]\|_\lambda = \|B\|_\lambda$. By part (ii) at $k = 0$, we have $M \in \mathrm{SN} = \mathrm{WN}$, so $M \to_S^* M^{\mathrm{nf}} \in \mathrm{NF}$; by rule (step) and confluence $(M^{\mathrm{nf}})_\lambda \to_\beta^* N$, we may assume $M \equiv M^{\mathrm{nf}} \in \mathrm{NF}$. Every $M^{\mathrm{nf}} \in \mathcal{T}_S(\mathcal{V}) \cap \mathrm{NF}$ falls into three cases: if $M^{\mathrm{nf}} \equiv x \in \mathcal{V}$, rule (var) applies; if $M^{\mathrm{nf}} \equiv A B$ with $\mathrm{hd}(A) = x \in \mathcal{V}$ and $A, B \in \mathrm{NF}$, then $(A)_\lambda$ never reduces to an abstraction, so $(A B)_\lambda \to_\beta^* N$ factors as $N \equiv N_A N_B$ with $(A)_\lambda \to_\beta^* N_A \in \mathrm{NF}_\beta$, $(B)_\lambda \to_\beta^* N_B \in \mathrm{NF}_\beta$, and $\|N_A\|_\lambda, \|N_B\|_\lambda < \|N\|_\lambda$, allowing rule (app) to combine the induction hypotheses on $A$ and $B$; finally, if $\mathrm{hd}(M^{\mathrm{nf}}) = S$, normality forces $\operatorname{ls}(M^{\mathrm{nf}}) \le 2$ and hence $M^{\mathrm{nf}} \in \mathcal{P}_S$, so $(M^{\mathrm{nf}})_\lambda \to_\beta^* \lambda x.\, B$ and confluence forces $N \equiv \lambda x.\, N_0$ ($N_0 \in \mathrm{NF}_\beta$). Choosing a fresh variable $z \in \mathcal{V} \setminus \mathrm{FV}(M^{\mathrm{nf}})$ gives $(M^{\mathrm{nf}} z)_\lambda \to_\beta^* (\lambda x.\, N_0)\,z \to_\beta N_0[x := z] \in \mathrm{NF}_\beta$ with $\|N_0[x := z]\|_\lambda = \|N_0\|_\lambda < \|N\|_\lambda$, so the induction hypothesis gives $\mathrm{DeepNorm}(M^{\mathrm{nf}} z)$ and rule (sat) yields $\mathrm{DeepNorm}(M^{\mathrm{nf}})$.
 $\square$

### 7.3. Open Question 34: Single-Constant Combinatory Saturation, the Unique $\lambda\mathrm{I}$ Sink, and Congruence Incomparability

Theorem 7.5(iii) characterizes $\lambda\beta$-normalization of $(M)_\lambda$ for any $M \in \mathcal{T}_S(\mathcal{V})$ internally within $\mathrm{CL}(S)$ via the hereditary fresh-variable saturation predicate $\mathrm{DeepNorm}(M)$ of (7.6). Restricting to closed pure-$S$ terms $\mathcal{T}_S$, Waldmann [66] established that the intrinsic strong normalization language $\mathrm{SN} \subset \mathcal{T}_S$ is recognized by the $39$-state $S$-algebra $\mathcal{A}_{\mathrm{SN}}$, whereas the $9$-leaf combinator $W_9 \equiv S(S(A A))S$ and the $10$-leaf normal form $N_{10} \equiv S(S(S A A))S$ of Proposition 7.4 witness the strict inclusion $\{M \in \mathcal{T}_S : (M)_\lambda \in \SN_\beta\} \subsetneq \mathrm{SN}$. Because $(M)_\lambda \in \Lambda_{\mathrm{I}}$ for every $M \in \mathcal{T}_S(\mathcal{V})$, Lemma 7.2(iii) equates weak and strong $\beta$-normalization on $(M)_\lambda$. Concerning the tree-automaton complexity of this language, Barendregt, Endrullis, Klop, and Waldmann [4, Question 34, p. 96] introduced

$$
L_{34} \;:=\; \bigl\{M \in \mathcal{T}_S : (M)_\lambda \in \SN_\beta\bigr\} \;=\; \bigl\{M \in \mathcal{T}_S : (M)_\lambda \in \WN_\beta\bigr\}, \tag{7.8}
$$

and asked whether membership in $L_{34}$ is decidable, noting empirical evidence that $L_{34}$ is not a regular tree language over $\{S, \cdot\}$.

By the Myhill–Nerode theorem for binary trees, $L_{34}$ is regular if and only if its syntactic congruence $\equiv_{34}$ has finite index $|\mathcal{T}_S / {\equiv_{34}}| < \infty$, where for $M, N \in \mathcal{T}_S$ we write

$$
M \equiv_{34} N \quad:\Longleftrightarrow\quad \forall\,\text{closed pure-$S$ one-hole contexts } C[\square],\;\; \bigl(C[M] \in L_{34} \iff C[N] \in L_{34}\bigr). \tag{7.9}
$$

Analyzing $L_{34}$ directly presents two apparent obstacles: untyped $\lambda\beta$-reduction involves bound-variable capture avoidance and substitution under binders, while the combinatory characterization $\mathrm{DeepNorm}(M)$ in (7.6) introduces a fresh variable $z \notin \mathrm{FV}(U)$ at every saturation step $U \mapsto U z$, seemingly requiring an unbounded variable alphabet along deep syntactic branches.

Our next theorem removes this fresh-variable requirement completely. Let $\mathrm{CL}(S, x_0)$ denote the left-linear combinatory rewriting system obtained by adjoining to $\{S\}$ a single inert constant $x_0$, with term set $\mathcal{T}_S(\{x_0\})$ and one-step reduction $\to_S$ generated contextually by $S X Y Z \to_S (X Z)(Y Z)$ ($x_0$ participates in no root rule). Define the variable-erasing applicative homomorphism $\pi_0 \colon \mathcal{T}_S(\mathcal{V}) \to \mathcal{T}_S(\{x_0\})$ by

$$
\pi_0(S) \;\equiv\; S, \qquad \pi_0(v) \;\equiv\; x_0 \quad (v \in \mathcal{V}), \qquad \pi_0(A B) \;\equiv\; \pi_0(A)\,\pi_0(B).
$$

On $\mathcal{T}_S(\{x_0\})$, define *single-constant hereditary saturation* $\mathrm{DeepNorm}_1(U)$ inductively as the least predicate closed under four monotone clauses: (i) if $U \to_S U'$ and $\mathrm{DeepNorm}_1(U')$, then $\mathrm{DeepNorm}_1(U)$; (ii) $\mathrm{DeepNorm}_1(x_0)$ holds; (iii) if $\mathrm{hd}(A) = x_0$ and both $\mathrm{DeepNorm}_1(A)$ and $\mathrm{DeepNorm}_1(B)$ hold, then $\mathrm{DeepNorm}_1(A B)$ holds; and (iv) if $U$ is a partial $S$-application ($U \equiv S$, $S P$, or $S P Q$) and $\mathrm{DeepNorm}_1(U x_0)$ holds, then $\mathrm{DeepNorm}_1(U)$ holds. Notice that clause (iv) feeds the same fixed atom $x_0$ at every saturation depth without any freshness side condition. Throughout what follows we retain the abbreviations $T \equiv S S$, $A \equiv S S S$, $V \equiv S(S T T)$, $W_9 \equiv S(S(A A))S$, $N_{10} \equiv S(S(S A A))S$, and $W_{\mathrm{Wal}} \equiv S V V$.

**Theorem 7.6 (Single-constant reduction, unique $\lambda\mathrm{I}$ sink, and congruence incomparability for Question 34).**
The language $L_{34} \subset \mathcal{T}_S$ and its syntactic congruence $\equiv_{34}$ satisfy the following properties:

- (i) *Single-constant combinatory reduction:* For every open or closed pure-$S$ term $M \in \mathcal{T}_S(\mathcal{V})$, one has $\mathrm{DeepNorm}(M)$ if and only if $\mathrm{DeepNorm}_1(\pi_0(M))$. In particular, for every closed term $M \in \mathcal{T}_S$,
  
$$
M \in L_{34} \;\iff\; (M)_\lambda \in \SN_\beta \;\iff\; (M)_\lambda \in \WN_\beta \;\iff\; \mathrm{DeepNorm}_1(M).
$$
- (ii) *Unique two-sided absorbing sink $\infty_{34}$:* For every closed pure-$S$ one-hole context $C[\square]$ and every $M \in \mathcal{T}_S$ with $(M)_\lambda \notin \SN_\beta$, one has $(C[M])_\lambda \notin \SN_\beta$. Consequently, $\infty_{34} := \mathcal{T}_S \setminus L_{34}$ forms a single $\equiv_{34}$-congruence class and acts as the unique two-sided absorbing zero of the syntactic quotient magma $\mathcal{T}_S / {\equiv_{34}}$: for all $M, N \in \infty_{34}$ and $P \in \mathcal{T}_S$, $M \equiv_{34} N$ and $M P, P M \in \infty_{34}$.
- (iii) *Mutual incomparability with intrinsic $S$-algebra congruences and four-way splitting of $q_6$:* The $9$-leaf combinators $A A A \notin \mathrm{SN}$ and $W_9 \in \mathrm{SN}$ satisfy $A A A \equiv_{34} W_9$ while $A A A \not\equiv_{\mathrm{SN}} W_9$, so ${\equiv_{34}} \not\subseteq {\equiv_{\mathrm{SN}}}$. Conversely, inside the single accepting state $q_6$ of $\mathcal{A}_{\mathrm{SN}}$ (and $p_{18}$ of $\mathcal{A}_P$), the four order-$2$ closed pure-$S$ normal forms
  
$$
u_0 \;\equiv\; S(S(S A)), \qquad u_1 \;\equiv\; V \;\equiv\; S(S T T), \qquad u_2 \;\equiv\; S V, \qquad u_3 \;\equiv\; S(S(S A A)) \tag{7.10}
$$

  all lie in $L_{34}$ (with $u_0$ and $u_2$ sharing the identical joint state $(q_6, h_9, p_{18})$ in $\mathcal{A}_{\mathrm{SN}} \times \mathcal{A}_{\mathrm{HN}} \times \mathcal{A}_P$), yet are pairwise $\equiv_{34}$-inequivalent under the three closed contexts $C_1[\square] \equiv \square \cdot S$, $C_2[\square] \equiv \square \cdot V$, and $C_3[\square] \equiv (S V) \cdot \square$ (and inequivalent to $\infty_{34}$ in the empty context $\square$); hence ${\equiv_{\mathrm{SN} \times \mathrm{HN} \times \mathrm{Prod}}} \not\subseteq {\equiv_{34}}$.

*Proof.*
For (i), we first verify that $\pi_0$ both preserves and reflects one-step reduction $\to_S$. Because $\pi_0$ is an applicative homomorphism fixing $S$, $\pi_0(S X Y Z) \equiv S\,\pi_0(X)\,\pi_0(Y)\,\pi_0(Z) \to_S (\pi_0(X)\,\pi_0(Z))(\pi_0(Y)\,\pi_0(Z)) \equiv \pi_0((X Z)(Y Z))$, so structural induction gives $M \to_S M'$ implies $\pi_0(M) \to_S \pi_0(M')$. Conversely, suppose $\pi_0(M) \to_S U'$. By definition of $\pi_0$, $\pi_0(E) \equiv S$ forces $E \equiv S$, $\pi_0(E) \equiv x_0$ forces $E \in \mathcal{V}$, and $\pi_0(E) \equiv P_1 P_2$ forces $E \equiv E_1 E_2$ with $\pi_0(E_i) \equiv P_i$. If $\pi_0(M) \to_S U'$ is a root contraction $\pi_0(M) \equiv S X' Y' Z'$ with $U' \equiv (X' Z')(Y' Z')$, inverting $\pi_0$ three times along the left spine forces $M \equiv S X Y Z$ with $\pi_0(X) \equiv X'$, $\pi_0(Y) \equiv Y'$, and $\pi_0(Z) \equiv Z'$; because the pure-$S$ rule $S X Y Z \to_S (X Z)(Y Z)$ is left-linear (no non-linear equality test between subterms appears on the left-hand side), $M$ contracts directly to $M' \equiv (X Z)(Y Z)$ with $\pi_0(M') \equiv U'$, even when distinct variables inside $X, Y, Z$ are identified to $x_0$ by $\pi_0$. Context steps lift directly by the induction hypothesis. Similarly, $\mathrm{hd}(M) \in \mathcal{V}$ holds if and only if $\mathrm{hd}(\pi_0(M)) = x_0$, and $M \in \mathcal{P}_S$ holds if and only if $\pi_0(M)$ is a partial $S$-application in $\mathcal{T}_S(\{x_0\})$.

An immediate induction on (7.6) now maps $\mathrm{DeepNorm}(M)$ to $\mathrm{DeepNorm}_1(\pi_0(M))$, since $\pi_0(M z) \equiv \pi_0(M)\,x_0$ in rule (sat). Conversely, induction on a derivation of $\mathrm{DeepNorm}_1(U)$ proves that every $M \in \mathcal{T}_S(\mathcal{V})$ with $\pi_0(M) \equiv U$ satisfies $\mathrm{DeepNorm}(M)$: clause (i) uses backward step reflection; clause (ii) forces $M \in \mathcal{V}$ and applies rule (var); clause (iii) splits $M \equiv A B$ with $\mathrm{hd}(A) \in \mathcal{V}$ and applies rule (app); and in clause (iv), where $U \equiv \pi_0(M)$ is a partial $S$-application with $\mathrm{DeepNorm}_1(U x_0)$, we have $M \in \mathcal{P}_S$, and choosing a fresh variable $z \in \mathcal{V} \setminus \mathrm{FV}(M)$ (for instance, of index strictly exceeding the maximum variable index occurring in the finite tree $M$) gives $\pi_0(M z) \equiv \pi_0(M)\,\pi_0(z) \equiv U x_0$. The induction hypothesis on $U x_0$ then yields $\mathrm{DeepNorm}(M z)$, and rule (sat) gives $\mathrm{DeepNorm}(M)$. Since $\pi_0(M) \equiv M$ for $M \in \mathcal{T}_S$, Theorem 7.5(iii) completes (i).

For (ii), in the untyped $\lambda$-calculus any binary application $P Q \in \SN_\beta$ satisfies $P \in \SN_\beta$ and $Q \in \SN_\beta$, by well-founded induction on reachable reducts of $P Q$. Because closed pure-$S$ one-hole contexts are built solely from $\square$ and left/right binary applications without outer $\lambda K$-abstractions, induction on $C[\square]$ shows that $(C[M])_\lambda \in \SN_\beta$ implies $(M)_\lambda \in \SN_\beta$. Contrapositively, $M \in \infty_{34}$ implies $C[M] \in \infty_{34}$ for every closed context $C[\square]$. Specializing to $\square \cdot P$ and $P \cdot \square$ shows that $\infty_{34}$ is a two-sided ideal, and for all $M, N \in \infty_{34}$ both $C[M] \in L_{34}$ and $C[N] \in L_{34}$ evaluate to false in every context $C[\square]$, so $M \equiv_{34} N$.

For (iii), $A A A \notin \mathrm{SN}$ implies $(A A A)_\lambda \notin \SN_\beta$ by forward simulation, whereas Proposition 7.4(ii) gives $W_9 \in \mathrm{SN}$ and $(W_9)_\lambda \notin \SN_\beta$. Thus $A A A, W_9 \in \infty_{34}$, so $A A A \equiv_{34} W_9$ by (ii), whereas $A A A \not\equiv_{\mathrm{SN}} W_9$ in the empty context $\square$. Next, each term in (7.10) has spine length at most $2$ at every subterm and hence belongs to $\mathcal{T}_S \cap \mathrm{NF}$. Writing $(q_i, h_j, p_k)$ for non-absorbing states of $\mathcal{A}_{\mathrm{SN}} \times \mathcal{A}_{\mathrm{HN}} \times \mathcal{A}_P$, bottom-up evaluation from $\llbracket S \rrbracket = (q_0, h_0, p_0)$, $\llbracket T \rrbracket = (q_1, h_1, p_1)$, and $\llbracket A \rrbracket = (q_7, h_6, p_3)$ gives $\llbracket u_0 \rrbracket = (q_6, h_9, p_{18})$, $\llbracket u_1 \rrbracket = (q_6, h_8, p_{18})$, $\llbracket u_2 \rrbracket = (q_6, h_9, p_{18})$, and $\llbracket u_3 \rrbracket = (q_6, h_{10}, p_{18})$; in particular, all four map to $q_6$ in $\mathcal{A}_{\mathrm{SN}}$ and $p_{18}$ in $\mathcal{A}_P$, and $u_0, u_2$ share $(q_6, h_9, p_{18})$. Applying part (i), single-constant saturation reduces $u_0, u_1, u_2, u_3$ to pure $x_0$-headed normal trees, placing all four in $L_{34}$. Under $(C_1, C_2, C_3)$, saturation reduces $C_1[u_0], C_2[u_0], C_3[u_0]$ completely to inert $x_0$-trees, so $(C_1[u_0], C_2[u_0], C_3[u_0]) \in L_{34}^3$. For $u_1 \equiv V$, one has $V S, V V \in L_{34}$, whereas $C_3[u_1] \equiv S V V \equiv W_{\mathrm{Wal}} \notin L_{34}$ by Proposition 7.4(ii), separating $u_1$ from $u_0$. For $u_2 \equiv S V$, one has $S V S \in L_{34}$, whereas $C_2[u_2] \equiv S V V \equiv W_{\mathrm{Wal}} \notin L_{34}$, separating $u_2$ from both $u_0$ and $u_1$ (and demonstrating ${\equiv_{\mathrm{SN} \times \mathrm{HN} \times \mathrm{Prod}}} \not\subseteq {\equiv_{34}}$ via $u_0$ and $u_2$). For $u_3 \equiv S(S(S A A))$, already $C_1[u_3] \equiv S(S(S A A))S \equiv N_{10} \notin L_{34}$ by Proposition 7.4(i), separating $u_3$ from $u_0, u_1, u_2$. The resulting membership rows $(1, 1, 1)$, $(1, 1, 0)$, $(1, 0, *)$, and $(0, *, *)$ form an upper-triangular separation matrix, while the empty context $\square$ separates all four from $N_{10} \in \infty_{34}$. $\square$

*Remark 7.7 (Exact single-constant frontier of Open Question 34).*
Whether the cardinal $|\mathcal{T}_S / {\equiv_{34}}|$ is finite (making $L_{34}$ a regular tree language and hence decidable in linear time, answering Question 34 affirmatively) or countably infinite (making $L_{34}$ non-regular, with general decidability still open) remains open. Theorem 7.6 isolates the exact combinatory content of this question: part (i) eliminates $\lambda$-binders, $\alpha$-renaming, and fresh-variable bookkeeping altogether, reducing Question 34 to whether single-constant saturation $\mathrm{DeepNorm}_1$ in the two-atom left-linear system $\mathrm{CL}(S, x_0)$ induces finitely many contextual equivalence classes on $\mathcal{T}_S$. Parts (ii) and (iii) explain why existing finite pure-$S$ algebras do not transfer directly: on the rejecting side, non-erasing $\lambda\mathrm{I}$ contexts collapse $\mathrm{SN} \setminus L_{34}$ and $\mathcal{T}_S \setminus \mathrm{SN}$ into the single sink $\infty_{34}$, while on the accepting side, repeated probing by $x_0$ penetrates arbitrarily nested partial $S$-combinators and activates frozen latent subterms (such as $S A A$ inside $u_3$), shattering even single joint fibers such as $(q_6, h_9, p_{18})$ of $\mathcal{A}_{\mathrm{SN}} \times \mathcal{A}_{\mathrm{HN}} \times \mathcal{A}_P$.

### 7.4. Open Question 32: Small-Term $\lambda\beta$-Rigidity and Equational Non-Finite Axiomatizability

We now turn from tree-automaton complexity to equational completeness, comparing external $\lambda\beta$-convertibility $(M)_\lambda =_\beta (N)_\lambda$ on $\mathcal{T}_S(\mathcal{V})$ with intrinsic combinatory convertibility $M =_S N$. Because every pure-$S$ contraction $S X Y Z \to_S (X Z)(Y Z)$ is simulated by $\beta$-reduction, induction on conversion steps yields the one-way implication

$$
M =_S N \;\implies\; (M)_\lambda =_\beta (N)_\lambda \qquad \bigl(M, N \in \mathcal{T}_S(\mathcal{V})\bigr). \tag{7.11}
$$

Over the full combinatory basis $\{S, K\}$, intrinsic equality $=_{S,K}$ is likewise strictly weaker than $=_\beta$, yet Curry [19, 20] and Barendregt [1, Theorem 7.3.10] proved that adjoining finitely many closed combinatory equations (Curry's five axioms) suffices to axiomatize $(M)_\lambda =_\beta (N)_\lambda$ across all open and closed $\mathrm{CL}(S, K)$-terms.

In $\mathrm{CL}(S)$, where the erasing combinator $K$ is absent, constant bracket abstractions $\lambda^* x.\, M$ ($x \notin \mathrm{FV}(M)$) cannot be synthesized internally. Waldmann [66] observed that $=_S$ is strictly weaker than $=_\beta$ even on closed pure-$S$ normal forms, exhibiting a pair of closed normal forms of leaf sizes $8$ and $11$. Asking whether a finite Curry-style basis nevertheless exists for pure $S$, Barendregt, Endrullis, Klop, and Waldmann [4, Question 32, p. 94] posed the problem of whether there is a finite set $\mathcal{E}$ of equations between pure-$S$ terms such that, for all $M, N \in \mathcal{T}_S(\mathcal{V})$,

$$
\mathrm{CL}(S) + \mathcal{E} \vdash M = N \;\iff\; (M)_\lambda =_\beta (N)_\lambda. \tag{7.12}
$$

Here, given any finite set of schematic equations $\mathcal{E} = \{P_1 = Q_1, \dots, P_r = Q_r\} \subset \mathcal{T}_S(\mathcal{V}) \times \mathcal{T}_S(\mathcal{V})$ (whose members $P_i, Q_i$ may contain arbitrary free variables), equational derivability $\mathrm{CL}(S) + \mathcal{E} \vdash M = N$ is the least equivalence relation on $\mathcal{T}_S(\mathcal{V})$ containing one-step reduction $A \to_S B$ together with every substitution instance $P_i^\sigma = Q_i^\sigma$ ($\sigma \colon \mathcal{V} \to \mathcal{T}_S(\mathcal{V})$) of $(P_i = Q_i) \in \mathcal{E}$, and closed under left and right application congruence ($A_1 = A_2$ implies $A_1 C = A_2 C$ and $C A_1 = C A_2$). We call $\mathcal{E}$ *$\lambda\beta$-sound* if $(P)_\lambda =_\beta (Q)_\lambda$ for every $(P = Q) \in \mathcal{E}$; since $=_\beta$ is closed under substitution and application contexts, $\lambda\beta$-soundness of $\mathcal{E}$ guarantees that $\mathrm{CL}(S) + \mathcal{E} \vdash M = N$ implies $(M)_\lambda =_\beta (N)_\lambda$.

Two syntactic notions govern local rigidity under $=_S$ and $=_\beta$. First, a term $M \in \mathcal{T}_S(\mathcal{V})$ is *globally $\lambda\beta$-rigid* if $(M)_\lambda =_\beta (N)_\lambda$ holds if and only if $M =_S N$ for every $N \in \mathcal{T}_S(\mathcal{V})$. Second, a subterm of the form $(X Z)(Y Z)$, whose left and right factors are applications sharing the identical right argument $Z$, is called a *co-redex*; a term $W \in \mathcal{T}_S(\mathcal{V})$ is an *isolated normal form* if $W \in \mathrm{NF}$ and $W$ contains no co-redex subterm (cf. Subsection 9.3). Because every contraction $C[S X Y Z] \to_S C[(X Z)(Y Z)]$ creates a co-redex $(X Z)(Y Z)$, an isolated normal form $W$ has neither forward reducts nor backward predecessors, and Church–Rosser confluence (Proposition 2.2(i)) collapses its $=_S$-class to the singleton $[W]_{=_S} = \{W\}$.

**Proposition 7.8 (Universal $S$-free rigidity, small-term global rigidity, and uniqueness of the minimal $(8, 11)$ pair).**
The following rigidity and separation laws hold on $\mathcal{T}_S(\mathcal{V})$:

- (i) *Universal backward-cone rigidity of $S$-free trees:* Let $F \in \mathcal{T}_S(\mathcal{V})$ be an $S$-free term (built solely from variables in $\mathcal{V}$ and binary application). For every open or closed pure-$S$ term $M \in \mathcal{T}_S(\mathcal{V})$,
  
$$
(F)_\lambda =_\beta (M)_\lambda \;\iff\; M \to_S^* F. \tag{7.13}
$$

  In particular, every variable $x \in \mathcal{V}$ satisfies $(x)_\lambda =_\beta (M)_\lambda$ if and only if $M \equiv x$, and every co-redex-free $S$-free term $F$ satisfies $(F)_\lambda =_\beta (M)_\lambda$ if and only if $M \equiv F$.
- (ii) *Small-term global rigidity and the minimal $(8, 11)$ pairs:* The combinators $S$, $T \equiv S S$, $A \equiv S S S$, and every closed strongly normalizing term $M \in \mathcal{T}_S \cap \mathrm{SN}$ with $|M| \le 7$ (comprising all $65$ closed terms with $|M| \le 6$ and all $89$ closed normal forms with $|M| \le 7$) are globally $\lambda\beta$-rigid in $\mathcal{T}_S(\mathcal{V})$; across all $197$ closed pure-$S$ terms with $|M|, |N| \le 7$, $(M)_\lambda =_\beta (N)_\lambda$ holds if and only if $M =_S N$. At sizes $(8, 11)$, for any $x, y \in \mathcal{T}_S(\mathcal{V})$, the two-variable schematic terms
  
$$
L(x, y) \;\equiv\; S\,(S\,T\,y)\,(S\,x\,y), \qquad R(x, y) \;\equiv\; S\,\bigl(S\,y\,(S\,x\,y)\bigr)\,\bigl(S\,(T\,x)\,y\bigr) \tag{7.14}
$$

  satisfy $(L(x, y))_\lambda =_\beta (R(x, y))_\lambda$; when $x, y \in \mathcal{V}$, $L(x, y)$ ($8$ leaves) is an isolated normal form and $R(x, y)$ ($11$ leaves) lies in $\mathrm{NF}$, so $L(x, y) \not=_S R(x, y)$. Specializing to $x \equiv y \equiv S$ recovers Waldmann's $(8, 11)$ closed normal-form pair [66]
  
$$
U_1 \;\equiv\; S\,(S\,T\,S)\,A \quad (|U_1| = 8), \qquad U_2 \;\equiv\; S\,(T\,A)\,(S\,A\,S) \quad (|U_2| = 11), \tag{7.15}
$$

  satisfying $(U_1)_\lambda =_\beta (U_2)_\lambda$, $[U_1]_{=_S} = \{U_1\}$, and $U_1 \not=_S U_2$; moreover, $\{U_1, U_2\}$ is the unique unordered pair of distinct closed pure-$S$ normal forms $M, N \in \mathcal{T}_S \cap \mathrm{NF}$ with $|M|, |N| \le 11$ (among all $3{,}562$ such normal forms) satisfying $(M)_\lambda =_\beta (N)_\lambda$.

*Proof.*
For (i), $M \to_S^* F$ implies $(M)_\lambda \to_\beta^* (F)_\lambda$, giving $(F)_\lambda =_\beta (M)_\lambda$. For the converse, we first establish quantitative invariants of $\beta$-reduction on $\lambda$-translations of pure-$S$ terms. For $E \in \Lambda$, define the variable-leaf count $\mathrm{vl}(E)$ ($\mathrm{vl}(v) = 1$ on bound or free variable occurrences, $\mathrm{vl}(\lambda z.\, P) = \mathrm{vl}(P)$, $\mathrm{vl}(P Q) = \mathrm{vl}(P) + \mathrm{vl}(Q)$), the binder count $\#_\lambda(E)$ ($\#_\lambda(v) = 0$, $\#_\lambda(\lambda z.\, P) = 1 + \#_\lambda(P)$, $\#_\lambda(P Q) = \#_\lambda(P) + \#_\lambda(Q)$), and the free-occurrence count $\#_v(E)$ for $v \in \mathcal{V}$. Let $\mathcal{I}_S \subset \Lambda_{\mathrm{I}}$ be the class of $\lambda$-terms $E$ such that at every abstraction subterm $\lambda z.\, P$ of $E$, the bound variable $z$ occurs $c_z(P) \ge 1$ times in $P$, $\#_\lambda(P) + 2 \le \mathrm{vl}(P)$, and either $P$ is itself an abstraction or $c_z(P) \ge 2$. Structural induction shows $\mathrm{vl}(E) - \#_\lambda(E) \ge 1$ for all $E \in \mathcal{I}_S$; since $(S)_\lambda \equiv \lambda x y z.\, (x z)(y z) \in \mathcal{I}_S$ (its three nested bodies have $(\#_\lambda, \mathrm{vl}) = (0, 4), (1, 4), (2, 4)$ and innermost multiplicity $c_z = 2$), every $M \in \mathcal{T}_S(\mathcal{V})$ satisfies $(M)_\lambda \in \mathcal{I}_S$ with $|M| + \#_\lambda((M)_\lambda) = \mathrm{vl}((M)_\lambda)$ and $\#_v((M)_\lambda) = \#_v(M)$.

For any root $\beta$-step $(\lambda z.\, P)\,Q \to_\beta P[z := Q]$ inside $\mathcal{I}_S$, writing $c := c_z(P) = d + 1$ ($d \ge 0$) gives $\mathrm{vl}(P[z := Q]) + c = \mathrm{vl}(P) + c\,\mathrm{vl}(Q)$, $\#_\lambda(P[z := Q]) = \#_\lambda(P) + c\,\#_\lambda(Q)$, and $\#_v(P[z := Q]) = \#_v(P) + c\,\#_v(Q) \ge \#_v(P) + \#_v(Q)$. Subtracting the binder count from the variable-leaf count yields

$$
\bigl(\mathrm{vl}(P[z := Q]) - \#_\lambda(P[z := Q])\bigr) - \bigl(\mathrm{vl}((\lambda z.\, P)\,Q) - \#_\lambda((\lambda z.\, P)\,Q)\bigr) \;=\; d\,\bigl(\mathrm{vl}(Q) - \#_\lambda(Q) - 1\bigr) \;\ge\; 0,
$$

and $\mathcal{I}_S$ is preserved under substitution and contextual $\beta$-steps. Induction along $(M)_\lambda \to_\beta^* B$ therefore yields, for every $M \in \mathcal{T}_S(\mathcal{V})$,

$$
|M| + \#_\lambda(B) \;\le\; \mathrm{vl}(B), \qquad \#_v(M) \;\le\; \#_v(B) \quad (v \in \mathcal{V}). \tag{7.16}
$$

From (7.16) we obtain constructive $\mathrm{CL}(S)$ normal-form extraction: whenever $(M)_\lambda \to_\beta^* B$ with $B \in \NF_\beta$, there exists $N \in \mathrm{NF}$ such that $M \to_S^* N$ and $(N)_\lambda \to_\beta^* B$. Indeed, if $M \notin \mathrm{NF}$, picking any step $M \to_S M'$ gives $(M)_\lambda \to_\beta^+ (M')_\lambda$, and confluence of $\to_\beta^*$ with $B \in \NF_\beta$ forces $(M')_\lambda \to_\beta^* B$, whence $|M'| \le \mathrm{vl}(B)$ by (7.16). By Proposition 2.2(ii) and Theorem 2.3(i), each step $M \to_S M'$ either strictly decreases $\mathrm{vl}(B) - |M| \in \mathbb{N}$ (when $|M| < |M'|$) or preserves $|M'| = |M|$ while strictly decreasing Bergstra's weight $\|M\|_{\mathrm{B}}$ by at least $6$, so well-founded induction on $(\mathrm{vl}(B) - |M|, \|M\|_{\mathrm{B}}) \in \mathbb{N}^2$ reaches $N \in \mathrm{NF}$ with $(N)_\lambda \to_\beta^* B$.

Now let $F$ be $S$-free and suppose $(F)_\lambda =_\beta (M)_\lambda$. Because $(F)_\lambda \equiv F$ contains no $\lambda$-binders, $(F)_\lambda \in \NF_\beta$, so confluence gives $(M)_\lambda \to_\beta^* (F)_\lambda$ and normal-form extraction gives $M \to_S^* N \in \mathrm{NF}$ with $(N)_\lambda \to_\beta^* (F)_\lambda$. If $\mathrm{hd}(N) = S$, then $N \in \mathcal{P}_S$ reduces in $0, 1$, or $2$ weak-head $\beta$-steps to an abstraction, which is preserved under $\to_\beta^*$ and contradicts $(F)_\lambda$ not being an abstraction. Hence $\mathrm{hd}(N) \in \mathcal{V}$, so $(N)_\lambda$ has a neutral free-variable head that never creates a root $\beta$-redex: structural induction on $F$ immediately forces $N \equiv F$, establishing $M \to_S^* F$.

For (ii), computing the $\beta$-normal forms $B_{M_0}$ of $M_0 \in \{S, T, A\}$ gives $(\#_\lambda, \mathrm{vl}) = (3, 4)$ for $S$, $(3, 5)$ for $T$ ($B_T \equiv \lambda y z w.\, (z w)((y z) w)$), and $(3, 6)$ for $A$ ($B_A \equiv \lambda z w.\, (z w)(\lambda w'.\, (z w')(w w'))$). Whenever $(M_0)_\lambda =_\beta (N)_\lambda$ for $N \in \mathcal{T}_S(\mathcal{V})$, normal-form extraction and (7.16) yield $N \to_S^* N_0 \in \mathrm{NF}$ with $\#_v(N_0) \le \#_v(B_{M_0}) = 0$ (so $N_0 \in \mathcal{T}_S$ is closed) and $|N_0| \le \mathrm{vl}(B_{M_0}) - \#_\lambda(B_{M_0}) \in \{1, 2, 3\}$; comparing the distinct $\beta$-normal forms of closed normal forms up to size $3$ ($S, T, A$, and $S T$ whose $\beta$-normal form has three top-level $\lambda$-abstractions unlike $B_A$) forces $N_0 \equiv M_0$. Likewise, because the minimum leaf size in $\mathcal{T}_S \cap \mathrm{SN} \setminus L_{34}$ is $|W_9| = 9 > 7$ (Proposition 7.4(iii)), every $M \in \mathcal{T}_S \cap \mathrm{SN}$ with $|M| \le 7$ has a closed $\beta$-normal form $B_M$ satisfying $\mathrm{vl}(B_M) - \#_\lambda(B_M) \le 7$; any $N \in \mathcal{T}_S(\mathcal{V})$ with $(M)_\lambda =_\beta (N)_\lambda$ reduces in $\mathrm{CL}(S)$ to a closed normal form of size at most $7$, and the $89$ closed pure-$S$ normal forms of size at most $7$ have pairwise distinct $\beta$-normal forms, forcing $N =_S M$. The only two non-$\mathrm{SN}$ closed terms of size $7$, $S T S S S S$ and $A T S S$, satisfy $S T S S S S \to_S A T S S$ and have non-normalizing $\lambda$-translations, so $=_\beta$ and $=_S$ coincide across all $197$ closed terms of size at most $7$.

For (7.14), pick a fresh variable $z \in \mathcal{V}$ not occurring in $x, y$. Five contractions in $\mathrm{CL}(S)$ give

$$
\begin{aligned}
L(x, y)\,z &\;\to_S\; (S T y z)(S x y z) \;\to_S^2\; \bigl((T z)(y z)\bigr)\bigl((x z)(y z)\bigr) \\
  &\;\to_S\; \Bigl(S\,(y z)\,\bigl(z\,(y z)\bigr)\Bigr)\bigl((x z)(y z)\bigr) \;\to_S\; \Bigl((y z)\,\bigl((x z)(y z)\bigr)\Bigr)\Bigl(\bigl(z\,(y z)\bigr)\,\bigl((x z)(y z)\bigr)\Bigr),
\end{aligned}
$$

while six contractions give

$$
\begin{aligned}
R(x, y)\,z &\;\to_S\; \bigl(S y (S x y) z\bigr)\bigl(S(T x) y z\bigr) \;\to_S^4\; \Bigl((y z)\,\bigl((x z)(y z)\bigr)\Bigr)\Bigl(\bigl((S z)(x z)\bigr)\,(y z)\Bigr) \\
  &\;\to_S\; \Bigl((y z)\,\bigl((x z)(y z)\bigr)\Bigr)\Bigl(\bigl(z\,(y z)\bigr)\,\bigl((x z)(y z)\bigr)\Bigr),
\end{aligned}
$$

so $L(x, y)\,z =_S R(x, y)\,z$. Abstracting the fresh variable $z$ via $(S P Q)_\lambda \to_\beta^2 \lambda z.\, ((P)_\lambda z)((Q)_\lambda z)$ yields $(L(x, y))_\lambda =_\beta (R(x, y))_\lambda$. Direct subterm inspection shows that $L(x, y)$ (for $x, y \in \mathcal{V}$) and $U_1 \equiv L(S, S)$ have spine length at most $2$ everywhere and unequal right arguments ($4$ leaves versus $1$ leaf) at their sole two-application node, making both isolated normal forms. Finally, among the $3{,}562$ closed normal forms of size at most $11$, $25$ lie outside $L_{34}$ ($4$ of size $10$ and $21$ of size $11$, pairwise $\beta$-inconvertible via distinct finite Böhm-tree prefixes and $\beta$-inconvertible to every term in $L_{34}$), and pairwise comparison of the $\beta$-normal forms of the remaining $3{,}537$ closed normal forms yields $\mathrm{nf}_\beta((U_1)_\lambda) \equiv \mathrm{nf}_\beta((U_2)_\lambda)$ as the unique collision. $\square$

Proposition 7.8 shows that adjoining $U_1 = U_2$ (or even $L(x, y) = R(x, y)$) repairs all discrepancies up to $11$ leaves, yet tower-delayed distributivity generates infinitely many independent equational gaps at unbounded depths. For any $U \in \mathcal{T}_S(\mathcal{V})$ and $k \in \mathbb{N}$, define the right-nested unary $S$-tower recursively by $S^0(U) \equiv U$ and $S^{k+1}(U) \equiv S(S^k(U))$ ($|S^k(U)| = k + |U|$), and for each $m \in \mathbb{N}$ and $Y \in \mathcal{T}_S(\mathcal{V})$ set

$$
\begin{aligned}
  M_m(Y) &\;\equiv\; S\,\Bigl(S\,\bigl(S^{m+1}(T)\bigr)\,Y\Bigr)\,\Bigl(S\,\bigl(S^m(T)\bigr)\,Y\Bigr), \\
  N_m(Y) &\;\equiv\; S\,\Bigl(S\,\bigl(S^m(T T)\bigr)\,Y\Bigr)\,\Bigl(S\,\bigl(S^{m+1}(A)\bigr)\,Y\Bigr).
\end{aligned} \tag{7.17}
$$

When $Y \equiv y \in \mathcal{V}$ (or $Y \equiv S$), $|M_m(Y)| = 2m + 10$ whereas $|N_m(Y)| = 2m + 13$. Combining $S$-free probe rigidity, exact finite backward reduction cones, and deep $T$-core variable abstraction yields the negative resolution of Open Question 32.

**Theorem 7.9 (Equational non-finite axiomatizability of $\lambda\beta$-equality and negative resolution of Question 32).**
Let $\mathcal{E} = \{P_1 = Q_1, \dots, P_r = Q_r\} \subset \mathcal{T}_S(\mathcal{V}) \times \mathcal{T}_S(\mathcal{V})$ ($r \ge 0$) be any finite $\lambda\beta$-sound set of schematic pure-$S$ equations (allowing arbitrary free variables), and set $m := \max(\{0\} \cup \{|P_i|, |Q_i| : 1 \le i \le r\})$. For every variable $y \in \mathcal{V}$, the pair $(M_m(y), N_m(y))$ of (7.17) satisfies:

- (i) The term $M_m(y)$ is an isolated normal form of leaf size $2m + 10$, $N_m(y) \in \mathrm{NF}$ has leaf size $2m + 13$, and $(M_m(y))_\lambda =_\beta (N_m(y))_\lambda$.
- (ii) The $\mathrm{CL}(S) + \mathcal{E}$ equational class of $M_m(y)$ collapses to the singleton $\{R \in \mathcal{T}_S(\mathcal{V}) : \mathrm{CL}(S) + \mathcal{E} \vdash M_m(y) = R\} = \{M_m(y)\}$, whence $\mathrm{CL}(S) + \mathcal{E} \nvdash M_m(y) = N_m(y)$ (and if $\mathcal{E} \subset \mathcal{T}_S \times \mathcal{T}_S$ consists of closed equations, $\mathrm{CL}(S) + \mathcal{E} \nvdash M_m(S) = N_m(S)$ despite $(M_m(S))_\lambda =_\beta (N_m(S))_\lambda$).

Consequently, there exists no finite set $\mathcal{E}$ of pure-$S$ equations satisfying (7.12) for all $M, N \in \mathcal{T}_S(\mathcal{V})$, resolving Open Question 32 of Barendregt, Endrullis, Klop, and Waldmann [4, p. 94] in the negative.

*Proof.*
We divide the argument into four steps.

*Step 1: Fibonacci probe expansion and $(M_m(Y))_\lambda =_\beta (N_m(Y))_\lambda$.* For $A_0, B_0 \in \mathcal{T}_S(\mathcal{V})$, define Fibonacci applicative words by $F_0(A_0, B_0) \equiv A_0$, $F_1(A_0, B_0) \equiv B_0$, and $F_{k+2}(A_0, B_0) \equiv F_k(A_0, B_0)\,F_{k+1}(A_0, B_0)$, so $F_k(B_0, A_0 B_0) \equiv F_{k+1}(A_0, B_0)$ by induction on $k$ (cf. Lemma 6.5). Induction on $k$ from $S(S^{k'}(U)) A_0 B_0 \to_S S^{k'}(U)\,B_0\,(A_0 B_0)$ gives $S^k(U)\,A_0\,B_0 \to_S^k U\,F_k(A_0, B_0)\,F_{k+1}(A_0, B_0)$, and one outer contraction gives $S(S^k(U))\,Y\,X \to_S^{k+1} U\,F_k(X, Y X)\,F_{k+1}(X, Y X)$. Fix a fresh variable $a \in \mathcal{V} \setminus \mathrm{FV}(Y)$, put $d_j \equiv F_j(a, Y a)$ and $E \equiv S\,d_{m+1}\,d_{m+2}$, and write $M_m(Y) \equiv S L_A R_A$ and $N_m(Y) \equiv S L_B R_B$. Applying the single-arm identity gives $L_A\,a \to_S^{m+2} T\,d_{m+1}\,d_{m+2} \to_S S\,d_{m+2}\,d_{m+3}$ and $R_A\,a \to_S^{m+1} T\,d_m\,d_{m+1} \to_S E$, whence $(L_A a)(R_A a) \to_S^* (S\,d_{m+2}\,d_{m+3})\,E \to_S (d_{m+2} E)(d_{m+3} E)$. Similarly, $L_B\,a \to_S^{m+1} (T T)\,d_m\,d_{m+1} \to_S^2 (d_m d_{m+1})(T\,d_m\,d_{m+1}) \to_S d_{m+2}\,E$ and $R_B\,a \to_S^{m+2} A\,d_{m+1}\,d_{m+2} \to_S^2 (d_{m+1} d_{m+2})(S\,d_{m+1}\,d_{m+2}) \equiv d_{m+3}\,E$, so $(L_B a)(R_B a) \to_S^* (d_{m+2} E)(d_{m+3} E)$. Abstracting the fresh variable $a$ as in Proposition 7.8(ii) yields $(M_m(Y))_\lambda =_\beta (N_m(Y))_\lambda$.

*Step 2: Isolated-subterm equational rigidity criterion.* For $y \in \mathcal{V}$, every subterm of $M_m(y)$ and $N_m(y)$ has left-spine length at most $2$, and at the root of $M_m(y) \equiv (S L_A)\,R_A$ the right arguments of $S L_A$ and $R_A$ have leaf sizes $m + 5 \ne 1 = |y|$, while all other compound subterms have left child $S$ or right child $y$; thus $M_m(y)$ is an isolated normal form. In general, for any isolated normal form $W \in \mathcal{T}_S(\mathcal{V})$ (writing $U \preceq W$ for subterms), if every $(P = Q) \in \mathcal{E}$ and substitution $\sigma$ satisfy $(P^\sigma \preceq W \implies Q^\sigma \equiv P^\sigma)$ and $(Q^\sigma \preceq W \implies P^\sigma \equiv Q^\sigma)$, structural induction on $\mathrm{CL}(S) + \mathcal{E} \vdash A = B$ proves $(A \preceq W \implies B \equiv A) \land (B \preceq W \implies A \equiv B)$ (reduction steps are vacuous on isolated subterms, and congruence steps preserve subterm containment). By symmetry of $(P = Q)$, it suffices to show that whenever $(P)_\lambda =_\beta (Q)_\lambda$, $|P| \le m$, and $P^\sigma \preceq M_m(y)$, one has $Q^\sigma \equiv P^\sigma$.

*Step 3: Finite backward-cone rigidity of proper subterms and the variable-core template.* Every subterm $U \preceq M_m(y)$ falls into six classes: (1) $S$; (2) $y$; (3) $S^j(T)$ ($0 \le j \le m + 2$); (4) $P_k \equiv S(S^k(T))y$ ($k \in \{m, m + 1\}$); (5) $S P_{m+1}$; or (6) $M_m(y)$ itself. Classes (1)–(2) are globally rigid by Proposition 7.8. For classes (3)–(5) and the two-variable core template

$$
A_{\mathrm{var}}(m + 1, u, y) \;\equiv\; S\,\Bigl(S\,\bigl(S^{m+1}(u)\bigr)\,y\Bigr)\,\Bigl(S\,\bigl(S^m(u)\bigr)\,y\Bigr) \qquad (u, y \in \mathcal{V},\; u \ne y),
$$

we prove exact syntactic rigidity ($(U)_\lambda =_\beta (R)_\lambda$ implies $R \equiv U$) via $S$-free probes. Note that for distinct variables $a, b$ (and $y, a$), the $S$-free words $F_k(a, b)$ ($k \ge 1$) and $d_k \equiv F_k(a, y a)$ ($k \ge 0$, with $k + 1 \le |d_k| < |d_{k+1}|$ and $|d_{k+1}| \ge 2$) have strictly increasing leaf counts and hence contain no co-redexes.

- For $S^k(T)$: if $(S^k(T))_\lambda =_\beta (R)_\lambda$, choose distinct $a, b, c \in \mathcal{V}$ and set $F_j \equiv F_j(a, b)$. Then $S^k(T)\,a\,b\,c \to_S^* (F_{k+1} c)(F_{k+2} c) \equiv: \Theta_1$, which is $S$-free, so $R\,a\,b\,c \to_S^* \Theta_1$ by Proposition 7.8(i). Tracing backward one-step predecessors from $\Theta_1$ (using co-redex-freeness of $F_j$ and disjointness of closed right subterms of $S^j(T)$ from variable-bearing $F_r$) closes the finite backward cone at $\mathcal{C}_1 = \{\Theta_1,\, S\,F_{k+1}\,F_{k+2}\,c\} \cup \{S^j(T)\,F_r\,F_{r+1}\,c : j + r = k\}$. Matching $R\,a\,b\,c \in \mathcal{C}_1$ against $|b| = 1$ forces $r = 0$ and $j = k$, whence $R \equiv S^k(T)$. (For closed $\mathcal{E}$, all subterms of $M_m(S)$ of size $\le m$ have the form $S$ or $S^j(T)$, already completing the closed-equation case.)
- For $P_k \equiv S(S^k(T))y$ and $S P_{m+1}$: picking distinct $a, b \in \mathcal{V} \setminus \{y\}$ gives $P_k\,a\,b \to_S^* (d_{k+1} b)(d_{k+2} b) \equiv: \Theta_2$, whose backward cone $\{\Theta_2,\, S\,d_{k+1}\,d_{k+2}\,b\} \cup \{S^j(T)\,d_r\,d_{r+1}\,b : j + r = k\} \cup \{P_k\,a\,b\}$ contains $P_k\,a\,b$ as the unique term whose second spine argument from the right has leaf size $1 = |a|$ (since $|d_{r+1}| \ge 2$), forcing $R \equiv P_k$. Likewise, for distinct $w, a \in \mathcal{V} \setminus \{y\}$ with $B \equiv w a$, $(S P_{m+1})\,w\,a \to_S^* (d_{m+2} B)(d_{m+3} B) \equiv: \Theta_3$ has backward cone $\{\Theta_3,\, S\,d_{m+2}\,d_{m+3}\,B\} \cup \{S^j(T)\,d_r\,d_{r+1}\,B : j + r = m + 1\} \cup \{(P_{m+1} a)\,B,\, (S P_{m+1})\,w\,a\}$, where only $(S P_{m+1})\,w\,a$ has outer right argument of leaf size $1 = |a| < 2 = |B|$, forcing $R \equiv S P_{m+1}$.
- For $A_{\mathrm{var}}(m + 1, u, y)$ ($u \ne y$): picking fresh $a \notin \{u, y\}$ gives $A_{\mathrm{var}}(m + 1, u, y)\,a \to_S^{2m+4} ((u\,d_{m+1})\,d_{m+2})((u\,d_m)\,d_{m+1}) \equiv: \Theta_4$, so $(A_{\mathrm{var}}(m + 1, u, y))_\lambda =_\beta (R)_\lambda$ implies $R\,a \to_S^* \Theta_4$. Since $u$ occurs in $S^j(u)$ and never in $d_r$, each arm $(u\,d_k)\,d_{k+1}$ has backward cone $\mathcal{D}_k = \{S(S^k(u))\,y\,a\} \cup \{(S^j(u)\,d_r)\,d_{r+1} : j + r = k\}$ (all of leaf size $\ge 4$). Root-uncontracting $X_L \cdot X_R \in \mathcal{D}_{m+1} \cdot \mathcal{D}_m$ requires identical right arguments, yielding only $A_{\mathrm{var}}(m + 1, u, y)\,a$ (at shared argument $a$) and $\{S(S^{m+1-r}(u)\,d_r)(S^{m-r}(u)\,d_r)\,d_{r+1} : 0 \le r \le m\}$ (at shared argument $d_{r+1}$, by injectivity of $r \mapsto |d_{r+1}|$), none of which contains a co-redex. Among this closed backward cone $\mathcal{C}_4$, only $A_{\mathrm{var}}(m + 1, u, y)\,a$ has outer right argument of size $1 = |a|$, forcing $R \equiv A_{\mathrm{var}}(m + 1, u, y)$.

*Step 4: Deep $T$-core variable abstraction at the root.* Finally, suppose $(P)_\lambda =_\beta (Q)_\lambda$, $|P| \le m$, and $P^\sigma \equiv M_m(y)$ at the root. Choose two distinct fresh variables $x_0, x_2 \in \mathcal{V} \setminus \{y\}$ (so $x_0 \notin \mathrm{FV}(M_m(y))$ and $x_2 \notin \{x_0, y\}$). Define the $T$-core replacement map $\rho_{x_0} \colon \mathcal{T}_S(\mathcal{V}) \to \mathcal{T}_S(\mathcal{V})$ recursively by $\rho_{x_0}(S) \equiv S$, $\rho_{x_0}(v) \equiv v$, $\rho_{x_0}(S S) \equiv x_0$, and $\rho_{x_0}(A B) \equiv \rho_{x_0}(A)\,\rho_{x_0}(B)$ whenever $A B \not\equiv S S$. The only subterms of $M_m(y)$ literally equal to $S S$ are the two $T$-cores at the bottoms of the two $S$-towers, which sit at binary application depths $m + 4$ and $m + 3$ from the root of $M_m(y)$, so $\rho_{x_0}(M_m(y)) \equiv A_{\mathrm{var}}(m + 1, x_0, y)$. Because $|P| \le m < m + 3$, every internal application node of the pattern $P$ lies at depth at most $|P| - 1 < m$, so no application node of $P$ can assemble $S S$ in $P^\sigma \equiv M_m(y)$; both $T$-cores lie strictly inside substitution images $\sigma(v)$, giving $\rho_{x_0}(P^\sigma) \equiv P^{\tau_0}$ where $\tau_0(v) \equiv \rho_{x_0}(\sigma(v))$.

Define the modified substitution $\tau \colon \mathcal{V} \to \mathcal{T}_S(\mathcal{V})$ by $\tau(v) \equiv \rho_{x_0}(\sigma(v))$ for $v \in \mathrm{FV}(P)$ and $\tau(v) \equiv x_2$ for $v \notin \mathrm{FV}(P)$. Then $P^\tau \equiv P^{\tau_0} \equiv \rho_{x_0}(M_m(y)) \equiv A_{\mathrm{var}}(m + 1, x_0, y)$, and substitution invariance of $=_\beta$ gives $(A_{\mathrm{var}}(m + 1, x_0, y))_\lambda \equiv (P^\tau)_\lambda =_\beta (Q^\tau)_\lambda$. By Step 3, syntactic rigidity of $A_{\mathrm{var}}(m + 1, x_0, y)$ forces $Q^\tau \equiv A_{\mathrm{var}}(m + 1, x_0, y)$. Because $x_2$ does not occur in $A_{\mathrm{var}}(m + 1, x_0, y)$, this immediately implies $\mathrm{FV}(Q) \subseteq \mathrm{FV}(P)$. Letting $\psi \colon \mathcal{V} \to \mathcal{T}_S(\mathcal{V})$ be the restoration substitution mapping $x_0 \mapsto T \equiv S S$ and fixing all other variables, every $v \in \mathrm{FV}(Q) \subseteq \mathrm{FV}(P)$ satisfies $x_0 \notin \mathrm{FV}(\sigma(v))$ (as $\sigma(v) \preceq M_m(y)$) and hence $(\rho_{x_0}(\sigma(v)))^\psi \equiv \sigma(v)$. Applying $\psi$ to $Q^\tau \equiv A_{\mathrm{var}}(m + 1, x_0, y)$ yields

$$
Q^\sigma \;\equiv\; (Q^\tau)^\psi \;\equiv\; \bigl(A_{\mathrm{var}}(m + 1, x_0, y)\bigr)^\psi \;\equiv\; M_m(y) \;\equiv\; P^\sigma.
$$

By Step 2, $[M_m(y)]_{\mathrm{CL}(S) + \mathcal{E}} = \{M_m(y)\}$, and since $|N_m(y)| = 2m + 13 \ne 2m + 10 = |M_m(y)|$, we conclude $\mathrm{CL}(S) + \mathcal{E} \nvdash M_m(y) = N_m(y)$. Finally, any $\mathcal{E}$ satisfying (7.12) is necessarily $\lambda\beta$-sound (taking identity substitutions), contradicting $(M_m(y))_\lambda =_\beta (N_m(y))_\lambda$. $\square$

## 8. Fixed-Order Dynamics, Super-Pushdown Traces, and Clone-Theoretic Cellular Barriers

Fixed deterministic reduction strategies—leftmost-outermost ($\to_{\mathrm{lo}}$), rightmost-outermost ($\to_{\mathrm{ro}}$), leftmost-innermost ($\to_{\mathrm{li}}$), rightmost-innermost ($\to_{\mathrm{ri}}$), shallowest-leftmost breadth-first ($\to_{\mathrm{bfs}}$), and Gross–Knuth parallel reduction ($\to_{\mathrm{gk}}$)—govern step-by-step evaluation in $\mathrm{CL}(S)$, while clone-theoretic monotonicity separates the semantic $S$-algebras $\mathcal{A}_{\mathrm{HN}}$, $\mathcal{A}_{\mathrm{SN}}$, and $\mathcal{A}_P$ from normal-form cellular computation.

### 8.1. Pure-Line Strategy Coincidence, Quadratic Automaton Traces, and Innermost $A A A$

Let $\#\mathrm{Redex}(M) \in \mathbb{N}$ denote the number of redex occurrences $S X Y Z$ in $M$, and let $\mathcal{N}_2 = \{ S X Y : X, Y \in \mathcal{N} \} \subset \mathcal{N}$ denote the set of Spine-$2$ closed normal forms. Following [4], a term $M$ is *pure-line* along a trajectory if every visited reduct satisfies $\#\mathrm{Redex}(M_t) = 1$.

**Proposition 8.1 (Pure-line six-strategy coincidence, quadratic traces, and innermost $A A A$).**

- (i) *(Six-strategy coincidence on single-redex terms)* For every $M \in \mathcal{T}_S(\mathcal{V})$ satisfying $\#\mathrm{Redex}(M) = 1$, all six deterministic evaluators $\to_{\mathrm{lo}}, \to_{\mathrm{ro}}, \to_{\mathrm{li}}, \to_{\mathrm{ri}}, \to_{\mathrm{bfs}}, \to_{\mathrm{gk}}$ select the unique redex of $M$ and yield the identical one-step reduct $M'$.
- (ii) *(Super-pushdown quadratic checkpoint language on $Z_{\mathrm{Zac}}$)* Along the reduction sequence $Z_{\mathrm{Zac}} = T_0 \to T_1 \to T_2 \to \cdots$ starting from Zachos's $10$-leaf combinator $Z_{\mathrm{Zac}} \equiv G_0 G_0 \equiv (S T T)(S T T)$, every reduct $T_t$ satisfies $\#\mathrm{Redex}(T_t) = 1$ (so all six strategies generate the identical infinite sequence $(T_t)_{t \ge 0}$). Moreover, there is an explicit $8$-state deterministic bottom-up tree automaton $\mathcal{B}_Z = (\{b_0, \dots, b_7\}, b_0, \odot_{\mathcal{B}_Z}, \{b_6\})$ such that for all $t \in \mathbb{N}$, 
$$
\llbracket T_t \rrbracket_{\mathcal{B}_Z} = b_6
\;\Longleftrightarrow\;
t \in \Bigl\{ \frac{n(n+3)}{2} : n \in \mathbb{N} \Bigr\}
\;=\; \{0, 2, 5, 9, 14, 20, 27, \dots\} \tag{8.1}
$$
 (shifted by $+1$ to the triangular numbers $\binom{n+2}{2} = \{1, 3, 6, 10, 15, \dots\}$ when starting from the $9$-leaf precursor $Z_0 \equiv S(S T)(S T)T$, while on $D_{\mathrm{seed}} \equiv Z_0 S$ an explicit $68$-state automaton $\mathcal{B}_{\mathrm{quad}}$ recognizes $\{2n^2 + 3n + 1 : n \in \mathbb{N}\}$ under $\to_{\mathrm{lo}}$). By Parikh's theorem [47], the unary trace language $\{ 1^t : \llbracket T_t \rrbracket_{\mathcal{B}_Z} = b_6 \}$ is not context-free and cannot be generated by any pushdown or one-counter machine.
- (iii) *(Closed-form exponential size growth of $A A A$ under $\to_{\mathrm{li}}$, versus $\to_{\mathrm{ro}}$ trapping)* Under rightmost-outermost reduction $\to_{\mathrm{ro}}$, any non-root-redex application $L R$ with $R \in \mathcal{T}_S \setminus \mathrm{SN}$ traps forever on the right: $(L R)_t \equiv L\,R_t$ for all $t \ge 0$. Under leftmost-innermost reduction $\to_{\mathrm{li}}$, every non-normalizing closed term reduces once its minimal leftmost-innermost $\infty_{\mathrm{SN}}$-subterm freezes its outer context to iterating the normal-form map $F_{\mathrm{li}} : \mathcal{N}_2 \times \mathcal{N} \to \mathcal{N}_2 \times \mathcal{N}$ on critical pairs $(L, Z)$ ($\llbracket L Z \rrbracket_{\mathrm{SN}} = \infty_{\mathrm{SN}}$). For $A A A \equiv (S S S)(S S S)(S S S)$, setting $M_1 \equiv S A A$, $H_0 \equiv S A M_1$, and $H_{n+1} \equiv S H_n (S H_n) \in \mathcal{N}_2$ ($n \ge 0$), a $4$-macro-step transient from $(S A (S A), A)$ reaches $(H_1, H_1)$, after which every cycle $n \ge 1$ executes the $(n+2)$-macro-step loop $(H_n, H_n) \mapsto^n (H_0, H_n) \mapsto (M_1, H_n) \mapsto (H_{n+1}, H_{n+1})$ with exact exponential leaf count $|H_n| = 13 \cdot 2^n - 2$.

*Proof.* 
For (i), structural induction on $M$ shows that $\#\mathrm{Redex}(M) = 0$ if and only if $M \in \mathrm{NF}$, on which every strategy is idle ($\mathrm{gk}(M) = M$). When $\#\mathrm{Redex}(M) = 1$, either $M \equiv S X Y Z$ is itself a root redex with $X, Y, Z \in \mathrm{NF}$—where $\to_{\mathrm{lo}}, \to_{\mathrm{ro}}, \to_{\mathrm{bfs}}$ contract the root directly, $\to_{\mathrm{li}}, \to_{\mathrm{ri}}$ find $S X Y, Z \in \mathrm{NF}$ and contract the root, and $\mathrm{gk}(S X Y Z) = (\mathrm{gk}(X)\,\mathrm{gk}(Z))(\mathrm{gk}(Y)\,\mathrm{gk}(Z)) = (X Z)(Y Z)$—or $M \equiv L R$ is not a root redex and $(\#\mathrm{Redex}(L), \#\mathrm{Redex}(R)) \in \{(1, 0), (0, 1)\}$, where the idle child contains no redexes and the induction hypothesis equates all six evaluators on the active child.

For (ii), recall $G_0 \equiv S T T$ and $G_{k+1} \equiv T G_k$, which contain no redexes ($\#\mathrm{Redex}(G_k) = 0$), whereas $\#\mathrm{Redex}(G_k G_m) = 1$ for all $k, m \in \mathbb{N}$ (at the root $S T T G_m$ when $k = 0$, and at $S S G_{k-1} G_m$ when $k \ge 1$). For any sequence of indices $\vec{m} = (m_1, \dots, m_r)$, define the normal-form wrapper $W_{\vec{m}}(C) \equiv S G_{m_1} (S G_{m_2} (\cdots (S G_{m_r} C)\cdots))$; since $\#\mathrm{Redex}(S G_m) = 0$ and $\mathrm{ls}(S G_m C) = 2$, we have $\#\mathrm{Redex}(W_{\vec{m}}(C)) = \#\mathrm{Redex}(C)$. Starting at $W_{\vec{m}}(G_0 G_n)$, one contraction yields $W_{\vec{m}}(G_{n+1} G_{n+1})$, and $n + 1$ subsequent contractions $G_{k+1} G_{n+1} \equiv S S G_k G_{n+1} \to_S S G_{n+1} (G_k G_{n+1})$ ($k = n, \dots, 0$) yield $W_{\vec{m} \cdot (n+1)^{n+1}}(G_0 G_{n+1})$ in $(n + 2)$ steps total. Summing $\sum_{j=0}^{n-1} (j + 2) = \frac{1}{2}n(n+3)$ from $T_0 \equiv G_0 G_0$ ($n = 0$, empty $\vec{m}$) shows $\#\mathrm{Redex}(T_t) = 1$ for all $t \ge 0$, with $T_{n(n+3)/2} \equiv W_{\vec{\mu}_n}(G_0 G_n)$ and intermediate steps $T_{n(n+3)/2 + j} \equiv W_{\vec{\mu}'}(G_{n+2-j} G_{n+1})$ ($1 \le j \le n + 1$). Define $\odot_{\mathcal{B}_Z}$ on $\{b_0, \dots, b_7\}$ by $b_0 \odot b_0 = b_1$ ($T$), $b_0 \odot b_1 = b_2$ ($S T$), $b_2 \odot b_1 = b_3$ ($G_0$), $b_1 \odot b_3 = b_1 \odot b_4 = b_4$ ($G_{k+1}$ for $k \ge 0$), $b_0 \odot b_3 = b_0 \odot b_4 = b_5$ ($S G_m$), $b_3 \odot b_3 = b_3 \odot b_4 = b_6$ ($G_0 G_n$), $b_5 \odot b_6 = b_6$ (preserving $b_6$ across $W_{\vec{m}}$), and $b_7$ elsewhere (so $G_{k+1} G_m \mapsto b_4 \odot b_{3,4} = b_7$ and $b_5 \odot b_7 = b_7$). Then $\llbracket T_t \rrbracket_{\mathcal{B}_Z} = b_6$ holds if and only if the core is $G_0 G_n$, proving (8.1). Because consecutive gaps $\frac{1}{2}(n+1)(n+4) - \frac{1}{2}n(n+3) = n + 2 \to \infty$ are unbounded while the set is infinite, $\{ \frac{1}{2}n(n+3) : n \in \mathbb{N} \}$ is not a finite union of arithmetic progressions (not semilinear); by Parikh's theorem [47], $\{ 1^t : \llbracket T_t \rrbracket_{\mathcal{B}_Z} = b_6 \}$ is not context-free.

For (iii), if $L R$ is not a root redex and $R \in \mathcal{T}_S \setminus \mathrm{SN}$, Theorem 6.2 ensures $R$ is not in normal form, so $\to_{\mathrm{ro}}$ steps inside $R \to_{\mathrm{ro}} R'$ while preserving non-root-redex shape and $\llbracket R' \rrbracket_{\mathrm{SN}} = \infty_{\mathrm{SN}}$ inductively. Under $\to_{\mathrm{li}}$, $A A A \equiv ((S S S) A) A \to_{\mathrm{li}} (S A (S A)) A$ reaches the critical pair $(L_0, Z_0) = (S A (S A), A)$ with $\llbracket L_0 \rrbracket_{\mathrm{SN}} = q_{29}$, $\llbracket A \rrbracket_{\mathrm{SN}} = q_7$, and $q_{29} \odot_{\mathrm{SN}} q_7 = \infty_{\mathrm{SN}}$. Since $A U \equiv S S S U \to_{\mathrm{li}} S U (S U) \in \mathcal{N}_2$ for every $U \in \mathcal{N}$, induction on $k \ge 0$ gives $\llbracket H_0 \rrbracket_{\mathrm{SN}} = q_{29}$ and $\llbracket H_{k+1} \rrbracket_{\mathrm{SN}} = q_{30}$ (from $\llbracket M_1 \rrbracket_{\mathrm{SN}} = q_{34}$, $\llbracket H_0 \rrbracket_{\mathrm{SN}} = (q_0 \odot_{\mathrm{SN}} q_7) \odot_{\mathrm{SN}} q_{34} = q_{29}$, and $q_0 \odot_{\mathrm{SN}} q_{29} = q_0 \odot_{\mathrm{SN}} q_{30} = q_6$ with $q_6 \odot_{\mathrm{SN}} q_6 = q_{30}$), while $\{q_{29}, q_{30}\} \odot_{\mathrm{SN}} \{q_{29}, q_{30}\} = \{\infty_{\mathrm{SN}}\}$ and $q_{34} \odot_{\mathrm{SN}} \{q_{29}, q_{30}\} = \{\infty_{\mathrm{SN}}\}$. After $(S A (S A), A) \mapsto (S A (S A), M_1) \mapsto (S M_1 (S M_1), H_0) \mapsto (M_1, H_0) \mapsto (H_1, H_1)$, each $(H_k, H_n)$ with $k, n \ge 1$ has left contraction child $H_{k-1} H_n$ of state $\llbracket H_{k-1} \rrbracket_{\mathrm{SN}} \odot_{\mathrm{SN}} q_{30} = \infty_{\mathrm{SN}}$ (Case 1, peeling $H_k \mapsto H_{k-1}$ in $n$ steps to $(H_0, H_n)$); at $(H_0, H_n) = (S A M_1, H_n)$, the left contraction child satisfies $A H_n \to_{\mathrm{li}} H_{n+1} \in \mathcal{N} \subseteq \mathrm{SN}$ while $M_1 H_n$ has state $q_{34} \odot_{\mathrm{SN}} q_{30} = \infty_{\mathrm{SN}}$ (Case 2, advancing to $(M_1, H_n) = (S A A, H_n)$); and at $(S A A, H_n)$, both $A H_n$ children normalize in one step to $H_{n+1}$, yielding $(H_{n+1}, H_{n+1})$ (Case 3). Finally, $|H_0| = 1 + 3 + (1 + 3 + 3) = 11$ and $|H_{n+1}| = 2|H_n| + 2$, solving to $|H_n| = 13 \cdot 2^n - 2$.
 $\square$

### 8.2. The Sharp Five-Step Innermost Case-3 Ceiling

Along any innermost reduction ($\to_{\mathrm{li}}$ or $\to_{\mathrm{ri}}$) of a non-normalizing closed $S$-term, each macro-step on the active critical pair $(L, Z) \in \mathcal{N}_2 \times \mathcal{N}$ ($L \equiv S X Y$, $\llbracket L Z \rrbracket_{\mathrm{SN}} = \infty_{\mathrm{SN}}$) falls into Case 1 ($\llbracket X Z \rrbracket_{\mathrm{SN}} = \infty_{\mathrm{SN}}$, descending to $(X, Z)$), Case 2 ($\llbracket X Z \rrbracket_{\mathrm{SN}} \neq \infty_{\mathrm{SN}}$ and $\llbracket Y Z \rrbracket_{\mathrm{SN}} = \infty_{\mathrm{SN}}$, descending to $(Y, Z)$ under $\to_{\mathrm{li}}$), or *Case 3*, in which both $X Z$ and $Y Z$ are strongly normalizing—normalizing to $L' = \mathrm{nf}(X Z) \in \mathcal{N}_2$ and $Z' = \mathrm{nf}(Y Z) \in \mathcal{N}$—while $\llbracket L' Z' \rrbracket_{\mathrm{SN}} = \infty_{\mathrm{SN}}$. By global top-termination (Theorem 6.9), Case 3 cannot occur infinitely many times consecutively, because consecutive Case 3 steps contract repeatedly at the root of the fixed minimal non-$\mathrm{SN}$ locus without descending into a proper subterm. Although the abstract Case-3 transition graph over state pairs $(u, v) \in F_{\mathrm{SN}}^2$ contains directed cycles—such as $(q_{25}, q_{25}) \to (q_{25}, q_{30}) \to (q_{30}, q_{30}) \to (q_{30}, q_6) \to (q_{29}, q_{25}) \to (q_{25}, q_{25})$—refining $L$ by a two-level normal-form descriptor yields a universal uniform bound of $5$ consecutive Case-3 steps across all of $\mathrm{CL}(S)$, dropping to $3$ asymptotically.

**Theorem 8.2 (Sharp consecutive Case-3 ceiling under $\to_{\mathrm{li}}$ and $\to_{\mathrm{ri}}$).** 
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

### 8.3. Post's Lattice Monotonicity versus Minimal Normal-Form Rule 110

We next examine whether a fixed open $S$-polynomial $P(x_1, \dots, x_k)$ built from $S$ and variables $x_1, \dots, x_k$ can evaluate Boolean logic or evolve a universal one-dimensional cellular automaton such as Cook's universal, $\mathrm{P}$-complete elementary cellular automaton Rule 110 [18, 46, 68] over two distinguished closed equivalence classes of $\mathrm{CL}(S)$. Using Post's functional completeness theorem and lattice of Boolean clones [49], we establish a sharp algebraic dichotomy: inside the semantic $S$-algebras $\mathcal{A}_{\mathrm{HN}}$, $\mathcal{A}_{\mathrm{SN}}$, and $\mathcal{A}_P$, compatible partial orders confine all induced Boolean operations to Post's monotone clone $M$, forbidding negation and Rule 110; yet over a dedicated $4$-state conversion-invariant $S$-algebra $\mathcal{D}_4$ (Table 7), non-monotonicity emerges cleanly and yields a globally minimal $11$-leaf normal-form Rule 110 combinator.

**Table 7.** Multiplication table of the $4$-state functionally complete $S$-algebra $\mathcal{D}_4 = (\{d_0, d_1, d_2, d_3\}, d_0, \odot_{\mathcal{D}_4})$ and minimal normal-form ground representatives.

| $\odot_{\mathcal{D}_4}$ | $d_0$ | $d_1$ | $d_2$ | $d_3$ | Minimal Representative | Boolean / Algebraic Role |
| :---: | :---: | :---: | :---: | :---: | :--- | :--- |
| $d_0$ | $d_1$ | $d_1$ | $d_1$ | $d_2$ | $S$ ($1$ leaf, $\mathcal{N}$) | Generator $d_0 = \llbracket S \rrbracket_{\mathcal{D}_4}$ |
| $d_1$ | $d_3$ | $d_3$ | $d_3$ | $d_3$ | $S S$ ($2$ leaves, Spine-$1$ $\mathcal{N}$) | Encoded Boolean $\mathsf{false}$ ($0$) |
| $d_2$ | $d_1$ | $d_1$ | $d_3$ | $d_3$ | $S(S S S)$ ($4$ leaves, Spine-$1$ $\mathcal{N}$) | Encoded Boolean $\mathsf{true}$ ($1$) |
| $d_3$ | $d_3$ | $d_3$ | $d_3$ | $d_3$ | $S S S$ ($3$ leaves, Spine-$2$ $\mathcal{N}$) | Auxiliary absorbing mediator |

**Theorem 8.3 (Post's lattice monotonicity barrier and minimal $11$-leaf normal-form Rule 110).**

- (i) *(Monotone-clone barrier in $\mathcal{A}_{\mathrm{HN}}, \mathcal{A}_{\mathrm{SN}}, \mathcal{A}_P$)* Each of $\mathcal{A}_{\mathrm{HN}}$, $\mathcal{A}_{\mathrm{SN}}$, and $\mathcal{A}_P$ admits non-trivial compatible preorders $\sqsubseteq$ satisfying $x_1 \odot y_1 \sqsubseteq x_2 \odot y_2$ whenever $x_1 \sqsubseteq x_2$ and $y_1 \sqsubseteq y_2$ ($6$ non-trivial compatible preorders on $\mathcal{A}_{\mathrm{HN}}$, and $5$ each on $\mathcal{A}_{\mathrm{SN}}$ and $\mathcal{A}_P$). Across every pair of distinct states $(e_0, e_1)$ in $\mathcal{A}_{\mathrm{HN}}$, $\mathcal{A}_{\mathrm{SN}}$, or $\mathcal{A}_P$, every open $S$-polynomial $P(x_1, \dots, x_k)$ mapping $\{e_0, e_1\}^k$ into $\{e_0, e_1\}$ computes a monotone Boolean function belonging to Post's clone $M$ [49]; in particular, none of $\mathrm{NOT}$, $\mathrm{NAND}$, $\mathrm{XOR}$, or Rule 110 is polynomial-definable over any $2$-state encoding in $\mathcal{A}_{\mathrm{HN}}$, $\mathcal{A}_{\mathrm{SN}}$, or $\mathcal{A}_P$.
- (ii) *(Functional completeness of $\mathcal{D}_4$ and minimal $11$-leaf normal-form Rule 110)* The $4$-state structure $\mathcal{D}_4$ of Table 7 is a conversion-invariant $S$-algebra satisfying (2.3) on all $64$ triples, breaking monotonicity via $d_0 \odot_{\mathcal{D}_4} d_3 = d_2 \neq d_1 = d_0 \odot_{\mathcal{D}_4} d_1$. Encoding $\mathsf{false}$ by $F_{\flat} \equiv S S$ ($\llbracket F_{\flat} \rrbracket_{\mathcal{D}_4} = d_1$) and $\mathsf{true}$ by $T_{\sharp} \equiv S(S S S)$ ($\llbracket T_{\sharp} \rrbracket_{\mathcal{D}_4} = d_2$), the $4$-leaf polynomial $\mathrm{NAND}(x, y) \equiv S(x(y S))$ realizes Boolean $\mathrm{NAND}$ on $\{d_1, d_2\}$, and the $11$-leaf polynomial 
$$
R_{110}(x, y, z) \;\equiv\; S\Bigl(S(y\,x)\Bigl(S(y\,z)\bigl(S(z\,y)\,S\bigr)\Bigr)\Bigr) \tag{8.2}
$$
 evaluates elementary cellular automaton Rule 110 ($b'_i = (b_y + b_z + b_y b_z + b_x b_y b_z) \bmod 2$, truth vector $01101110_2$ on $111 \dots 000$) over $\{d_1, d_2\}$. Furthermore:

- (a) Whenever $x, y, z \in \mathcal{T}_S$ are Spine-$1$ normal forms ($S W$ with $W \in \mathcal{N}$, including $F_{\flat}$ and $T_{\sharp}$), $R_{110}(x, y, z)$ is already a Spine-$1$ normal form ($0$ reduction steps), so synchronous iteration of $R_{110}$ evolves arbitrary Rule 110 configurations entirely within Spine-$1$ normal forms.
- (b) No open $\{S, x, y, z\}$-polynomial with fewer than $11$ leaves realizes Rule 110 on $\{d_1, d_2\}$ in $\mathcal{D}_4$, and no curried closed combinator $G \in \mathcal{T}_S$ can satisfy $\llbracket G x y z \rrbracket_{\mathcal{D}_4} = \llbracket R_{110}(x, y, z) \rrbracket_{\mathcal{D}_4}$ (nor reduce $G x y z \to_S^* S W$).

*Proof.* 
For (i), if $\sqsubseteq$ is a compatible preorder on $(Q, q_0, \odot)$, structural induction on any open polynomial $P(x_1, \dots, x_k)$ built from constants in $Q$ and variables shows that $\vec{u} \sqsubseteq \vec{v}$ componentwise implies $P(\vec{u}) \sqsubseteq P(\vec{v})$. Whenever $e_0 \sqsubset e_1$ (meaning $e_0 \sqsubseteq e_1$ and $e_1 \not\sqsubseteq e_0$), any induced Boolean operation $f : \{0, 1\}^k \to \{0, 1\}$ with $P(e_{b_1}, \dots, e_{b_k}) = e_{f(b_1, \dots, b_k)}$ must satisfy $f(\vec{b}) \le f(\vec{b}')$ whenever $\vec{b} \le \vec{b}'$, placing $f$ inside Post's monotone clone $M \subsetneq \mathrm{Pol}(\{0, 1\})$ [49]. On $\mathcal{A}_{\mathrm{HN}}$, for example, ordering $q \sqsubseteq \infty_{\mathrm{HN}}$ for all $q$ (and refining along the $6$ compatible preorders of $\mathcal{A}_{\mathrm{HN}}$ and $5$ of $\mathcal{A}_{\mathrm{SN}}, \mathcal{A}_P$), together with complete finite closure of unary and binary operations on every incomparable pair $(e_0, e_1)$, confirms that every unary polynomial in $\mathcal{A}_{\mathrm{HN}}, \mathcal{A}_{\mathrm{SN}}, \mathcal{A}_P$ is aperiodic ($f(e_0) = e_1$ and $f(e_1) = e_0$ never hold simultaneously), ruling out $\mathrm{NOT}$ ($\neg x$), $\mathrm{NAND}$ ($\mathrm{NAND}(x, x) = \neg x$), $\mathrm{XOR}$ ($\mathrm{XOR}(x, 1) = \neg x$), and Rule 110 ($R_{110}(1, x, 1) = \neg x$).

For (ii), we verify (2.3) on $\mathcal{D}_4$ in four lines: for all $x, y, z \in Q_{\mathcal{D}_4}$, $d_0 \odot x \in \{d_1, d_2\}$, whence $(d_0 \odot x) \odot y \in \{d_1, d_3\}$, and since rows $d_1$ and $d_3$ are identically $d_3$, the left-hand side $((d_0 \odot x) \odot y) \odot z$ equals $d_3$. On the right-hand side $(x \odot z) \odot (y \odot z)$, note $d_0 \notin \mathrm{im}(\odot)$, so $x \odot z \in \{d_1, d_2, d_3\}$; if $x \odot z \in \{d_1, d_3\}$ the product is $d_3$, while the sole entry giving $x \odot z = d_2$ is $(x, z) = (d_0, d_3)$, for which $y \odot d_3 \in \{d_2, d_3\}$ and $d_2 \odot \{d_2, d_3\} = \{d_3\}$. Thus both sides of (2.3) equal $d_3$ identically.

Evaluating $\mathrm{NAND}(x, y) \equiv S(x(y S))$ on $x, y \in \{d_1, d_2\}$: if $y = d_1$, then $y \odot d_0 = d_3$, $x \odot d_3 = d_3$, and $d_0 \odot d_3 = d_2$; if $y = d_2$, then $y \odot d_0 = d_1$, so $d_1 \odot d_1 = d_3 \mapsto d_2$ whereas $d_2 \odot d_1 = d_1 \mapsto d_0 \odot d_1 = d_1$, matching $\mathrm{NAND}$. Similarly, for $x, y, z \in \{d_1, d_2\}$, observe that $u \odot v = d_1$ if $(u, v) = (d_2, d_1)$ and $d_3$ otherwise on $\{d_1, d_2\}^2$. Direct substitution into (8.2) over the eight triples $(x, y, z) \in \{d_1, d_2\}^3$ ordered from $(d_1, d_1, d_1)$ ($000$) to $(d_2, d_2, d_2)$ ($111$) yields $(d_1, d_2, d_2, d_2, d_1, d_2, d_2, d_1)$, matching $0, 1, 1, 1, 0, 1, 1, 0$ (Rule 110). For (a), if $x \equiv S W_x$, $y \equiv S W_y$, $z \equiv S W_z$ with $W_x, W_y, W_z \in \mathcal{N}$, then $y x \equiv S W_y (S W_x) \in \mathcal{N}_2 \subset \mathcal{N}$ (and likewise $y z, z y \in \mathcal{N}$), whence $S(z y)S \in \mathcal{N}$, $S(y z)(S(z y)S) \in \mathcal{N}$, $S(y x)(\dots) \in \mathcal{N}$, and $R_{110}(x, y, z) \equiv S(\dots)$ is a Spine-$1$ normal form. For (b), dynamic programming over all $4^8 = 65{,}536$ truth vectors in $Q_{\mathcal{D}_4}^8$ reachable from $\{S, x, y, z\}$ by leaf size $s = 1, \dots, 11$ confirms that $(d_1, d_2, d_2, d_2, d_1, d_2, d_2, d_1)$ is absent for all $s \le 10$ and first appears at $s = 11$; finally, for any $g \in Q_{\mathcal{D}_4}$, $((g \odot x) \odot y) \odot z = d_3$ identically as above, while Lemma 6.5(i) forbids $(G x y) z \to_S^* S W$.
 $\square$

## 9. Wolfram's Benchmark Evolutions, All-Step Jump-Ahead, Garden-of-Eden Normal Forms, and Exact Catalan Phase Transitions

In his centennial combinator monograph [72] and challenge announcement [71], Stephen Wolfram surveyed the empirical dynamics of small closed $S$-terms across the Catalan tree hierarchy, noting the minimal $7$-leaf threshold for non-termination, presenting twelve non-terminating benchmark expressions $W_1, \dots, W_{12}$ of leaf sizes $8$ through $11$ whose leftmost-outermost leaf-count differences exhibit varied transient and staircase patterns, and asking whether bounded-time "jump-ahead" procedures can predict halting or future structural states without step-by-step simulation. Beyond individual trajectories, Wolfram posed quantitative questions concerning the prevalence of Garden-of-Eden expressions (terms of in-degree zero in the multiway rewrite graph), strategy-dependent subterm appearance, and the limiting proportions of dynamical regimes among large random $S$-terms.

In this section we resolve each of these questions constructively. Subsection 9.1 classifies Duboué's $7$-leaf terms and Wolfram's twelve benchmarks algebraically and dynamically, isolating $W_2$ from Zachos's productive combinator $Z_{\mathrm{Zac}}$. Subsection 9.2 establishes linear-time multi-hole context halting, explicit all-step leftmost-outermost state and cubic leaf-count formulas for $Z_{\mathrm{Zac}}$, $W_2$ (together with a constant $+14$ leaf-shift law linking $W_2$ to an $=_S$-inconvertible twin), and the $10$-leaf universal seed $D_{\mathrm{seed}}$, followed by a three-rule multiway grammar on $A A A$ that yields sharp subterm-appearance separations between $\to_S^*$ and $\to_{\mathrm{lo}}$. Subsection 9.3 characterizes Garden-of-Eden normal forms, equates them on $\mathcal{N} := \mathrm{NF} \cap \mathcal{T}_S$ with isolated normal forms ($[P]_{=_S} = \{P\}$), proves a constructive tower law and linear-time decidability, and derives the exact Fibonacci–Mahler functional equation governing their growth constant $\gamma_{\mathrm{Iso}} \approx 2.907622 < 3$. Subsection 9.4 establishes sharp small-term minimality and confluence thresholds across all $23{,}714$ closed $S$-terms up to $11$ leaves. Finally, Subsection 9.5 combines analytic combinatorics with constructive arithmetic certificates over $\mathbb{N}$ to prove universal positive-density bounds and exact dyadic-ternary rational Catalan densities $(c_0, c_1, c_2, c_3)$ for the functional order hierarchy $\{0, 1, 2, 3\}$, completing a six-tier exponential growth spectrum for $\mathrm{CL}(S)$.

### 9.1. Algebraic and Dynamical Classification of Wolfram's Benchmark Expressions

Alongside Duboué's two minimal $7$-leaf non-normalizing $S$-terms $X_1 \equiv S(S S)S S S S$ and $X_2 \equiv S S S (S S) S S$ (communicated by Duboué and Baron in 1975; see [2], [1, Exercise 7.4.5], and [71, line 131]), let $W_1, \dots, W_{12}$ denote the twelve non-normalizing expressions displayed in lines 147–153 of [71]. Throughout this section we retain the standard abbreviations $T \equiv S S$, $A \equiv S S S$, $G_0 \equiv S T T$, $G_{k+1} \equiv T G_k$, $Z_0 \equiv S(S T)(S T)T$, $Z_{\mathrm{Zac}} \equiv G_0 G_0$, and $D_{\mathrm{seed}} \equiv Z_0 S$. Under leftmost-outermost reduction $\to_{\mathrm{lo}}$, whenever a closed $S$-term reaches a head normal form $S A_1$ or $S A_1 A_2$, the outer $S$-application freezes permanently as a *head-normal shell*: for $S A_1$, reduction descends into $A_1$; for $S A_1 A_2$, reduction descends into $A_1$ if $A_1 \notin \mathrm{SN}$, and otherwise normalizes $A_1 \to_{\mathrm{lo}}^* \mathrm{nf}(A_1) \in \mathcal{N}$ before descending permanently into $A_2$. Table 8 records the exact algebraic coordinates and $\to_{\mathrm{lo}}$ shell-stabilization behavior of all fourteen terms.

**Table 8.** Complete algebraic and $\to_{\mathrm{lo}}$ dynamical classification of Duboué's $7$-leaf terms $X_1, X_2$ and Wolfram's twelve challenge benchmarks $W_1, \dots, W_{12}$ [71]. State indices refer to $(\llbracket M \rrbracket_{\mathrm{SN}}, \llbracket M \rrbracket_{\mathrm{HN}}, \llbracket M \rrbracket_P)$ with sinks $(q_{38}, q_{34}, q_{37}) = (\infty_{\mathrm{SN}}, \infty_{\mathrm{HN}}, \infty_P)$.

| Term | Combinatory Form | Wolfram Announcement Syntax | $\vert M\vert$ | $(\mathrm{SN}, \mathrm{HN}, P)$ | Shells / Lock | $\to_{\mathrm{lo}}$ Dynamical Regime |
| :--- | :--- | :--- | :---: | :---: | :---: | :--- |
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

**Theorem 9.1 (Classification of Wolfram's benchmarks and separation of $W_2$ from $Z_{\mathrm{Zac}}$).**
Every term $M$ among the fourteen benchmark $S$-terms $X_1, X_2, W_1, \dots, W_{12}$ of Table 8 satisfies $\llbracket M \rrbracket_{\mathrm{SN}} = \infty_{\mathrm{SN}}$ and $\llbracket M \rrbracket_P = \infty_P$, and the fourteen terms partition into three disjoint $\to_{\mathrm{lo}}$ regimes:

- (i) *(Immediate unsolvability)* Seven benchmarks—$W_3, W_4, W_6, W_7, W_9, W_{10}, W_{12}$—satisfy $\llbracket W_i \rrbracket_{\mathrm{HN}} = \infty_{\mathrm{HN}}$ ($\mathrm{ord}(W_i) = 0$), executing pure head reduction indefinitely with $\mathrm{BT}(W_i) = \bot$.
- (ii) *(Finite shell stabilization into $\infty_{\mathrm{HN}}$)* Six benchmarks—$X_1, X_2, W_1, W_5, W_8, W_{11}$—lie in $\mathrm{HN} \setminus \mathrm{Prod}$ ($\mathrm{ord}(M) = 1$) and emit $4$ head-normal shells for $W_1$ and $1$ shell for each of the other five before their active $\to_{\mathrm{lo}}$ focus locks permanently into $\infty_{\mathrm{HN}}$ at steps $9, 8, 18, 21, 8, 4$, respectively.
- (iii) *(Perpetual solvable focus with hidden $\bot$)* Alone among the fourteen benchmarks, $W_2 \equiv S S S (S T) T$ ($8$ leaves, $\mathrm{ord}(W_2) = 1$) maintains an active $\to_{\mathrm{lo}}$ focus in $\mathrm{HN} \setminus \mathrm{SN}$ at every step $t \in \mathbb{N}$: defining $E_0 \equiv S(S T)T$ and $E_{m+1} \equiv T E_m$, after $\frac{1}{2}(n+1)(n+6) + 1$ steps ($n \ge 0$), $W_2$ reaches active focus $E_0 E_{n+1}$ ($\mathrm{HN}$ state $q_{23} \neq \infty_{\mathrm{HN}}$) beneath $\frac{1}{2}(n+1)(n+2)$ head-normal shells. Nevertheless, $\mathrm{BT}(W_2)$ contains an unsolvable subterm ($\infty_{\mathrm{HN}}$) at depth $5$, whence $W_2 \notin \mathrm{Prod}$, $W_2 \neq_S Z_{\mathrm{Zac}}$, and $W_2 \neq_S Z_0$.

*Proof.*
Regimes (i) and (ii) follow from Theorem 6.8(i) and Theorem 6.25(i) by evaluating $\llbracket \cdot \rrbracket_{\mathrm{HN}}$ on the initial terms and tracing $4$ to $21$ deterministic $\to_{\mathrm{lo}}$ steps until the unique active subterm beneath the stabilized $\mathrm{HNF}$ context reaches $\mathrm{HN}$ state $\infty_{\mathrm{HN}}$, after which pure head reduction continues inside that focus forever because $\infty_{\mathrm{HN}}$ admits no $\mathrm{HNF}$.

For (iii), set $E_0 \equiv S(S T)T \in \mathcal{N}$ ($6$ leaves) and $E_{m+1} \equiv T E_m \equiv S S E_m \in \mathcal{N}$ ($m \ge 0$, $|E_m| = 2m + 6$). Tracing the first four $\to_{\mathrm{lo}}$ steps of $W_2 \equiv ((S S S)(S T)) T$ yields

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

Here the outer shell $S\,\square\,[E_{k+2}(E_{k+1} E_{k+2})]$ permanently freezes its right sibling $R_{\mathrm{fr}}(k) \equiv E_{k+2}(E_{k+1} E_{k+2})$ and enters the left child $E_{k+1} E_{k+2}$, which then executes $k + 1$ single-step countdowns $E_{m+1} E_{k+2} \equiv S S E_m E_{k+2} \to_{\mathrm{lo}} S E_{k+2} (E_m E_{k+2})$ ($m = k, \dots, 0$, each $E_{k+2} \in \mathcal{N}$) down to $E_0 E_{k+2}$. Summing $4 + \sum_{j=0}^{n-1} (j + 4) = \frac{1}{2}(n+1)(n+6) + 1$ steps and $1 + \sum_{j=0}^{n-1} (j + 2) = \frac{1}{2}(n+1)(n+2)$ shells establishes the checkpoint trajectory, with every intermediate focus in $F_{\mathrm{HN}}$. Yet at $k = 0$, the first orphaned right sibling $R_{\mathrm{fr}}(0) \equiv E_2(E_1 E_2)$ sits at shell depth $2$ inside $S\,E_1\,(S\,\square\,R_{\mathrm{fr}}(0))$, and unfolding three further Böhm levels inside $R_{\mathrm{fr}}(0)$ reaches an unsolvable subterm ($\infty_{\mathrm{HN}}$) at Böhm depth $5$. Thus $\llbracket W_2 \rrbracket_P = \infty_P \neq q_{29} = \llbracket Z_{\mathrm{Zac}} \rrbracket_P = \llbracket Z_0 \rrbracket_P$, proving $W_2 \neq_S Z_{\mathrm{Zac}}$ and $W_2 \neq_S Z_0$. $\square$

### 9.2. Compositional Context Halting, All-Step Jump-Ahead Closed Forms, and Multiway Subterm Separations

In line 179 of [71], Wolfram asks whether "jump-ahead" procedures—algorithms guaranteed to halt in bounded time—can decide termination or compute distant future states of $S$-terms without simulating intermediate reductions. Theorems 6.2 and 6.8 furnish linear-time halting deciders for $\to_{\mathrm{lo}}$ and $\to_h$, and homomorphic compositionality extends these deciders to multi-hole contexts whose explicit substitution would grow exponentially. Beyond halting decisions, we show in Theorem 9.4 that for the principal non-terminating combinators $Z_{\mathrm{Zac}}$, $W_2$, and $D_{\mathrm{seed}}$, both the exact $t$-th leftmost-outermost reduct $\mathrm{lo}^t(M)$ and its exact cubic leaf count $|\mathrm{lo}^t(M)|$ admit closed-form descriptions at *every* integer step $t \in \mathbb{N}$.

**Proposition 9.2 (Linear-time multi-hole context halting and checkpoint jump-ahead).**

- (i) *(Compositional $k$-hole context halting)* Let $C[\square_1, \dots, \square_k]$ be an arbitrary $k$-hole $S$-context (allowing each hole $\square_i$ to appear arbitrarily many times at arbitrary depths) of syntactic size $|C|$, and let $M_1, \dots, M_k \in \mathcal{T}_S$ be closed arguments. Whether $C[M_1, \dots, M_k]$ halts under $\to_{\mathrm{lo}}$ (respectively $\to_h$) is decidable in $O\bigl(|C| + \sum_{i=1}^k |M_i|\bigr)$ time without constructing $C[M_1, \dots, M_k]$.
- (ii) *(Two-parameter counter checkpoints on $D_{\mathrm{seed}}$)* On the $10$-leaf seed $D_{\mathrm{seed}} \equiv S(S(S S))(S(S S))(S S)S$, setting $C_0 \equiv S T T \equiv G_0$ and $C_{m+1} \equiv T C_m \equiv G_{m+1}$, for every $n \ge 1$ and $0 \le r \le n$, step $(2n^2 - n + 1) + 4r$ under $\to_{\mathrm{lo}}$ places $D_{\mathrm{seed}}$ at active counter focus $C_{n-r} C_n S$ beneath $\frac{1}{2}n(n-1) + r$ left-active head-normal shells (reaching $C_0 C_n S$ at step $2n^2 + 3n + 1$ when $r = n$).
- (iii) *(Exact quarter-square normal-form step count on left spines)* Define the left-associated spine $P_0 \equiv S$, $P_{m+1} \equiv P_m S$ ($m + 1$ leaves, arity $m \ge 0$). Then $P_m$ reaches its normal form under $\to_{\mathrm{lo}}$ in exact step count

$$
s(m) \;=\; \Bigl\lfloor \frac{m-1}{2} \Bigr\rfloor \cdot \Bigl\lfloor \frac{m}{2} \Bigr\rfloor
\qquad (m \in \mathbb{N}), \tag{9.1}
$$

whereas the right-associated comb $R_m$ ($R_0 \equiv S$, $R_{m+1} \equiv S R_m$) is already in normal form ($0$ steps).

*Proof.*
For (i), evaluate $q_i = \llbracket M_i \rrbracket_{\mathrm{SN}} \in Q_{\mathrm{SN}}$ (or $\llbracket M_i \rrbracket_{\mathrm{HN}} \in Q_{\mathrm{HN}}$) in $2|M_i| - 1$ table lookups for $1 \le i \le k$, then evaluate $C$ bottom-up in $|C|$ lookups by assigning state $q_i$ to every occurrence of $\square_i$ and $q_0$ to $S$. By homomorphic compositionality of $\llbracket \cdot \rrbracket_{\mathcal{A}}$, the root state equals $\llbracket C[M_1, \dots, M_k] \rrbracket_{\mathcal{A}}$, deciding $\mathrm{SN}$ (hence $\to_{\mathrm{lo}}$ halting by standardization and Proposition 2.2) and $\mathrm{HN}$ ($\to_h$ halting) in $O(|C| + \sum |M_i|)$ time.

For (ii), two initial contractions reduce $D_{\mathrm{seed}} \equiv S(S T)(S T)T S \to_{\mathrm{lo}} (S T T)(S T T) S \equiv C_0 C_0 S \to_{\mathrm{lo}} (T C_0)(T C_0) S \equiv C_1 C_1 S$, reaching $(1, 1)$ at step $2 = 2(1)^2 - 1 + 1$ with $0$ shells. From any counter state $C_{m+1} C_p S \equiv (S S C_m) C_p S$ ($p \ge 1$), four $\to_{\mathrm{lo}}$ contractions via $((S C_p)(C_m C_p)) S \to_{\mathrm{lo}} (C_p S)(C_m C_p S) \equiv (S S (C_{p-1} S))(C_m C_p S)$ produce $S\,(C_m C_p S)\,\bigl((C_{p-1} S)(C_m C_p S)\bigr)$, adding one left-active Spine-$2$ shell around $C_m C_p S$; at $m = 0$, a single contraction resets $C_0 C_p S \equiv S T T C_p S \to_{\mathrm{lo}} (T C_p)(T C_p) S \equiv C_{p+1} C_{p+1} S$ with $0$ additional shells. Induction over $n \ge 1$ sums $2 + \sum_{j=1}^{n-1} (4j + 1) = 2n^2 - n + 1$ steps and $\sum_{j=1}^{n-1} j = \frac{1}{2}n(n-1)$ shells to reach $C_n C_n S$, after which $r$ further countdown transitions ($0 \le r \le n$) add $4r$ steps and $r$ shells to reach $C_{n-r} C_n S$.

For (iii), $P_0 \equiv S$, $P_1 \equiv S S$, and $P_2 \equiv S S S$ lie in $\mathcal{N}$, matching $s(0) = s(1) = s(2) = 0$. For $m = d + 3$ ($d \ge 0$), $P_{d+3} \equiv S S S S S^d \to_{\mathrm{lo}} (S S)(S S) S^d$, which peels in $d$ further $\to_{\mathrm{lo}}$ steps via $(S S) U S \to_{\mathrm{lo}} S S (U S)$ to $(S S)\,P_{d+1} \equiv T\,P_{d+1}$, giving $P_{d+3} \to_{\mathrm{lo}}^{d+1} T\,P_{d+1}$ with spine arity at least $3$ at all $j < d + 1$ steps. Because $T\,U \equiv S S U$ is a Spine-$2$ right-hole shell $S\,S\,\square$ with $S \in \mathcal{N}$, subsequent $\to_{\mathrm{lo}}$ steps act strictly inside $P_{d+1}$, yielding the recurrence $s(d + 3) = (d + 1) + s(d + 1)$. Since $\lfloor \frac{d+2}{2} \rfloor \lfloor \frac{d+3}{2} \rfloor - \lfloor \frac{d}{2} \rfloor \lfloor \frac{d+1}{2} \rfloor = (\lfloor \frac{d}{2} \rfloor + 1)(\lfloor \frac{d+1}{2} \rfloor + 1) - \lfloor \frac{d}{2} \rfloor \lfloor \frac{d+1}{2} \rfloor = \lfloor \frac{d}{2} \rfloor + \lfloor \frac{d+1}{2} \rfloor + 1 = d + 1$, induction on $m$ establishes (9.1). $\square$

To extend checkpoint descriptions to *all* steps $t \in \mathbb{N}$ without existential context quantifiers, we define the accumulated head-normal shell contexts explicitly.

**Definition 9.3 (Explicit leftmost-outermost shell contexts for $Z_{\mathrm{Zac}}$, $W_2$, and $D_{\mathrm{seed}}$).**
For any closed normal form $L \in \mathcal{N}$, write $(S L)^0(U) \equiv U$ and $(S L)^{k+1}(U) \equiv S\,L\,\bigl((S L)^k(U)\bigr)$ ($k \in \mathbb{N}$). Define three families of one-hole head-normal contexts inductively:

- (i) *(Zachos context tower)* Set $\mathcal{C}_Z(0)[\square] \equiv \square$ and, for $n \in \mathbb{N}$,

$$
\mathcal{C}_Z(n+1)[\square] \;\equiv\; \mathcal{C}_Z(n)\Bigl[(S G_{n+1})^{n+1}(\square)\Bigr]
\qquad (|G_k| = 2k + 5).
$$

- (ii) *(Benchmark $W_2$ context tower)* With $E_0 \equiv S(S T)T$ and $E_{k+1} \equiv T E_k$ ($|E_k| = 2k + 6$), set $\mathcal{C}_{W_2}(0)[\square] \equiv S\,E_1\,\square$ and, for $n \in \mathbb{N}$,

$$
\mathcal{C}_{W_2}(n+1)[\square] \;\equiv\; \mathcal{C}_{W_2}(n)\Bigl[S\,\bigl((S E_{n+2})^{n+1}(\square)\bigr)\,\bigl(E_{n+2}(E_{n+1} E_{n+2})\bigr)\Bigr].
$$

- (iii) *(Universal seed context tower)* With $C_k \equiv G_k$ and $D_{k,p} \equiv C_k C_p S$ ($|D_{k,p}| = 2k + 2p + 11$), for each $p \in \mathbb{N}$ and $0 \le r \le p + 1$ define the partial cycle wrapper $\mathcal{F}_{p,0}[\square] \equiv \square$ and $\mathcal{F}_{p, r+1}[\square] \equiv \mathcal{F}_{p,r}\bigl[S\,\square\,\bigl((C_p S)\,D_{p-r, p+1}\bigr)\bigr]$, and set $\mathcal{C}_{\mathrm{seed}}(0)[\square] \equiv \square$ and $\mathcal{C}_{\mathrm{seed}}(m+1)[\square] \equiv \mathcal{C}_{\mathrm{seed}}(m)\bigl[\mathcal{F}_{m, m+1}[\square]\bigr]$.

For any context $\mathcal{C}[\square]$ built from Spine-$1$ frames $S\,\square$, Spine-$2$ right-hole frames $S\,L\,\square$ ($L \in \mathcal{N}$), and Spine-$2$ left-hole frames $S\,\square\,R$, let $\lambda(\mathcal{C}) := |\mathcal{C}[S]| - 1$ denote the frozen shell leaf contribution, so that $|\mathcal{C}[U]| = \lambda(\mathcal{C}) + |U|$ and $\mathrm{lo}^k(\mathcal{C}[U]) \equiv \mathcal{C}[\mathrm{lo}^k(U)]$ whenever $\mathrm{lo}^j(U)$ is reducible for all $j < k$.

**Theorem 9.4 (All-step $\to_{\mathrm{lo}}$ closed forms, triangular staircase law, and $+14$ twin shift).**
Let $\mathrm{lo}^t(M)$ denote the $t$-th iterate of deterministic leftmost-outermost reduction starting from $M \in \mathcal{T}_S$.

- (i) *(All-step closed form and triangular staircase law on $Z_{\mathrm{Zac}}$)* Every step $t \in \mathbb{N}$ decomposes uniquely as $t = \frac{1}{2}n(n+3) + r$ with $n \in \mathbb{N}$ and $0 \le r \le n + 1$. At offset $r = 0$, $\mathrm{lo}^t(Z_{\mathrm{Zac}}) \equiv \mathcal{C}_Z(n)[G_0 G_n]$, whereas at offset $r = k + 1$ ($0 \le k \le n$), $\mathrm{lo}^t(Z_{\mathrm{Zac}}) \equiv \mathcal{C}_Z(n)\bigl[(S G_{n+1})^k(G_{n+1-k}\,G_{n+1})\bigr]$. For every $t = \frac{1}{2}n(n+3) + r$ ($0 \le r \le n + 1$), the exact leaf count is

$$
\bigl|\mathrm{lo}^t(Z_{\mathrm{Zac}})\bigr|
\;=\; 10 \;+\; \frac{2n(n+2)(n+4)}{3} \;+\; \mathbf{1}_{r \ge 1}\,\bigl(r(2n+6) - 2\bigr). \tag{9.2}
$$

Moreover, re-indexing $t$ along triangular blocks $t = \frac{1}{2}m(m+1) + j$ ($m \in \mathbb{N}$, $0 \le j \le m$), the first difference obeys the exact staircase law

$$
\bigl|\mathrm{lo}^{t+1}(Z_{\mathrm{Zac}})\bigr| - \bigl|\mathrm{lo}^t(Z_{\mathrm{Zac}})\bigr|
\;=\; 2(m + 2)
\qquad (0 \le j \le m), \tag{9.3}
$$

generating the blockwise step increments $+4;\; +6, +6;\; +8, +8, +8;\; +10, +10, +10, +10;\; \dots$
- (ii) *(All-step closed form on $W_2$ and constant $+14$ twin shift law)* On $W_2 \equiv S S S (S T) T$, initial leaf counts at $t = 0, 1, 2, 3$ are $8, 10, 11, 16$. Every step $t \ge 4$ decomposes uniquely as $t = \frac{1}{2}(n+1)(n+6) + 1 + r$ with $n \in \mathbb{N}$ and $0 \le r \le n + 3$, where

$$
\mathrm{lo}^t(W_2) \;\equiv\;
\begin{cases}
\mathcal{C}_{W_2}(n)[E_0 E_{n+1}] & \text{if } r = 0, \\
\mathcal{C}_{W_2}(n)\bigl[(S T E_{n+1})\,E_{n+2}\bigr] & \text{if } r = 1, \\
\mathcal{C}_{W_2}(n)\bigl[E_{n+3}(E_{n+1} E_{n+2})\bigr] & \text{if } r = 2, \\
\mathcal{C}_{W_2}(n)\Bigl[S\,\bigl((S E_{n+2})^j(E_{n+1-j} E_{n+2})\bigr)\,\bigl(E_{n+2}(E_{n+1} E_{n+2})\bigr)\Bigr] & \text{if } r = j + 3 \; (0 \le j \le n),
\end{cases}
$$

with exact cubic leaf count

$$
\bigl|\mathrm{lo}^t(W_2)\bigr|
\;=\; \frac{4n^3 + 51n^2 + 197n + 138}{6} \;+\; \delta_{W_2}(n, r), \tag{9.4}
$$

for $\delta_{W_2}(n, 0) = 0$, $\delta_{W_2}(n, 1) = 2n + 7$, $\delta_{W_2}(n, 2) = 4n + 16$, and $\delta_{W_2}(n, j + 3) = (8n + 33) + j(2n + 9)$. Furthermore, the $12$-leaf twin $W_2^{\mathrm{twin}} \equiv E_0 E_0$ shares identical $(\mathcal{A}_{\mathrm{SN}}, \mathcal{A}_P)$ evaluations $(\infty_{\mathrm{SN}}, \infty_P)$ and order-$1$ solvability ($\llbracket W_2 \rrbracket_{\mathrm{HN}} = q_{24}$, $\llbracket W_2^{\mathrm{twin}} \rrbracket_{\mathrm{HN}} = q_{23}$) with $W_2$, satisfies $W_2 \neq_S W_2^{\mathrm{twin}}$, yet obeys for every $t \ge 3$ the exact constant-offset identity

$$
\bigl|\mathrm{lo}^{t+1}(W_2)\bigr| + 14 \;=\; \bigl|\mathrm{lo}^t(W_2^{\mathrm{twin}})\bigr|. \tag{9.5}
$$

- (iii) *(All-step exact leaf formula on $D_{\mathrm{seed}}$)* On $D_{\mathrm{seed}}$, initial leaf counts at $t = 0, 1$ are $10, 11$. Every step $t \ge 2$ decomposes uniquely as $t = (2N^2 - N + 1) + d$ with $N \ge 1$ and $0 \le d \le 4N$; writing $r = \lfloor d / 4 \rfloor$, one has

$$
\bigl|\mathrm{lo}^t(D_{\mathrm{seed}})\bigr|
\;=\; \frac{5N^3 + 15N^2 - 8N + 33}{3} \;+\; r(6N + 13 - r) \;+\; \mathbf{1}_{d \not\equiv 0 \pmod{4}}\,(2N + 4). \tag{9.6}
$$

*Proof.*
For (i), because $\tau_Z(n+1) - \tau_Z(n) = \frac{1}{2}(n+1)(n+4) - \frac{1}{2}n(n+3) = n + 2$, the intervals $\{\tau_Z(n) + r : 0 \le r \le n + 1\}$ partition $\mathbb{N}$. From $\mathcal{C}_Z(n)[G_0 G_n]$, one contraction inside the active focus gives $G_0 G_n \equiv S T T G_n \to_{\mathrm{lo}} (T G_n)(T G_n) \equiv G_{n+1} G_{n+1}$, and $k$ subsequent contractions ($0 \le k \le n + 1$) peel Spine-$2$ right-hole shells $G_{m+1} G_{n+1} \equiv S S G_m G_{n+1} \to_{\mathrm{lo}} S G_{n+1} (G_m G_{n+1})$ since $G_{n+1} \in \mathcal{N}$; at $k = n + 1$, the accumulated shells merge into $\mathcal{C}_Z(n+1)[G_0 G_{n+1}]$. Induction on $n$ gives $3\,\lambda(\mathcal{C}_Z(n)) = \sum_{i=1}^n 3i(1 + |G_i|) = \sum_{i=1}^n 6i(i + 3) = n(n+1)(2n+10)$. Adding $|G_0 G_n| = 5 + (2n + 5) = 2n + 10$ gives $3\,\lambda(\mathcal{C}_Z(n)) + 3(2n + 10) = 2n(n+2)(n+4) + 30$, proving (9.2) at $r = 0$. For $r = k + 1 \ge 1$, the $k$ inner frames $(S G_{n+1})^k$ and focus $G_{n+1-k} G_{n+1}$ contribute $k(2n + 8) + (2(n + 1 - k) + 5) + (2n + 7) = (2n + 10) + (k + 1)(2n + 6) - 2$, yielding (9.2) for all $r$.

To deduce (9.3), at $m = 0$ ($j = 0, t = 0$) we have $14 - 10 = 4 = 2(0 + 2)$. For $m = n + 1 \ge 1$, note that $\frac{1}{2}(n+1)(n+2) = \frac{1}{2}n(n+3) + 1 = \tau_Z(n) + 1$. When $0 \le j \le n$, step $t = \tau_Z(n) + (j + 1)$ advances to $t + 1 = \tau_Z(n) + (j + 2)$ within cycle $n$ ($r = j + 1 \to j + 2 \le n + 2$, valid since the formula at $r = n + 2$ agrees with cycle $n + 1$ at $r = 0$), increasing leaf count by $((j + 2)(2n + 6) - 2) - ((j + 1)(2n + 6) - 2) = 2n + 6 = 2(m + 2)$. At the block endpoint $j = n + 1$, $t = \tau_Z(n) + (n + 2) = \tau_Z(n + 1)$ transitions from $r = 0$ to $r = 1$ in cycle $n + 1$, increasing leaf count by $1 \cdot (2(n + 1) + 6) - 2 = 2n + 6 = 2(m + 2)$.

For (ii), Theorem 9.1(iii) yields the intra-cycle transitions of $W_2$ at offsets $r = 0, 1, 2$ and $r = j + 3$ ($0 \le j \le n + 1$), with $\tau_{W_2}(n+1) - \tau_{W_2}(n) = n + 4$. Each cycle $i \to i + 1$ appends one left-hole frame $S\,\square\,[E_{i+2}(E_{i+1} E_{i+2})]$ of extra leaf weight $1 + (2i + 10) + (2i + 8) + (2i + 10) = 6i + 29$ and $i + 1$ right-hole frames $S E_{i+2} \square$ of weight $(i + 1)(2i + 11)$, so induction on $n$ gives $6\,\lambda(\mathcal{C}_{W_2}(n)) = 4n^3 + 51n^2 + 185n + 54$. Adding $|E_0 E_{n+1}| = 6 + (2n + 8) = 2n + 14$ at $r = 0$ gives $(4n^3 + 51n^2 + 197n + 138)/6$, and inspecting the focus and local frame weights at $r = 1, 2, j + 3$ yields $\delta_{W_2}(n, r)$ and (9.4). Next, for $W_2^{\mathrm{twin}} \equiv E_0 E_0$, direct automaton evaluation gives $(\llbracket W_2^{\mathrm{twin}} \rrbracket_{\mathrm{SN}}, \llbracket W_2^{\mathrm{twin}} \rrbracket_{\mathrm{HN}}, \llbracket W_2^{\mathrm{twin}} \rrbracket_P) = (\infty_{\mathrm{SN}}, q_{23}, \infty_P)$. Three leftmost-outermost contractions reduce

$$
W_2^{\mathrm{twin}} \;\equiv\; S(S T)T\,E_0
\;\longrightarrow_{\mathrm{lo}}\; (S T E_0)\,E_1
\;\longrightarrow_{\mathrm{lo}}\; E_2\,(E_0 E_1)
\;\longrightarrow_{\mathrm{lo}}\; S\,(E_0 E_1)\,\bigl(E_1(E_0 E_1)\bigr),
$$

whereas $W_2 \to_{\mathrm{lo}}^4 S\,E_1\,(E_0 E_1)$. If $W_2 =_S W_2^{\mathrm{twin}}$, then the Spine-$2$ root normal forms $S\,E_1\,(E_0 E_1)$ and $S\,(E_0 E_1)\,(E_1(E_0 E_1))$ would be $=_S$-convertible, forcing $S E_1 =_S S(E_0 E_1)$ by Proposition 6.22(iii); this is impossible because $S E_1 \in \mathcal{N} \subseteq \mathrm{SN}$ while $\llbracket S(E_0 E_1) \rrbracket_{\mathrm{SN}} = \infty_{\mathrm{SN}}$ ($E_0 E_1 \notin \mathrm{SN}$). Yet both $\mathrm{lo}^4(W_2) \equiv \mathcal{K}_1[E_0 E_1]$ ($\mathcal{K}_1[\square] \equiv S\,E_1\,\square$, $\lambda(\mathcal{K}_1) = 1 + 8 = 9$) and $\mathrm{lo}^3(W_2^{\mathrm{twin}}) \equiv \mathcal{K}_2[E_0 E_1]$ ($\mathcal{K}_2[\square] \equiv S\,\square\,[E_1(E_0 E_1)]$, $\lambda(\mathcal{K}_2) = 1 + 8 + 6 + 8 = 23$) wrap valid head-normal shells around the identical non-normalizing active focus $E_0 E_1$. For every $k \in \mathbb{N}$ ($t = 3 + k$), $\mathrm{lo}^{4+k}(W_2) \equiv \mathcal{K}_1[\mathrm{lo}^k(E_0 E_1)]$ and $\mathrm{lo}^{3+k}(W_2^{\mathrm{twin}}) \equiv \mathcal{K}_2[\mathrm{lo}^k(E_0 E_1)]$, so their leaf counts differ constantly by $\lambda(\mathcal{K}_2) - \lambda(\mathcal{K}_1) = 23 - 9 = 14$, proving (9.5).

For (iii), in cycle $N = m + 1 \ge 1$ starting at step $2N^2 - N + 1$ with $\mathcal{C}_{\mathrm{seed}}(m)[D_{N,N}]$ (Proposition 9.2(ii)), the $r$-th four-step countdown ($0 \le r \le m$) peels the frozen right sibling $(C_m S)\,D_{m-j, m+1}$ for $j = 0, \dots, r - 1$ of weight $1 + (2m + 6) + (2(m - j) + 2(m + 1) + 11) = 6m + 20 - 2j$, summing over $0 \le j < r$ to $r(6m + 21 - r) = r(6N + 15 - r)$. Summing full cycles $1 \le i \le m$ yields $3\,\lambda(\mathcal{C}_{\mathrm{seed}}(m)) = 5m^3 + 30m^2 + 25m$, and adding $|D_{N,N}| = 4N + 11$ gives $(5N^3 + 15N^2 - 8N + 33)/3$ at $d = 0$. Writing $d = 4r + u$ ($0 \le u \le 3$), decreasing $D_{N,N}$ to $D_{N-r, N}$ subtracts $2r$ from the focus while adding $r(6N + 15 - r)$ to the shell, for a net gain of $r(6N + 13 - r)$ at $u = 0$. When $u \in \{1, 2, 3\}$ ($r < N$, $k = N - 1 - r$), the first contraction $D_{k+1, N} \equiv (S S C_k) C_N S \to_{\mathrm{lo}} (S C_N)(C_k C_N) S$ duplicates $C_N$ ($|C_N| = 2N + 5$), adding $(2N + 5) - 1 = 2N + 4$ leaves, while the second and third contractions $((S C_N)(C_k C_N)) S \to_{\mathrm{lo}} (C_N S)(C_k C_N S) \to_{\mathrm{lo}} (S S (C_{N-1} S))(C_k C_N S)$ have atomic third argument $S$ and therefore preserve leaf count identically at $+(2N + 4)$, proving (9.6). $\square$

Wolfram also asked whether subterms reachable somewhere in the multiway reduction graph $\to_S^*$ must eventually appear along deterministic leftmost-outermost evolution $\to_{\mathrm{lo}}$. Analyzing the multiway invariant of Barendregt's unsolvable term $A A A$ yields negative answers in both the normalizing and perpetually evolving regimes.

**Proposition 9.5 (Multiway grammar on $A A A$, universal $S(S S)$ exclusion, and subterm separations).**
Let $\mathcal{G}_A \subseteq \mathcal{T}_S$ be the inductive class generated by the three rules $A \in \mathcal{G}_A$ ($A \equiv S S S$), $U \in \mathcal{G}_A \implies S U \in \mathcal{G}_A$, and $U, V \in \mathcal{G}_A \implies U V \in \mathcal{G}_A$ (coinciding on closed terms with $\mathcal{H}$ of Definition 6.17).

- (i) *(Multiway closure, $+2$ leaf growth, and universal $S(S S)$ exclusion on $A A A$)* Every $U \in \mathcal{G}_A$ satisfies $|U| \ge 3$, and every one-step multiway contraction $U \to_S U'$ from $U \in \mathcal{G}_A$ satisfies $U' \in \mathcal{G}_A$ and $|U'| \ge |U| + 2$. Consequently, along $\to_{\mathrm{lo}}$, $A A A \in \mathcal{G}_A$ executes pure head reduction with $|\mathrm{lo}^{k+1}(A A A)| \ge |\mathrm{lo}^k(A A A)| + 2$ and $|\mathrm{lo}^k(A A A)| \ge 9 + 2k$ for all $k \in \mathbb{N}$, and across the entire infinite multiway reduction set $\{ N \in \mathcal{T}_S : A A A \to_S^* N \}$, the $3$-leaf normal form $S(S S)$ never occurs as a subterm.
- (ii) *(Halting and non-halting subterm-appearance separations)* On the $7$-leaf normalizing term $M_{\mathrm{sep}}^{\mathrm{SN}} \equiv T(S S S S)S$, the $6$-leaf normal form $P_{\mathrm{sep}}^{\mathrm{SN}} \equiv T(T T)$ occurs as a subterm in one multiway step ($M_{\mathrm{sep}}^{\mathrm{SN}} \to_S T(T T)S$), yet never occurs in $\mathrm{lo}^k(M_{\mathrm{sep}}^{\mathrm{SN}})$ for any $k \in \mathbb{N}$. On the $14$-leaf non-normalizing term $M_{\mathrm{sep}}^{\infty} \equiv S(A A A)(A T) \in \mathrm{HN} \setminus \mathrm{SN}$, the $3$-leaf normal form $S(S S)$ occurs as a subterm in one multiway step ($M_{\mathrm{sep}}^{\infty} \to_S S(A A A)\bigl(S(S S)(S(S S))\bigr)$), yet $\mathrm{lo}^k(M_{\mathrm{sep}}^{\infty})$ reduces forever without $S(S S)$ ever occurring as a subterm at any step $k \in \mathbb{N}$.

*Proof.*
For (i), structural induction on $U \in \mathcal{G}_A$ gives $|U| \ge 3$ (hence $U \not\equiv S$ and $U \not\equiv T$). Inversion on $\mathcal{G}_A$ shows $S U \in \mathcal{G}_A \implies U \in \mathcal{G}_A$ (since $S \notin \mathcal{G}_A$ rules out the binary-application constructor) and $S X Y \in \mathcal{G}_A \implies (X \equiv S \land Y \equiv S) \vee (X \in \mathcal{G}_A \land Y \in \mathcal{G}_A)$. If $U \in \mathcal{G}_A$ contracts at the root as $U \equiv S X Y Z \to_S (X Z)(Y Z) \equiv U'$, then $Z \in \mathcal{G}_A$ ($|Z| \ge 3$), and either $(X, Y) = (S, S)$ giving $(S Z)(S Z) \in \mathcal{G}_A$ or $X, Y \in \mathcal{G}_A$ giving $(X Z)(Y Z) \in \mathcal{G}_A$; in both cases $|U'| - |U| = |Z| - 1 \ge 2$. Contextual steps lift directly by induction because neither $S$ nor $S S$ admits an internal step in $A \equiv (S S) S$ or $S U$. Since $A A A \in \mathcal{G}_A$ and $\llbracket A A A \rrbracket_{\mathrm{HN}} = \infty_{\mathrm{HN}}$, every $\to_{\mathrm{lo}}$ step is a head step satisfying $|\mathrm{lo}^{k+1}(A A A)| \ge |\mathrm{lo}^k(A A A)| + 2$, giving $|\mathrm{lo}^k(A A A)| \ge 9 + 2k$. Finally, we check by induction on $U \in \mathcal{G}_A$ that $S(S S)$ is not a subterm of $U$: the subterms of $A \equiv (S S) S$ are $A, S S, S$; a node $S W$ with $W \in \mathcal{G}_A$ cannot equal $S(S S)$ at the root because $|W| \ge 3 > 2 = |S S|$; and a node $W_1 W_2$ with $W_1, W_2 \in \mathcal{G}_A$ cannot equal $S(S S)$ at the root because $|W_1| \ge 3 > 1 = |S|$. Since $\mathcal{G}_A$ is closed under $\to_S^*$, no multiway reduct $N$ of $A A A$ contains $S(S S)$.

For (ii), contracting $S S S S \to_S T T$ inside $M_{\mathrm{sep}}^{\mathrm{SN}} \equiv T(S S S S)S$ produces $T(T T)S$ in one step, whereas $\to_{\mathrm{lo}}$ reduces $T(S S S S)S \equiv S S (S S S S) S \to_{\mathrm{lo}} T((S S S S)S) \to_{\mathrm{lo}} T(T T S) \to_{\mathrm{lo}} T(S S(T S)) \in \mathcal{N}$, none of which contains $T(T T)$. Similarly, contracting $A T \equiv S S S (S S) \to_S S(S S)(S(S S))$ on the right of $M_{\mathrm{sep}}^{\infty}$ produces $S(S S)$ in one step; under $\to_{\mathrm{lo}}$, however, the Spine-$2$ left-hole shell $S\,\square\,(A T)$ keeps the right sibling $A T$ permanently unreduced while stepping forever inside $A A A$, so $\mathrm{lo}^k(M_{\mathrm{sep}}^{\infty}) \equiv S\,\mathrm{lo}^k(A A A)\,(A T)$ for all $k \in \mathbb{N}$. Neither $A T \equiv ((S S) S)(S S)$ nor $\mathrm{lo}^k(A A A) \in \mathcal{G}_A$ contains $S(S S)$ by (i), and $|\mathrm{lo}^k(A A A)| \ge 9$ precludes $S\,\mathrm{lo}^k(A A A) \equiv S(S S)$. $\square$

### 9.3. Garden-of-Eden and Isolated Normal Forms: Characterization, Decidability, and Mahler Growth

In cellular automata and combinatory rewriting [68, 72], a configuration or term is called *Garden-of-Eden* if it cannot be reached by one or more rewrite steps from any predecessor. On closed normal forms $\mathcal{N} = \mathrm{NF} \cap \mathcal{T}_S$, Garden-of-Eden status connects directly to Dana Scott's convertibility problem (Question 30, Proposition 6.22(ii)): a closed normal form has in-degree zero in $\mathrm{CL}(S)$ if and only if its $=_S$-equivalence class is a singleton.

**Definition 9.6 (Garden-of-Eden terms and isolated normal forms).**
A closed pure-$S$ term $P \in \mathcal{T}_S$ is *Garden-of-Eden* ($P \in \mathrm{GoE}$) if there is no closed term $M \in \mathcal{T}_S$ such that $M \to_S^+ P$. A term $P \in \mathcal{T}_S(\mathcal{V})$ is an *isolated normal form* ($P \in \mathrm{IsoNF}$) if $P \in \mathrm{NF}$ and there is no $M \in \mathcal{T}_S(\mathcal{V})$ such that $M \to_S P$. We write $\#\mathrm{IsoNF}(n) := \#\{ P \in \mathcal{T}_S \cap \mathrm{IsoNF} : |P| = n \}$ and $\#\mathcal{N}(n) := \#\{ P \in \mathcal{N} : |P| = n \}$.

**Theorem 9.7 (Characterization, tower law, Motzkin hierarchy, and Mahler asymptotics of Garden-of-Eden normal forms).**

- (i) *(Equivalence, backward decomposition, and syntactic decidability)* For every $P \in \mathcal{T}_S(\mathcal{V})$, $[P]_{=_S} = \{P\}$ holds if and only if $P \in \mathrm{IsoNF}$; for closed normal forms $P \in \mathcal{N}$, $P \in \mathrm{GoE} \iff P \in \mathrm{IsoNF}$. Every closed term with $|P| \le 3$ belongs to $\mathrm{GoE}$, and at $|P| = 4$, $S S (S S)$ is the unique closed normal form outside $\mathrm{GoE}$. For closed normal forms $U, V \in \mathcal{N}$, one has $S U \in \mathrm{GoE} \iff U \in \mathrm{GoE}$, whereas $S U V \in \mathrm{GoE}$ holds if and only if $U \in \mathrm{GoE}$, $V \in \mathrm{GoE}$, and there exists no $Y_0 \in \mathcal{N}$ with $|Y_0| + |U| \le |V|$ and $Y_0 U \to_S^* V$—a condition that, given $V \in \mathrm{GoE}$, reduces to the purely syntactic check $\forall Y \in \mathcal{T}_S,\, V \not\equiv Y U$. Consequently, membership in $\mathcal{N} \cap \mathrm{GoE}$ is constructively decidable in linear time on tree representations with subterm equality (or quadratic leaf-comparison time).
- (ii) *(Constructive tower law and isolation of order-$3$ combs)* Whenever $U, V \in \mathcal{N} \cap \mathrm{GoE}$ satisfy $|V| \le |U|$, the Spine-$2$ normal form $S U V$ lies in $\mathrm{GoE}$. Moreover, every closed order-$3$ right comb $R_{n-1}$ ($n \ge 1$) lies in $\mathrm{IsoNF}$.
- (iii) *(Shifted Motzkin law for $\mathcal{N}$, small-$n$ census, and constructive exponential decay)* For every $n \ge 1$, $\#\mathcal{N}(n) = M_{n-1}$ equals the shifted Motzkin number defined by $M_0 = 1$ and $\#\mathcal{N}(m+2) = \#\mathcal{N}(m+1) + \sum_{a+b=m+1} \#\mathcal{N}(a)\,\#\mathcal{N}(b)$ ($m \ge 0$, dominant growth rate $\gamma_{\mathrm{NF}} = 3$). Constructively for every $n \ge 1$,

$$
1 \;\le\; \#\mathrm{IsoNF}(n) \;\le\; \#\mathcal{N}(n) \;\le\; \#\mathrm{SN}(n),
\qquad
\frac{\#\mathrm{IsoNF}(n)}{C_{n-1}} \;\le\; \frac{\#\mathcal{N}(n)}{C_{n-1}} \;\le\; 51.39438 \cdot \Bigl(\frac{250}{259}\Bigr)^n. \tag{9.7}
$$

For leaf sizes $1 \le n \le 7$, the exact ratio $\#\mathrm{IsoNF}(n) / \#\mathcal{N}(n)$ takes the values $1/1,\; 1/1,\; 2/2,\; 3/4,\; 7/9,\; 15/21,\; 37/51$ (continuing $87/127,\; 218/323,\; 546/835,\; 1393/2188$ for $8 \le n \le 11$).
- (iv) *(Bilinear exclusion recurrence and Fibonacci–Mahler growth constant)* Setting $I_n := \#\mathrm{IsoNF}(n)$, the count $V(a, b)$ of valid Spine-$2$ pairs $(U, V) \in (\mathcal{N} \cap \mathrm{IsoNF})^2$ with $|U| = a$, $|V| = b$, and $S U V \in \mathrm{IsoNF}$ satisfies

$$
V(a, b) \;=\; I_a I_b \;-\; \mathbf{1}_{b = a + 1}\,I_a \;-\; \mathbf{1}_{b \ge a + 2}\,V(b - a - 1, a),
\qquad
I_n \;=\; I_{n-1} + \sum_{a=1}^{n-2} V(a, n - 1 - a) \quad (n \ge 2). \tag{9.8}
$$

Defining Fibonacci numbers $F_1 = F_2 = 1$ and $F_{k+2} = F_{k+1} + F_k$, the ordinary generating function $F_{\mathrm{Iso}}(z) = \sum_{n=1}^{\infty} I_n z^n$ satisfies the exact Fibonacci–Mahler functional equation

$$
F_{\mathrm{Iso}}(z) \;=\; z + z\,F_{\mathrm{Iso}}(z) + \sum_{k=1}^{\infty} (-1)^{k-1} z^{F_{k+2}-1}\Bigl(F_{\mathrm{Iso}}\bigl(z^{F_k}\bigr)\,F_{\mathrm{Iso}}\bigl(z^{F_{k+1}}\bigr) - z^{F_{k+1}} F_{\mathrm{Iso}}\bigl(z^{F_{k+2}}\bigr)\Bigr), \tag{9.9}
$$

whose dominant singularity is a square-root branch point at $r_{\mathrm{Iso}} \approx 0.3439236475 > \frac{1}{3}$, yielding the exponential growth constant $\gamma_{\mathrm{Iso}} = r_{\mathrm{Iso}}^{-1} \approx 2.9076221057 < 3$.

*Proof.*
For (i), if $[P]_{=_S} = \{P\}$, acyclicity of $\to_S$ (Proposition 2.4(i)) forbids both $P \to_S Q$ and $M \to_S P$, so $P \in \mathrm{IsoNF}$; conversely, if $P \in \mathrm{IsoNF}$ and $P =_S Q$, Church–Rosser gives a common reduct $D$ with $P \to_S^* D$ and $Q \to_S^* D$, forcing $D \equiv P$ by $P \in \mathrm{NF}$ and $Q \equiv P$ because any non-empty reduction $Q \to_S^+ P$ ends in a final single step $M' \to_S P$. Since any predecessor $M \to_S P$ of a closed term $P \in \mathcal{T}_S$ is itself closed ($S X Y Z \to_S (X Z)(Y Z)$ preserves variable sets from contractum to redex), $\mathrm{GoE}$ and absence of single-step predecessors coincide on $\mathcal{T}_S$, so $P \in \mathrm{GoE} \iff P \in \mathrm{IsoNF}$ for $P \in \mathcal{N}$. Because every redex $S X Y Z$ and contractum $(X Z)(Y Z)$ has leaf count at least $4$, all closed terms of size $\le 3$ ($S, S S, S(S S), S S S$) lie in $\mathrm{GoE}$; at size $4$, the four normal forms are $S(S(S S))$, $S(S S S)$, $S(S S)S$, and $S S (S S)$, among which only $S S (S S)$ has a predecessor ($S S S S \to_S S S (S S)$).

For $S U \in \mathcal{N}$, no root contraction can produce $S U$ because any root contractum $(X Z)(Y Z)$ has compound left child $X Z$ ($|X Z| \ge 2 > 1 = |S|$), and $S$ is irreducible; hence $M \to_S^+ S U \iff \exists U_0,\, M \equiv S U_0 \land U_0 \to_S^+ U$, giving $S U \in \mathrm{GoE} \iff U \in \mathrm{GoE}$. For $S U V \in \mathcal{N}$ ($U, V \in \mathcal{N}$), backward induction along $M \to_S^* S U V$ shows that either no root step occurs ($M \equiv S U_0 V_0$ with $U_0 \to_S^* U$ and $V_0 \to_S^* V$) or a last root step $S S Y Z \to_S (S Z)(Y Z)$ occurs ($M \to_S^* S S Y Z$ with $Z \to_S^* U$ and $Y Z \to_S^* V$). In the second case, $Y Z \in \mathrm{WN} = \mathrm{SN}$ implies $Y \in \mathrm{SN}$, so $Y \to_{\mathrm{lo}}^* Y_0 \in \mathcal{N}$, and confluence on $Y_0 U \leftarrow_S^* Y Z \to_S^* V \in \mathcal{N}$ gives $Y_0 U \to_S^* V$ with $|Y_0| + |U| \le |V|$ (conversely, any such $Y_0$ gives $S S Y_0 U \to_S (S U)(Y_0 U) \to_S^* S U V$, so $S S Y_0 U \to_S^+ S U V$). Moreover, once $V \in \mathrm{GoE}$, no closed term can reduce in one or more steps to $V$, so $Y_0 U \to_S^* V$ holds if and only if $Y_0 U \equiv V$, which is equivalent to $V$ having syntactic form $Y U$ (since any subterm $Y$ of $V \in \mathcal{N}$ automatically lies in $\mathcal{N}$).

For (ii), if $|V| \le |U|$, then for every $Y \in \mathcal{T}_S$ we have $|Y U| = |Y| + |U| \ge 1 + |U| > |V|$, ruling out $V \equiv Y U$ and giving $S U V \in \mathrm{GoE}$. Induction on $n$ using $S U \in \mathrm{GoE} \iff U \in \mathrm{GoE}$ immediately places $R_{n-1} \in \mathrm{IsoNF}$ for every $n \ge 1$.

For (iii), every closed normal form of size $m + 2 \ge 2$ has spine length $1$ or $2$, decomposing disjointly into $S U$ ($U \in \mathcal{N}$ of size $m + 1$) and $(S A_1) A_2$ ($A_1, A_2 \in \mathcal{N}$ with $|A_1| + |A_2| = m + 1$), establishing the shifted Motzkin recurrence $\#\mathcal{N}(n) = M_{n-1}$ whose generating function $M_{\mathrm{NF}}(z) = z + z M_{\mathrm{NF}}(z) + z M_{\mathrm{NF}}(z)^2 = \frac{1 - z - \sqrt{(1+z)(1-3z)}}{2z}$ has dominant singularity $z = \frac{1}{3}$ ($\gamma_{\mathrm{NF}} = 3$). Because $R_{n-1} \in \mathrm{IsoNF} \subseteq \mathcal{N} \subseteq \mathrm{SN}$, we have $1 \le \#\mathrm{IsoNF}(n) \le \#\mathcal{N}(n) \le \#\mathrm{SN}(n)$, and (9.7) follows from the constructive $\mathrm{SN}$ decay bound proved in Theorem 9.10(ii) below; direct recursive evaluation verifies the exact counts through $n = 11$.

For (iv), let $\mathcal{I}_m := \{ P \in \mathcal{N} \cap \mathrm{IsoNF} : |P| = m \}$ ($I_m = \#\mathcal{I}_m$). By (i), $(U, V) \in \mathcal{I}_a \times \mathcal{I}_b$ fails $S U V \in \mathrm{IsoNF}$ if and only if $V \equiv Y U$ for some $Y$. When $b \le a$, no such $Y$ exists, so $V(a, b) = I_a I_b$. When $b = a + 1$, $|Y| = 1$ forces $Y \equiv S$ and $V \equiv S U \in \mathcal{I}_{a+1}$ for each $U \in \mathcal{I}_a$, subtracting $I_a$. When $b \ge a + 2$, $|Y| = b - a \ge 2$ and $V \equiv Y U \in \mathcal{N}$ force $Y \equiv S W$ with $|W| = b - a - 1 \ge 1$, so $V \equiv S W U$; by (i), $S W U \in \mathcal{I}_b$ (given $U \in \mathcal{I}_a$) holds if and only if $W \in \mathcal{I}_{b-a-1}$ and $U \not\equiv Z W$, which bijects the excluded pairs $(U, V)$ onto the $V(b - a - 1, a)$ valid pairs $(W, U) \in \mathcal{I}_{b-a-1} \times \mathcal{I}_a$, proving (9.8). Setting $S_1(x, y) := \sum_{a, b \ge 1} V(a, b)\,x^a y^b$, multiplying (9.8) by $x^a y^b$ and summing over $a, b \ge 1$ (with $w = b - a - 1 \ge 1$ in the third term) gives

$$
S_1(x, y) \;=\; F_{\mathrm{Iso}}(x)\,F_{\mathrm{Iso}}(y) \;-\; y\,F_{\mathrm{Iso}}(x y) \;-\; y\,S_1(y, x y).
$$

Iterating $(x_k, y_k) \mapsto (y_k, x_k y_k)$ from $(x_1, y_1) = (z, z) = (z^{F_1}, z^{F_2})$ produces $(x_k, y_k) = (z^{F_k}, z^{F_{k+1}})$ with $x_k y_k = z^{F_{k+2}}$ and prefactor $(-1)^{k-1} z \prod_{j=1}^{k-1} y_j = (-1)^{k-1} z^{1 + \sum_{j=2}^k F_j} = (-1)^{k-1} z^{F_{k+2}-1}$. Substituting $F_{\mathrm{Iso}}(z) = z + z F_{\mathrm{Iso}}(z) + z S_1(z, z)$ yields (9.9). Separating $k = 1$ writes (9.9) as $z\,F_{\mathrm{Iso}}(z)^2 - B(z)\,F_{\mathrm{Iso}}(z) + C(z) = 0$, where $B(z) = 1 - z + z^2 F_{\mathrm{Iso}}(z^2)$ and $C(z) = z - z^2 F_{\mathrm{Iso}}(z^2) + z^4 F_{\mathrm{Iso}}(z^3) + \sum_{k=3}^{\infty} (-1)^{k-1} z^{F_{k+2}-1}(F_{\mathrm{Iso}}(z^{F_k}) F_{\mathrm{Iso}}(z^{F_{k+1}}) - z^{F_{k+1}} F_{\mathrm{Iso}}(z^{F_{k+2}}))$. Since $I_n \le M_{n-1} \le 3^n$ gives $r_{\mathrm{Iso}} \ge \frac{1}{3}$, for $|z| < 0.58 < \sqrt{1/3} \le \sqrt{r_{\mathrm{Iso}}}$ every higher Mahler argument satisfies $|z^{F_k}| \le |z|^2 < r_{\mathrm{Iso}}$, so $B(z)$ and $C(z)$ are analytic across a neighborhood of $r_{\mathrm{Iso}}$. Solving the discriminant vanishing condition $B(r_{\mathrm{Iso}})^2 - 4 r_{\mathrm{Iso}} C(r_{\mathrm{Iso}}) = 0$ locates the simple root $r_{\mathrm{Iso}} = 0.3439236474519548\dots > \frac{1}{3}$, yielding $\gamma_{\mathrm{Iso}} = r_{\mathrm{Iso}}^{-1} = 2.9076221056875632\dots < 3$. $\square$

### 9.4. Small-Term Catalan Census and Sharp Minimality Thresholds

By Section 2.1, the closed $S$-terms of leaf size $n \ge 1$ have cardinality $C_{n-1} = \frac{1}{n}\binom{2n-2}{n-1}$. Table 9 reports the exact cardinalities of isolated normal forms ($\mathrm{IsoNF}$), closed normal forms ($\mathcal{N}$), strongly normalizing terms ($\mathrm{SN}$), productive terms ($\mathrm{Prod}$), and the four functional order classes $\mathrm{Ord}_k := \{ M \in \mathcal{T}_S : \mathrm{ord}(M) = k \}$ ($k \in \{0, 1, 2, 3\}$, where $\mathrm{Ord}_0 = \overline{\mathrm{HN}}$ and $\mathrm{Ord}_1 \sqcup \mathrm{Ord}_2 \sqcup \mathrm{Ord}_3 = \mathrm{HN}$) for $1 \le n \le 11$ (a cumulative total of $23{,}714$ trees, extended by dynamic programming through $n = 150$).

**Table 9.** Exact Catalan phase and functional-order census of closed $S$-terms for leaf sizes $1 \le n \le 11$ and sharp onset thresholds.

| $n$ | $C_{n-1}$ | $\#\mathrm{IsoNF}$ | $\#\mathcal{N}$ | $\#\mathrm{SN}$ | $\#\mathrm{Prod}$ | $\#\mathrm{Ord}_3$ | $\#\mathrm{Ord}_2$ | $\#\mathrm{Ord}_1$ | $\#\mathrm{Ord}_0$ | Sharp Structural Threshold |
| ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | :--- |
| $1$ | $1$ | $1$ | $1$ | $1$ | $1$ | $1$ | $0$ | $0$ | $0$ | Unique atom $S$ ($\mathrm{ord} = 3$) |
| $2$ | $1$ | $1$ | $1$ | $1$ | $1$ | $1$ | $0$ | $0$ | $0$ | Unique Spine-$1$ comb $S S$ ($\mathrm{ord} = 3$) |
| $3$ | $2$ | $2$ | $2$ | $2$ | $2$ | $1$ | $1$ | $0$ | $0$ | Minimal $\mathrm{ord} = 2$ ($S S S$); all in $\mathrm{IsoNF}$ |
| $4$ | $5$ | $3$ | $4$ | $5$ | $5$ | $1$ | $4$ | $0$ | $0$ | Minimal redex $S S S S$; non-$\mathrm{GoE}$ $S S(S S)$ |
| $5$ | $14$ | $7$ | $9$ | $14$ | $14$ | $1$ | $12$ | $1$ | $0$ | Unique minimal $\mathrm{ord} = 1$ ($S(S S S)S$) |
| $6$ | $42$ | $15$ | $21$ | $42$ | $42$ | $1$ | $32$ | $9$ | $0$ | Universal $\mathrm{SN}$ and deterministic $\to_S$ ($n \le 6$) |
| $7$ | $132$ | $37$ | $51$ | $130$ | $130$ | $1$ | $83$ | $48$ | $0$ | Minimal $\overline{\mathrm{SN}}$ ($X_1, X_2$); $1$-step diamond break |
| $8$ | $429$ | $87$ | $127$ | $388$ | $388$ | $1$ | $240$ | $173$ | $15$ | Minimal $\mathrm{Ord}_0 = \overline{\mathrm{HN}}$ ($15$); $\mathrm{Prod} = \mathrm{SN}$ ($n \le 8$) |
| $9$ | $1{,}430$ | $218$ | $323$ | $1{,}154$ | $1{,}155$ | $1$ | $739$ | $554$ | $136$ | Unique minimal $\mathrm{Prod} \setminus \mathrm{SN}$ ($Z_0$); $15$ in $\mathrm{RNF}\setminus\mathrm{HN}$ |
| $10$ | $4{,}862$ | $546$ | $835$ | $3{,}381$ | $3{,}383$ | $1$ | $2{,}380$ | $1{,}740$ | $741$ | $S Z_0$ and Zachos's $Z_{\mathrm{Zac}} \equiv G_0 G_0$ appear |
| $11$ | $16{,}796$ | $1{,}393$ | $2{,}188$ | $9{,}967$ | $9{,}972$ | $1$ | $7{,}910$ | $5{,}685$ | $3{,}200$ | Normalizing fraction $\#\mathrm{SN} / C_{10} \approx 59.34\%$ |

**Theorem 9.8 (Sharp small-term minimality and confluence thresholds).**
Across all closed $S$-terms $M \in \mathcal{T}_S$:

- (i) *(Universal $\mathrm{SN}$ and determinism up to size $6$)* Every closed $S$-term with $|M| \le 6$ ($65$ terms in total) is strongly normalizing and satisfies $\#\mathrm{Redex}(M) \le 1$, so one-step multiway reduction $M \to_S N$ is deterministic for $|M| \le 6$.
- (ii) *(Size-$7$ non-halting and strict diamond thresholds)* Among the $132$ closed $S$-terms with $|M| = 7$, all $132$ lie in $\mathrm{HN}$, $130$ lie in $\mathrm{SN}$, and exclusively $X_1 \equiv S(S S)S S S S$ and $X_2 \equiv S S S (S S) S S$ fail to normalize. Exactly $3$ terms of size $7$ admit multiway branching ($\#\mathrm{Redex}(M) = 2$): $S S S (S S S S)$, $S S (S S S S) S$, and $S(S S S S) S S$. Among all $197$ terms with $|M| \le 7$, $S S S (S S S S)$ is the unique counterexample to the strict one-step $\to_S$ diamond property (joining instead in one parallel step at $\mathrm{gk}(S S S (S S S S))$).
- (iii) *(Size-$8$ unsolvability threshold and $\mathrm{Prod} = \mathrm{SN}$)* Every closed $S$-term with $|M| \le 7$ is solvable; at $|M| = 8$ ($429$ terms), $15$ terms lie in $\overline{\mathrm{HN}}$ (all evaluating to $q_{34}$ in $\mathcal{A}_{36}$, such as $S A S A$, $S S S(S A)S$, and $S(S S)S S S S S$). Moreover, $M \in \mathrm{Prod}$ if and only if $M \in \mathrm{SN}$ for all $626$ closed $S$-terms with $|M| \le 8$.
- (iv) *(Unique size-$9$ productive non-$\mathrm{SN}$ combinator and minimal $\mathrm{RNF} \setminus \mathrm{HN}$)* Out of all $2{,}056$ closed $S$-terms with $|M| \le 9$, $Z_0 \equiv S(S(S S))(S(S S))(S S)$ ($9$ leaves, reducing in one step to $Z_{\mathrm{Zac}}$) is the *unique* productive non-normalizing $S$-term. Size $9$ is also the minimal leaf size of $\mathrm{RNF} \setminus \mathrm{HN}$, inhabited by the $15$ terms $U S$ ($q_{35}$ in $\mathcal{A}_{36}$) obtained by applying the $15$ size-$8$ unsolvable terms $U$ to $S$.

*Proof.*
Constructive tree enumeration generates for each $n \ge 1$ the duplicate-free list $\mathcal{L}_n$ of all $C_{n-1}$ closed $S$-trees via binary splits $n = n_1 + n_2$ ($n_1, n_2 \ge 1$). Applying the sound and complete algebraic characterizations of Theorems 6.2, 6.8, 6.14, and 6.25 across $\mathcal{L}_1, \dots, \mathcal{L}_{11}$ establishes all $\mathrm{SN}$, $\mathrm{HN}$, $\mathrm{Prod}$, $\mathrm{Ord}_k$, and $\mathrm{RNF} \setminus \mathrm{HN}$ counts and isolates $\{X_1, X_2\}$ at $n = 7$, the $15$ unsolvable witnesses at $n = 8$ (notice that by (6.10), any $M \equiv P Q \in \mathrm{RNF} \setminus \mathrm{HN}$ requires $P \in \overline{\mathrm{HN}}$, hence $|P| \ge 8$ and $|P Q| = |P| + |Q| \ge 8 + 1 = 9$, with equality if and only if $|P| = 8$ and $Q \equiv S$), and the unique inhabitant $Z_0$ of $\mathrm{Prod} \setminus \mathrm{SN}$ at $n \le 9$.

For the multiway branching and diamond claims in (i)–(ii), every redex $S X Y Z$ has at least $4$ leaves; hence a tree with $\#\mathrm{Redex}(M) \ge 2$ either contains two disjoint redexes (requiring at least $4 + 4 = 8$ leaves) or nests one redex strictly inside an argument of another (requiring at least $3 + 4 = 7$ leaves, achieved exclusively by placing $S S S S$ in one of the three argument slots of $S \square_1 \square_2 \square_3$ with the remaining two slots equal to $S$). Thus $\#\mathrm{Redex}(M) \le 1$ for $|M| \le 6$. At $|M| = 7$, both $S(S S S S)S S$ and $S S (S S S S) S$ satisfy the strict one-step diamond property because $S S S S$ occurs linearly ($1$ copy) after root contraction, whereas $S S S (S S S S)$ duplicates its third argument:

$$
S S S (S S S S) \;\longrightarrow_S\; S(S S S S)\bigl(S(S S S S)\bigr) \;\equiv\; N_L,
\qquad
S S S (S S S S) \;\longrightarrow_S\; S S S \bigl(S S (S S)\bigr) \;\equiv\; N_R.
$$

Contracting the outer root of $N_R$ yields $S(S S (S S))\bigl(S(S S (S S))\bigr) \equiv \mathrm{gk}(S S S (S S S S))$, which requires *two* sequential $\to_S$ steps from $N_L$ (one in each duplicated copy of $S S S S$), refuting a $1$-step $\to_S$ join while confirming a $1$-step parallel join. $\square$

### 9.5. Analytic Combinatorics, Certified Rational Order Densities, and Catalan Phase Transitions

We conclude our analysis of unguided pure-$S$ rewriting by determining the asymptotic phase diagram of a uniformly random closed $S$-term of $n$ leaves as $n \to \infty$. In quantitative studies of untyped $\lambda$-calculus [10, 33, 11, 21], David et al. [21] proved that asymptotically almost all $\lambda$-terms are strongly normalizing, whereas in full combinatory logic $\mathrm{CL}(S, K)$ Bendkowski, Grygiel, Lescanne, and Zaionc [6, 7, 5] showed via Woods's subgraph-containment theorem [73] that almost no $\{S, K\}$-combinators normalize. In $\mathrm{CL}(S)$, because $\mathrm{SN}$, $\mathrm{Prod}$, $\mathrm{HN}$, and exact functional order $\mathrm{ord} \in \{0, 1, 2, 3\}$ are all recognized by explicit finite deterministic $S$-algebras, their counting sequences obey positive quadratic generating-function systems [24, 29] amenable to both exact rational singularity analysis and elementary all-$n$ constructive bounds over $\mathbb{N}$.

Forming the reachable product of $\mathcal{A}_{\mathrm{SN}} \times \mathcal{A}_P \times \mathcal{A}_{\mathrm{HN}}$ from $(q_0, q_0, q_0)$ yields $146$ reachable state triples: $98$ in $\mathrm{SN}$, $30$ in $\mathrm{Prod} \setminus \mathrm{SN}$, $17$ in $\mathrm{HN} \setminus \mathrm{Prod}$, and $1$ in $\overline{\mathrm{HN}}$, confirming the strict global inclusions $\mathrm{IsoNF} \cap \mathcal{T}_S \subsetneq \mathcal{N} \subsetneq \mathrm{SN} \subsetneq \mathrm{Prod} \subsetneq \mathrm{HN} \subsetneq \mathcal{T}_S$. Simultaneously, partitioning $Q_{\mathrm{HN}}$ by nilpotency index under $\tau_{\mathrm{HN}}(q) = q \odot_{\mathrm{HN}} \infty_{\mathrm{HN}}$ (Theorem 6.25(i)) decomposes $Q_{\mathrm{HN}} = Q_{\mathrm{ord}=0} \sqcup Q_{\mathrm{ord}=1} \sqcup Q_{\mathrm{ord}=2} \sqcup Q_{\mathrm{ord}=3}$ into $1 + 11 + 17 + 6 = 35$ states. We first establish exact all-$n$ combinatorial identities and constructive Catalan lower bounds for every order stratum.

**Proposition 9.9 (Catalan order partition, uniqueness of order $3$, and universal lower bounds).**
Let $\#\mathrm{Ord}_k(n) := \#\{ M \in \mathcal{T}_S : |M| = n,\; \mathrm{ord}(M) = k \}$ for $k \in \{0, 1, 2, 3\}$ and $n \ge 1$.

- (i) *(Exact Catalan partition and universal uniqueness of order $3$)* For every $n \ge 1$,

$$
\#\mathrm{Ord}_0(n) = \#\overline{\mathrm{HN}}(n), \qquad
\#\mathrm{Ord}_1(n) + \#\mathrm{Ord}_2(n) + \#\mathrm{Ord}_3(n) = \#\mathrm{HN}(n), \qquad
\sum_{k=0}^3 \#\mathrm{Ord}_k(n) = C_{n-1},
$$

and $\#\mathrm{Ord}_3(n) = 1$ holds identically for every $n \ge 1$ (inhabited solely by the right comb $R_{n-1}$).
- (ii) *(Universal all-$n$ positive-density lower bounds for orders $0, 1, 2$ and $\mathrm{HN}$)* Unconditionally for all $n$ above each sharp onset threshold:

$$
C_{n-2} \;\le\; \#\mathrm{Ord}_2(n) + 1 \;\; (n \ge 2), \qquad
C_{n-5} \;\le\; \#\mathrm{Ord}_1(n) \;\; (n \ge 5), \qquad
C_{n-8} \;\le\; \#\mathrm{Ord}_0(n) \;\; (n \ge 8), \tag{9.10}
$$

with equality $1 = 1$ at $n = 2$ (for $\#\mathrm{Ord}_2(2) + 1$) and $n = 5$ (for $\#\mathrm{Ord}_1(5)$). Furthermore,

$$
2\,C_{n-2} \;\le\; \#\mathrm{HN}(n) \quad (n \ge 3)
\qquad\text{and}\qquad
\#\mathrm{HN}(n) + C_{n-8} \;\le\; C_{n-1} \quad (n \ge 8), \tag{9.11}
$$

which implies $\#\mathrm{HN}(n) + C_{n-9} \le C_{n-1}$ and $\frac{1}{2} < \frac{\#\mathrm{HN}(n)}{C_{n-1}} \le 1 - \frac{C_{n-8}}{C_{n-1}}$ for every $n \ge 8$.

*Proof.*
Part (i) follows directly from Theorem 6.25(i)–(ii): $\mathrm{ord}(M) = \mathrm{ord}_{\mathrm{HN}}(\llbracket M \rrbracket_{\mathrm{HN}})$ partitions the duplicate-free tree list $\mathcal{L}_n$ of length $C_{n-1}$ into the four disjoint fibers of $Q_{\mathrm{ord}=k}$ ($k = 0, 1, 2, 3$), with $Q_{\mathrm{ord}=0} = \{\infty_{\mathrm{HN}}\}$ and $\mathcal{L}_n \cap \mathrm{Ord}_3 = \{R_{n-1}\}$.

For (ii), consider first $n \ge 2$: for every closed tree $R \in \mathcal{L}_{n-1}$ ($C_{n-2}$ trees), the Spine-$1$ normal form $S R$ has $\llbracket S R \rrbracket_{\mathrm{HN}} = q_0 \odot_{\mathrm{HN}} \llbracket R \rrbracket_{\mathrm{HN}} \in \{q_1, \dots, q_5, q_{10}, q_{14}, q_{18}, q_{27}\} \subseteq Q_{\mathrm{ord}=2} \sqcup Q_{\mathrm{ord}=3}$ across all $35$ values of $\llbracket R \rrbracket_{\mathrm{HN}} \in Q_{\mathrm{HN}}$. Injectivity of $R \mapsto S R$ yields $C_{n-2} \le \#\mathrm{Ord}_2(n) + \#\mathrm{Ord}_3(n) = \#\mathrm{Ord}_2(n) + 1$. Second, for $n \ge 5$, fix the $4$-leaf generator $L_1 \equiv S(S S S)$, which satisfies $\llbracket L_1 \rrbracket_{\mathrm{HN}} = q_7$. Direct inspection across all $35$ states $r \in Q_{\mathrm{HN}}$ confirms $q_7 \odot_{\mathrm{HN}} r \in Q_{\mathrm{ord}=1}$ identically; hence $R \mapsto L_1 R$ injects $\mathcal{L}_{n-4}$ ($C_{n-5}$ trees) into $\mathrm{Ord}_1$ of size $n$. Third, for $n \ge 8$, fix the $7$-leaf generator $L_0 \equiv S S S (S(S S S))$, which satisfies $\llbracket L_0 \rrbracket_{\mathrm{HN}} = q_{23}$. Inspection across all $35$ states $r \in Q_{\mathrm{HN}}$ confirms $q_{23} \odot_{\mathrm{HN}} r = \infty_{\mathrm{HN}}$ identically; hence $R \mapsto L_0 R$ injects $\mathcal{L}_{n-7}$ ($C_{n-8}$ trees) into $\mathrm{Ord}_0 = \overline{\mathrm{HN}}$ of size $n$, proving both $C_{n-8} \le \#\mathrm{Ord}_0(n)$ and $\#\mathrm{HN}(n) + C_{n-8} = C_{n-1} - \#\mathrm{Ord}_0(n) + C_{n-8} \le C_{n-1}$. Finally, for $n \ge 3$, every tree $U \in \mathcal{L}_{n-1}$ is an application $U \equiv A_1 A_2$, and the disjoint injections $U \mapsto S U \in \mathrm{HNF}_1$ and $(A_1, A_2) \mapsto S A_1 A_2 \in \mathrm{HNF}_2$ yield $\#\mathrm{HN}(n) \ge C_{n-2} + C_{n-2} = 2 C_{n-2}$. $\square$

For any finite $S$-algebra $\mathcal{A} = (Q, q_0, \odot)$, let $L_q(z) = \sum_{n=1}^{\infty} a_q(n)\,z^n$ denote the ordinary generating function in which $z$ marks $S$-leaves and $a_q(n) = \#\{ M \in \mathcal{T}_S : |M| = n,\; \llbracket M \rrbracket_{\mathcal{A}} = q \}$. Root decomposition translates into the positive quadratic polynomial system

$$
L_q(z) \;=\; \delta_{q, q_0}\,z \;+\; \sum_{\substack{(r, s) \in Q^2 \\ r \odot s = q}} L_r(z)\,L_s(z)
\qquad (q \in Q), \tag{9.12}
$$

whose total sum satisfies $\sum_{q \in Q} L_q(z) = T(z) = \sum_{n=1}^{\infty} C_{n-1} z^n = \frac{1 - \sqrt{1 - 4z}}{2}$, singular at the Catalan radius $z = \frac{1}{4}$ where $[z^n] T(z) = C_{n-1} \sim \frac{4^{n-1}}{\sqrt{\pi}\,n^{3/2}}$.

**Theorem 9.10 (Certified rational Catalan order densities, subcritical decay, and six-tier growth spectrum).**
Let $\#\mathrm{SN}(n)$, $\#\mathrm{Prod}(n)$, $\#\mathrm{HN}(n)$, and $\#\mathrm{Ord}_k(n)$ ($k \in \{0, 1, 2, 3\}$) denote the exact leaf-size-$n$ cardinalities in $\mathcal{T}_S$.

- (i) *(Certified rational stationary algebra of $\mathcal{A}_{\mathrm{HN}}$ and exact Catalan order densities)* At the Catalan singularity $z = \frac{1}{4}$ ($u = \sqrt{1 - 4z} = 0$), the $35$-variable system (9.12) for $\mathcal{A}_{\mathrm{HN}}$ admits an exact dyadic-ternary rational fixed point $a_q = L_q(\frac{1}{4}) \in 2^{-22} 3^{-3}\mathbb{Z}$ ($2^{22}\cdot 3^3 = 113{,}246{,}208$, with $\sum_{q \in Q_{\mathrm{HN}}} a_q = \frac{1}{2}$ and $a_{\infty_{\mathrm{HN}}} = \frac{3{,}366{,}067}{113{,}246{,}208}$), and the singular Puiseux expansion $L_q(z) = a_q - \frac{1}{2}\pi_q \sqrt{1 - 4z} + O(1 - 4z)$ is governed by the unique normalized rational eigenvector $\pi \in 2^{-18} 3^{-3}\mathbb{Z}^{35}$ ($2^{18}\cdot 3^3 = 7{,}077{,}888$) satisfying $\sum_{q \in Q_{\mathrm{HN}}} \pi_q = 1$ and

$$
\pi_q \;=\; \sum_{\substack{(i, j) \in Q_{\mathrm{HN}}^2 \\ i \odot_{\mathrm{HN}} j = q}} (a_i \pi_j + \pi_i a_j)
\qquad (q \in Q_{\mathrm{HN}}).
$$

Summing $\pi_q$ over $Q_{\mathrm{ord}=k}$ yields the exact limiting Catalan densities $c_k := \lim_{n \to \infty} \frac{\#\mathrm{Ord}_k(n)}{C_{n-1}}$:

$$
c_0 \;=\; \frac{2{,}648{,}215}{7{,}077{,}888}, \qquad
c_1 \;=\; \frac{1{,}864{,}553}{7{,}077{,}888}, \qquad
c_2 \;=\; \frac{835}{2{,}304} \;=\; \frac{2{,}565{,}120}{7{,}077{,}888}, \qquad
c_3 \;=\; 0, \tag{9.13}
$$

satisfying $c_0 + c_1 + c_2 + c_3 = 1$ ($c_0 \approx 0.3741532785$, $c_1 \approx 0.2634335271$, $c_2 \approx 0.3624131944$) and total solvable density

$$
c_{\mathrm{HN}} \;:=\; \lim_{n \to \infty} \frac{\#\mathrm{HN}(n)}{C_{n-1}}
\;=\; c_1 + c_2 + c_3
\;=\; \frac{4{,}429{,}673}{7{,}077{,}888}
\;=\; \frac{4{,}429{,}673}{2^{18} \cdot 3^3}
\;\approx\; 0.6258467215. \tag{9.14}
$$

- (ii) *(Algebraic singularities, constructive decay of $\mathrm{SN}$ and $\mathrm{Prod}$, and six-tier growth spectrum)* Because $\infty_{\mathrm{SN}}$ in $\mathcal{A}_{\mathrm{SN}}$ and $\infty_P$ in $\mathcal{A}_P$ are two-sided absorbing sinks coupled into top $4$-state strongly connected components ($\{q_6, q_{25}, q_{29}, q_{30}\}$ with pivot $q_{30}$ in $\mathcal{A}_{\mathrm{SN}}$; $\{q_{18}, q_{24}, q_{29}, q_{33}\}$ with pivot $q_{29}$ in $\mathcal{A}_P$), the generating functions $\sum_{q \in F_{\mathrm{SN}}} L_q(z)$ and $\sum_{q \in F_P} L_q(z)$ have dominant square-root singularities $r_{\mathrm{SN}} < \frac{1}{3}$ and $r_P < r_{\mathrm{SN}}$ strictly exceeding $\frac{1}{4}$, governed by irreducible degree-$35$ minimal polynomials $P_{\mathrm{SN}}(z), P_P(z) \in \mathbb{Z}[z]$:

$$
\begin{aligned}
P_{\mathrm{SN}}(z) &\;=\; 8 z^{35} + 28 z^{34} - 76 z^{33} - 384 z^{32} + \cdots - 5550 z^{10} + 3898 z^9 + \cdots - 73 z^3 - 3 z^2 + 7 z - 1, \\
P_P(z) &\;=\; 12 z^{35} + 48 z^{34} - 88 z^{33} - 584 z^{32} - \cdots - 5546 z^{10} + 3898 z^9 + \cdots - 73 z^3 - 3 z^2 + 7 z - 1,
\end{aligned}
$$

with exponential growth constants $\gamma_{\mathrm{SN}} = r_{\mathrm{SN}}^{-1} \approx 3.3699195015 < \gamma_P = r_P^{-1} \approx 3.3699837893 < 4$. Constructively over $\mathbb{N}$ (at rational test point $z_0 = \frac{37}{125} = 0.296 < r_P < r_{\mathrm{SN}}$, where $\frac{1}{4 z_0} = \frac{125}{148}$ and certified majorants yield base $\frac{250}{259} < 1$), for every $n \ge 1$:

$$
\frac{\#\mathrm{SN}(n)}{C_{n-1}} \;\le\; 51.39438 \cdot \Bigl(\frac{250}{259}\Bigr)^n,
\qquad
\frac{\#\mathrm{Prod}(n)}{C_{n-1}} \;\le\; 51.42860 \cdot \Bigl(\frac{250}{259}\Bigr)^n. \tag{9.15}
$$

Combining Parts (i)–(ii) with Theorem 9.7(iii)–(iv) and Proposition 9.9(i) yields six strictly separated exponential growth rates $\gamma_{\mathcal{K}} := \lim_{n \to \infty} \bigl(\#\mathcal{K}(n)\bigr)^{1/n}$ across $\mathrm{CL}(S)$:

$$
1 \;=\; \gamma_{\mathrm{Ord}_3}
\;<\; \gamma_{\mathrm{Iso}} \approx 2.907622
\;<\; \gamma_{\mathrm{NF}} = 3
\;<\; \gamma_{\mathrm{SN}} \approx 3.369920
\;<\; \gamma_P \approx 3.369984
\;<\; \gamma_{\mathrm{Ord}_0} = \gamma_{\mathrm{Ord}_1} = \gamma_{\mathrm{Ord}_2} = 4. \tag{9.16}
$$

*Proof.*
For (i), in $\mathcal{A}_{\mathrm{HN}}$, because $\infty_{\mathrm{HN}}$ is a left sink ($\infty_{\mathrm{HN}} \odot_{\mathrm{HN}} y = \infty_{\mathrm{HN}}$) rather than a two-sided sink ($q_0 \odot_{\mathrm{HN}} \infty_{\mathrm{HN}} = q_{10} \in F_{\mathrm{HN}}$), substituting $\sum_{s \in Q_{\mathrm{HN}}} L_s(z) = T(z) = \frac{1 - u}{2}$ ($u = \sqrt{1 - 4z}$, $z = \frac{1 - u^2}{4}$) eliminates $L_{\infty_{\mathrm{HN}}}(z)$ and expresses the $34$-variable system over $F_{\mathrm{HN}}$ in a lower-triangular block hierarchy whose diagonal equations are at most quadratic with rational square roots at $u = 0$: specifically, $a_{q_0} = \frac{1}{4}$, $a_{q_1} = \frac{1}{16}$, $\dots$, down to exact integer numerators $N_q = 113{,}246{,}208\,a_q \in \mathbb{N}$ satisfying $2\sum_{q \in Q_{\mathrm{HN}}} N_q = 113{,}246{,}208$ and $113{,}246{,}208\,N_q = 113{,}246{,}208 \cdot 28{,}311{,}552\,\delta_{q, q_0} + \sum_{i \odot_{\mathrm{HN}} j = q} N_i N_j$ across all $35$ states $q \in Q_{\mathrm{HN}}$. Differentiating (9.12) with respect to $u$ at $u = 0$ (where $\frac{dz}{du}\big|_{u=0} = 0$ and $\sum_{q \in Q_{\mathrm{HN}}} L_q(z) = \frac{1}{2} - \frac{1}{2}u$) shows that $\pi_q := -2\frac{d L_q}{du}\big|_{u=0}$ satisfies the linear fixed-point system $\pi = J(a)\,\pi$ with normalization $\sum_{q \in Q_{\mathrm{HN}}} \pi_q = 1$; because the sub-Jacobian of $J(a)$ restricted to $F_{\mathrm{HN}}$ has spectral radius strictly below $1$ (a positive fraction of products leak into $\infty_{\mathrm{HN}}$), $(I - J(a)|_{F_{\mathrm{HN}}})$ is invertible and determines $\pi$ uniquely. Clearing denominators via $\Pi_q = 7{,}077{,}888\,\pi_q \in \mathbb{N}$ verifies $113{,}246{,}208\,\Pi_q = \sum_{i \odot_{\mathrm{HN}} j = q} (N_i \Pi_j + \Pi_i N_j)$ identically across all $35$ states (in particular, $\Pi_q = 0$ on all $6$ states of $Q_{\mathrm{ord}=3}$, whose generating sum $\sum_{q \in Q_{\mathrm{ord}=3}} L_q(z) = \frac{z}{1 - z}$ is analytic at $z = \frac{1}{4}$) and confirms the exact partition sums $\sum_{Q_{\mathrm{ord}=0}} \Pi_q = 2{,}648{,}215$, $\sum_{Q_{\mathrm{ord}=1}} \Pi_q = 1{,}864{,}553$, $\sum_{Q_{\mathrm{ord}=2}} \Pi_q = 2{,}565{,}120$ ($2{,}565{,}120 \cdot 2{,}304 = 835 \cdot 7{,}077{,}888$), and $\sum_{Q_{\mathrm{ord}=3}} \Pi_q = 0$, summing to $7{,}077{,}888$. Because each $L_q(z)$ is an algebraic power series with non-negative coefficients dominated coefficientwise by $T(z)$ (hence analytic in a $\Delta$-domain around $z = \frac{1}{4}$ with no other singularities on $|z| = \frac{1}{4}$), Flajolet and Sedgewick's Transfer Theorem [29, Theorem VI.1 and Section VII.6] yields $[z^n] \sum_{q \in Q_{\mathrm{ord}=k}} L_q(z) = c_k\,C_{n-1}\bigl(1 + O(n^{-1})\bigr)$ for $k \in \{0, 1, 2\}$, proving (9.13) and (9.14).

For (ii), eliminating the $34$ lower transient and acyclic states of $F_{\mathrm{SN}}$ (respectively $F_P$) in (9.12) reduces the top $4$-state strongly connected component to a single quadratic equation $A_2(z)\,Y^2 - B_1(z)\,Y + C_0(z) = 0$ ($\deg A_2 = 30, \deg B_1 = 34, \deg C_0 = 38$) for the pivot generating function $Y = L_{q_{30}}(z)$ (respectively $L_{q_{29}}(z)$), whose discriminant $B_1(z)^2 - 4 A_2(z) C_0(z)$ factors over $\mathbb{Z}[z]$ with minimal positive root $r_{\mathrm{SN}}$ of $P_{\mathrm{SN}}(z)$ (respectively $r_P$ of $P_P(z)$, sharing identical coefficients up to $z^9$ because $\mathrm{Prod}$ and $\mathrm{SN}$ agree for all $n \le 8$ by Theorem 9.8(iii)). By the Drmota–Lalley–Woods Theorem [24, 73], [29, Theorem VII.6], $[z^n] \sum_{q \in F_{\mathrm{SN}}} L_q(z) \sim \alpha_{\mathrm{SN}}\,\gamma_{\mathrm{SN}}^n n^{-3/2}$ and $[z^n] \sum_{q \in F_P} L_q(z) \sim \alpha_P\,\gamma_P^n n^{-3/2}$. To prove (9.15) constructively over $\mathbb{N}$ without complex analysis, choose positive rational upper-envelope vectors $\mathbf{v}_{\mathrm{SN}} \in \mathbb{Q}_{>0}^{38}$ and $\mathbf{v}_P \in \mathbb{Q}_{>0}^{38}$ satisfying quadratic sub-invariance $\delta_{q, q_0}\,z_0 + \sum_{r \odot s = q} v_r v_s \le v_q$ at $z_0 = \frac{37}{125}$. Defining truncated partial sums $S_{q, N}(z_0) = \sum_{n=1}^N a_q(n)\,z_0^n$, induction on $N \ge 1$ shows $S_{q, N+1}(z_0) \le \delta_{q, q_0}\,z_0 + \sum_{r \odot s = q} S_{r, N}(z_0)\,S_{s, N}(z_0) \le v_q$, whence $a_q(n) \le v_q\,z_0^{-n} = v_q (\frac{125}{37})^n$ for every $n \ge 1$. Pairing this upper bound with the inductive Catalan lower bound $C_{n-1} \ge c_0 (\frac{7}{2})^n$ (since $\frac{C_n}{C_{n-1}} = \frac{4n-2}{n+1} \ge \frac{7}{2}$ for all $n \ge 11$, with $1 \le n \le 11$ checked directly) and simplifying

$$
\frac{(125 / 37)^n}{(7 / 2)^n} \;=\; \Bigl(\frac{250}{259}\Bigr)^n
$$

yields the constructive integer inequalities $100{,}000 \cdot 259^n \cdot \#\mathrm{SN}(n) \le 5{,}139{,}438 \cdot 250^n \cdot C_{n-1}$ and $100{,}000 \cdot 259^n \cdot \#\mathrm{Prod}(n) \le 5{,}142{,}860 \cdot 250^n \cdot C_{n-1}$ for all $n \ge 1$, completing (9.15) and (9.16). $\square$

## 10. Constructive Formalization in Lean 4 and Cross-Language Verification

Following the methodology established in large-scale mechanized mathematics and theoretical computer science—such as Gonthier's formalizations of the Four-Color and Odd Order Theorems [31, 32], the Flyspeck verification of the Kepler conjecture by Hales et al. [34], and Forster, Kunze, and Roth's mechanized computability theory [30]—every core theorem, compiler stage, contextual tree transducer, finite $S$-algebra, $\lambda\mathrm{I}$-calculus theorem, and constructive asymptotic inequality in Sections 2–9 has been formalized and kernel-checked in Lean 4 (version 4.33.1; with finite small-term minimality and collision censuses cross-validated by the companion verification suite), unified in the master module `s_challenge_master_headline.lean` across its transitive dependency graph of 202 self-contained formal modules. In this closing section we document the logical axiom footprint, kernel-reduction engineering, and cross-language verification architecture that connect the mathematical proofs of this monograph to the formal artifacts.

### 10.1. Axiom Footprint and Constructive Elimination of Non-Constructive Principles

In Lean 4's Calculus of Inductive Constructions, standard library reasoning may invoke three foundational axioms: propositional extensionality (`propext`), quotient soundness (`Quot.sound`, used internally by Lean's linear arithmetic decision procedure `omega` on `Nat` and `Int`), and Hilbert's choice principle (`Classical.choice`). Across the entire formalization—verified programmatically via `#print axioms` in `TRUST_ZERO_SPEC_CHECK.lean` and `adversarial_referee_audit/axiom_deep_audit.lean`—there are no occurrences of `sorry`, `admit`, user-declared `axiom`s, `partial`, `unsafe`, or `extern` declarations, and every exported theorem in `SChallengeMaster` depends solely on a subset of `[propext, Quot.sound]`, without relying on `Classical.choice`.

Achieving `Classical.choice`-free proofs across infinitary rewriting, Böhm-tree semantics, and $\lambda\mathrm{I}$-standardization required replacing four classical idioms common in paper rewriting theory by explicit constructive witnesses:

1. *Eliminating König's lemma and pigeonhole arguments in termination and non-spiralling.* Classical local-termination proofs [25] infer termination from absence of infinite paths in finitely branching trees via König's lemma, and classical unbounded-growth proofs invoke infinite pigeonhole principles. We replaced these in Section 2 by the exact $\Delta L = -2$ left-subtree drop on leaf-preserving steps, constructive lexicographic path-ordering (LPO) and weight-pair accessibility for Waldmann's $\mathcal{R}_m$ system and Klop's flat $\{S, K\}$-terms, and computable step thresholds for unbounded leaf and redex growth; in Section 6.1 by the rank-$6$ canonical normalizer $\mathrm{app}_{\mathcal{N}}$; in Section 6.2 by automaton-free head conservation paired with the pure-multiplier potential $\mu_{\mathrm{HN}}$ ($B \equiv 0$, $\max A = 30$); and in Section 6.3 by well-founded recursion (`Acc.rec`) on $\nu_{\mathrm{HN}}$ and right-spine strata.
2. *Constructive $\bot$-extraction and productive Böhm joinability.* On closed $S$-terms, productivity $\mathrm{Prod}(M) \equiv \forall d,\, \neg\bot_d(M)$ is a $\Pi_1^0$ predicate whose classical negation $\neg\mathrm{Prod}(M) \implies \exists d,\, \bot_d(M)$ is Markov's principle. Over the Myhill–Nerode minimal $113$-state joint algebra $\mathrm{PH} \subseteq Q_P \times Q_{\mathrm{HN}}$, rank-$10$ critical-pair stratification constructs an explicit depth $d \in \mathbb{N}$ witnessing $\bot_d(M)$ whenever $\llbracket M \rrbracket_P = \infty_P$, yielding the constructive disjunction $\mathrm{Prod}(M) \vee \exists d,\, \bot_d(M)$, while root-normal-form spine peeling constructs explicit common reducts witnessing Böhm-tree faithfulness and decidability of $=_S$ across $\mathrm{Prod} \times \mathcal{T}_S$.
3. *Constructive $\lambda\mathrm{I}$ standardization and $S$-free backward cones.* In Section 7, Church's conservation theorem ($\mathrm{WN}_\beta \iff \mathrm{SN}_\beta$ on $\lambda\mathrm{I}$) [16], Conjecture 40, the hereditary saturation repair $\mathrm{DeepNorm}(M) \iff (M)_\lambda \in \mathrm{SN}_\beta$, and single-constant collapse $\mathrm{DeepNorm}_1$ for Question 34 are proved constructively via de Bruijn parallel $\beta$-reduction and weak-head standardization without classical choice, while Question 32 is resolved via constructive $S$-free anti-redex backward-cone inversion.
4. *Step-indexed deterministic traces and contextual transducers.* In the universal Turing machine, program-free Cyclic Tag System, and pocket tree transducer simulations (Sections 3–4), existential halting witnesses are carried by explicit fuel-indexed evaluators (`uRun`, `InvokeTrace`, `pfIter`, and the two-pass $(25, 23, 136)$ transducer `pocketPFSelect`), avoiding non-constructive witness extraction from transitive closures.

### 10.2. Kernel Reduction Without `native_decide`

Lean 4 provides a tactic `native_decide` that compiles decidable propositions to native machine code, adding the compiler and runtime to the trusted computing base. To keep the trusted computing base confined strictly to Lean 4's small logical kernel, every finite algebraic, Myhill–Nerode, and small-term census check reduces directly inside the kernel's definitional equality checker (`rfl` / `decide`), making no appeal to `native_decide`.

Checking $39^3 = 59{,}319$ $S$-law triples for $\mathcal{A}_{\mathrm{SN}}$ and $\mathcal{A}_P$, $42{,}875$ triples for $\mathcal{A}_{\mathrm{HN}}$, the $35$-override two-dimensional collapse and rank-$10$ critical-pair tables over the $113$-state algebra $\mathrm{PH}$, the $17$-context Myhill–Nerode separation of $\mathrm{PH}$, and the $(25, 23, 136)$ pocket transducer equivalence inside Lean's kernel without stack overflow or quadratic pattern-compilation overhead uses three standard reflection techniques [31]:

1. *Balanced binary tree quantifiers and row factoring.* Universal quantification over finite inductive state types ($3$ to $39$ constructors) and bounded natural intervals is expressed via balanced Boolean conjunction trees (`checkAll1`, `checkAll2`, `checkNat1`, `checkNat2`) accompanied by projection soundness lemmas, and three-variable checks $(x, y, z) \in Q^3$ are factored into $|Q|$ separate two-variable row theorems each proved by `rfl`.
2. *Depth-$6$ and depth-$7$ binary Patricia lookup trees (`PTree64`, `PTree`).* Transition matrices, $113$-state witness tables, and rank tables over $\mathrm{PH}$ are stored as balanced binary trees of depth $6$ or $7$, reducing every state-pair or rank lookup in at most $7$ pointer steps rather than $113$ sequential linear comparisons.
3. *Explicit constructor case-splitting on pattern matches.* Lean 4's equation compiler and `split` tactic occasionally synthesize `Classical.em` on overlapping multi-constructor wildcard branches; replacing wildcard `split` steps with explicit constructor `cases` decompositions eliminates `Classical.choice` throughout the pocket transducer and algebraic parsers.

Similarly, for the root-restarted zipper controller `invoke` (`formal_controller/finite_tree_walker.lean`), whose nested register type `Control` has cardinality $4{,}376{,}490{,}905$, finiteness is proved symbolically via product-list membership (`mem_allControls`: $\forall c,\, c \in \mathrm{allControls}$) without materializing a four-billion-element list, while `pocketPFTransducer` achieves an explicit $(25, 23, 136)$ finite-state realization running in at most $2|M| - 1 + \mathrm{depth}(M)$ transitions.

### 10.3. Syntax Bijections and Cross-Language Parity

Because the formal modules were developed in modular namespaces (`FormalAlgebra`, `FormalTopTermination`, `IntrinsicTheorems`, `Q5SNStratifiedGame`, `FormalQ5Final`, `SimplifiedQ31Q7`, `SimplifiedQ10Q5`, `FormalQ30Q31Deep`, `FormalOrderAndIsolated`, `FormalNoSpiral`, `Conjecture17Obstructions`, `FormalLambdaConjectures`, `FormalQ32`, `FormalWolframFrontier`, `ZeroNavigatorFixedOrder`, `ZeroNavigatorMultiway`, `ZeroNavigatorCellular`, `FormalWolfram12`, `FormalMinimality`, and `FormalAsymptotics`), the master file `s_challenge_master_headline.lean` defines explicit recursive syntax translations (`toAlgebraTerm`, `ofAlgebraTerm`, …) and proves bidirectional round-trip identities together with closedness preservation and one-step rewrite equivalence ($\mathrm{Step}\;M\;N \iff \mathrm{Step}_{\text{mod}}(\tau(M), \tau(N))$) across all pure-$S$ syntax definitions. Thus no discrepancy in associativity, variable indexing, or redex semantics can arise between modules.

In parallel with the Lean 4 development, all compilers, tree-walking selectors, pocket tree transducers, halting automata, finite $S$-algebras (sizes $39, 35, 39, 36, 12, 3, 4$, and $113$), $\lambda\mathrm{I}$ divergence witnesses ($W_9, N_{10}, M_{14}, M_{15}$), Rule 110 normal-form iterators, all-step $\to_{\mathrm{lo}}$ jump-ahead formulas, Garden-of-Eden normal-form recognizers, and Catalan order-density constants are implemented in the standalone Wolfram Language package `wolfram_submission/PureSUniversality.wl` (accompanied by `wolfram_submission/VerifyPureSUniversality.wls`) and an independent Python verification suite (`verify_all_theorems.py` and `wolfram_submission/cross_validate_wl.py`). Automated comparison confirms exact agreement across all shared transition matrices, pure-multiplier table $A$ ($\max A = 30$), compiled Turing machine leaf counts ($1{,}996{,}921$ and $7{,}477{,}337$ leaves), $912$-contraction execution of the $2$-state Busy Beaver, pocket transducer trajectories from $D_{\mathrm{seed}}$, and $130$-digit dynamic programming verification of the Catalan phase transitions and rational order densities through $n = 150$.

## Appendix A. Concordance of Mathematical Results and Formal Artifacts

Table 10 maps the principal theorems, propositions, and lemmas of Sections 2–9 to their corresponding Lean 4 source files, kernel-verified declaration identifiers, exact foundational axiom footprints reported by `#print axioms` (where $\emptyset$ denotes no axioms, $\mathsf{P}$ denotes `[propext]`, and $\mathsf{PQ}$ denotes `[propext, Quot.sound]`), and exported Wolfram Language symbols in `wolfram_submission/PureSUniversality.wl`.

**Table 10.** Concordance between monograph results (Sections 2–9), Lean 4 declarations, axiom footprints, and Wolfram Language symbols.

| Monograph Result | Lean 4 Module Path | Lean 4 Declaration Identifier | Axioms | Wolfram Language Symbol |
| :--- | :--- | :--- | :---: | :--- |
| Prop. 2.2: CR & $\mathrm{WN} = \mathrm{SN}$ | `formal_algebra/s_structural_laws.lean` | `FormalAlgebra.church_rosser`, `wn_implies_sn` | $\mathsf{P}$ | `PureSContractAt` |
| Thm. 2.3: $\Delta L = -2$ & $\lfloor(n-2)^2/4\rfloor$ | `formal_order_and_isolated/leaf_preserving_and_isolated.lean` | `FormalOrderAndIsolated.leftSubtreeSum_leafPresStep`, `leafPres_sn` | $\mathsf{PQ}$ | `PureSLeftSubtreeSum` |
| Prop. 2.4, 2.5: No-spiral & Klop 18 | `formal_no_spiral/waldmann_no_spiral.lean`, `formal_no_spiral/bergstra_and_klop.lean` | `FormalNoSpiral.waldmann_no_spiral`, `klop_theorem_18_flat_sk_sn` | $\mathsf{P}$ | — |
| Prop. 2.11: $8$-leaf open $\overline{\mathrm{SN}}$ | `formal_conjecture17_obstructions/conjecture17_obstructions.lean` | `Conjecture17Obstructions.open_spiral_not_sn` | $\emptyset$ | — |
| Thm. 2.12: Self-right-tail Conj. 17 | `formal_no_spiral/conjecture17_open_spirals.lean` | `FormalNoSpiral.conjecture17_no_open_spiral_unless_self_right_tail` | $\mathsf{P}$ | — |
| Thm. 2.13: Short-loop & near-miss | `formal_conjecture17_obstructions/conjecture17_obstructions.lean` | `Conjecture17Obstructions.no_two_step_open_spiral`, `waldmann_open_parametric_near_miss` | $\mathsf{PQ}$ | — |
| Thm. 2.15: $\mathrm{minRS}_x/\mathrm{minLS}_x$ & $\mathcal{DP}$ | `formal_conjecture17_deep/minmaxrs_deep_obstructions.lean` | `FormalNoSpiral.step_minMaxRS_le`, `conjecture17_iff_no_dpChain_spiral` | $\mathsf{P}$ | — |
| Prop. 3.3: $M(w) \leftrightarrow U_{3,11}$ sim. | `formal_utm/neary_u311_sim.lean`, `formal_utm/neary_encoder.lean` | `source_halts_iff_u_stops`, `encodeSourceInstance_poly_bound` | $\mathsf{PQ}$ | `EncodeNearyU311` |
| Lem. 3.7: Zipper walker bound | `formal_controller/bare_output_and_invoke_trace.lean` | `exists_microtick_le_node_bound` | $\mathsf{PQ}$ | `RootRestartedSelectAddress` |
| Prop. 3.8: $11$-state halt DTA $\mathcal{H}_{11}$ | `formal_controller/halt_tree_automaton.lean` | `haltAutomaton_accepts_eq_rootHalt` | $\mathsf{P}$ | `PureSHaltDetectorQ` |
| Thm. 3.9: Root-restarted UTM | `formal_controller/constructive_endpoint.lean`, `formal_controller/bare_output_and_invoke_trace.lean` | `constructive_fixed_u_to_s_halting`, `decodeBareSTermOutput_correct` | $\mathsf{PQ}$ | `CompileTuringMachineToPureS` |
| Prop. 4.4: Seed genesis $D_{\mathrm{seed}} \to_S^* t_0$ | `formal_program_free/program_free_cts.lean` | `FormalProgramFree.seed_reduces_to_encodeProgramFreeCTS` | $\mathsf{PQ}$ | `EncodeProgramFreeCTS` |
| Thm. 4.5: Program-free CTS univ. | `formal_program_free/program_free_cts.lean` | `FormalProgramFree.program_free_cts_halting_iff_automaton` | $\mathsf{PQ}$ | `ProgramFreePureSSelect` |
| Thm. 4.7: $(25,23,136)$ $\mathcal{T}_{\mathrm{pocket}}$ | `formal_wolfram_frontier/pocket_pf_transducer.lean` | `FormalWolframFrontier.pocketPFSelect_eq_pfSelect`, `pocket_transducer_cts_universality` | $\mathsf{PQ}$ | `ProgramFreePureSSelect` |
| Thm. 5.2: Unary leaf-split univ. | `formal_algebra/trivial_rule_separation.lean` | `FormalAlgebra.TrivialRuleSeparation.fixed_universal_trivial_rule_separation` | $\mathsf{PQ}$ | — |
| Prop. 5.4: $7$/$5$-step shortcuts | `zero_navigator_multiway/multiway_and_q30_theorems.lean` | `ZeroNavigatorMultiway.protected_trie_nonhalting_shortcut_7steps` | $\mathsf{P}$ | — |
| Thm. 5.5: No pure-$S$ Church gate | `zero_navigator_multiway/multiway_and_q30_theorems.lean` | `ZeroNavigatorMultiway.no_church_boolean_pair_in_pure_s` | $\mathsf{P}$ | — |
| Thm. 6.2: $39$-state $\mathcal{A}_{\mathrm{SN}}$ | `formal_algebra/sn_hn_algebras.lean` | `FormalAlgebra.waldmann_theorem_9` | $\mathsf{P}$ | `EvalSNState` |
| Lem. 6.4, 6.6: Head cons. & $B\equiv 0$ | `formal_q10_q5_simplified/q10_thm9_simplified.lean` | `SimplifiedQ10Q5.hasHNF_iff_strongHeadNormalizing` | $\mathsf{PQ}$ | — |
| Prop. 6.7: Pointwise minimal $A$ | `formal_q10_q5_simplified/q10_thm9_simplified.lean` | `SimplifiedQ10Q5.hnA_pointwise_minimal`, `no_masked_rank1_hnA` | $\mathsf{PQ}$ | — |
| Thm. 6.8: Question 10 & Footnote 4 | `formal_q10_q5_simplified/q10_thm9_simplified.lean`, `formal_algebra/sn_hn_algebras.lean` | `SimplifiedQ10Q5.barendregt_open_problem_10_simplified`, `FormalAlgebra.footnote4_rnf_iff` | $\mathsf{PQ}$ | `EvalHNState` |
| Thm. 6.9: Top-termination | `formal_top_termination/top_termination.lean` | `FormalTopTermination.waldmann_theorem_29_top_termination` | $\mathsf{PQ}$ | `IsRootNormalFormQ` |
| Lem. 6.10, 6.11: $\bot$-propagation laws | `formal_q10_q5_simplified/q10_thm9_simplified.lean`, `formal_q10_q5_simplified/q5_simplified.lean` | `SimplifiedQ10Q5.hasBotWithin_app_left`, `hasBot_zachos_app` | $\mathsf{PQ}$ | — |
| Prop. 6.12: $34$-of-$38$ $\mathrm{SN}$ strat. | `q5_sn_stratified_game/sn_stratified_game.lean` | `Q5SNStratifiedGame.unique_nonSN_productive_root_redex_state` | $\mathsf{P}$ | `EvalProductivityState` |
| Thm. 6.14: Question 5 (rank-$10$ $\mathcal{A}_P$) | `formal_q10_q5_simplified/q5_simplified.lean`, `formal_q5_final/q5_completeness.lean` | `SimplifiedQ10Q5.barendregt_open_question_5_simplified` | $\mathsf{PQ}$ | `IsProductivePureSQ` |
| Prop. 6.15: $113$-state $\mathrm{PH}$ minimal | `formal_q10_q5_simplified/q5_simplified.lean` | `SimplifiedQ10Q5.ph_113_nerode_minimal`, `ph_113_quotient_lower_bound` | $\mathsf{PQ}$ | — |
| Prop. 6.16: $8$-leaf $L_{\mathrm{loop}}$ game | `q5_sn_stratified_game/sn_stratified_game.lean` | `Q5SNStratifiedGame.bohm_game_asymmetry_size8` | $\mathsf{P}$ | — |
| Thm. 6.19: Question 7 ($\mathcal{H}/\mathcal{U}$ & mod-$10$) | `SIMPLIFIED_Q31_Q7_BOOK_PROOFS.lean`, `formal_algebra/question7_flipflop.lean` | `SimplifiedQ31Q7.question_7_atomic_leaf_splits`, `FormalAlgebra.one_step_rescue_classification` | $\mathsf{PQ}$ | `Question7AtomicSplitTerm`, `Question7FlipFlopTerm` |
| Thm. 6.20: Question 31 ($\{A A A S^k\}$ & $\mathcal{A}_{36}$) | `SIMPLIFIED_Q31_Q7_BOOK_PROOFS.lean`, `intrinsic_research/intrinsic_theorems.lean` | `SimplifiedQ31Q7.question_31_infinite_family`, `IntrinsicTheorems.aaa_not_conv_aaas` | $\mathsf{PQ}$ | `EvalQuestion31State` |
| Thm. 6.21: $\mathrm{Prod} \times \mathcal{T}_S$ Böhm faithful | `formal_q30_q31_deep/q31_productive_bohm_faithfulness.lean` | `FormalQ30Q31Deep.productive_oneSided_bohm_iff_convS` | $\mathsf{PQ}$ | — |
| Prop. 6.22: Question 30 ($\mathrm{Prod} \times \mathcal{T}_S$ & finiteness) | `formal_q30_q31_deep/q31_productive_bohm_faithfulness.lean`, `formal_q30_q31_deep/q30_finiteness_and_sn_decidability.lean` | `FormalQ30Q31Deep.decideConvProd`, `closed_normalizing_equivClass_finite` | $\mathsf{PQ}$ | — |
| Thm. 6.25: Orders $\{0,1,2,3\}$ ($35,12,3$) | `formal_order_and_isolated/order_classification.lean` | `FormalOrderAndIsolated.visser_van_oostrom_exact_order_exhaustion` | $\mathsf{PQ}$ | `PureSFunctionalOrder` |
| Lem. 7.2: $\lambda\mathrm{I}$ $\mathrm{WN}_\beta \iff \mathrm{SN}_\beta$ | `formal_lambda_conjectures/lambda_standardization_conservation.lean` | `FormalLambdaConjectures.lambdaI_wn_iff_sn` | $\mathsf{PQ}$ | — |
| Thm. 7.3: Conjecture 40 ($\operatorname{ord}_{\mathrm{CL}} = \operatorname{ord}_\lambda$) | `formal_lambda_conjectures/conjecture_40_order.lean` | `FormalLambdaConjectures.conjecture_40_full_cl`, `conjecture_40_pure_s` | $\mathsf{PQ}$ | — |
| Prop. 7.4: $W_9, N_{10}$ $\lambda\beta$-divergers | `formal_lambda_conjectures/conjectures_42_43_and_repair.lean` | `FormalLambdaConjectures.w9_toLam_no_betaNF`, `n10_toLam_no_betaNF` | $\mathsf{PQ}$ | `MinimalLambdaDivergingPureSTerms` |
| Thm. 7.5: Conj. 42/43 refuted & $\mathrm{DeepNorm}$ | `formal_lambda_conjectures/conjectures_42_43_and_repair.lean` | `FormalLambdaConjectures.conjecture_42_and_43_refuted_14_leaves`, `repaired_conjecture_42` | $\mathsf{PQ}$ | `Conjecture42And43Counterexamples` |
| Thm. 7.6: Question 34 ($\mathrm{DeepNorm}_1$ & $\infty_{34}$) | `formal_lambda_conjectures/question_34_hereditary_and_shattering.lean` | `FormalLambdaConjectures.question_34_iff_single_constant_saturation` | $\mathsf{PQ}$ | — |
| Prop. 7.8: $S$-free rigidity & $(8,11)$ pair | `formal_q32_equational/lambda_i_rigidity.lean` | `FormalQ32.sFree_rigidity`, `theoremA_waldmann_8_11_separation` | $\mathsf{PQ}$ | — |
| Thm. 7.9: Question 32 refuted | `formal_q32_equational/question_32_negative_resolution.lean` | `FormalQ32.no_finite_equational_axiomatization_of_lambda_beta` | $\mathsf{PQ}$ | — |
| Prop. 8.1: $6$ strategies & $\mathcal{B}_Z$ | `zero_navigator_fixed_order/zero_nav_fixed_theorems.lean` | `ZeroNavigatorFixedOrder.zachos_unified_quadratic_trace` | $\mathsf{PQ}$ | `EvalBZachosState` |
| Thm. 8.2: $5$-step Case-$3$ ceiling | `zero_navigator_fixed_order/zero_nav_fixed_theorems.lean` | `ZeroNavigatorFixedOrder.no_six_consecutive_case3_li` | $\mathsf{PQ}$ | — |
| Thm. 8.3: Clone barrier & Rule 110 | `zero_navigator_cellular/cellular_and_clones.lean` | `ZeroNavigatorCellular.no_rule110_SN`, `dnand_rule110_correct` | $\mathsf{PQ}$ | `PureSRule110Term` |
| Thm. 9.1: $14$ benchmarks | `formal_wolfram12/wolfram_12_benchmarks.lean` | `FormalWolfram12.wolfram_14_dichotomy_master` | $\mathsf{P}$ | `WolframChallenge12Benchmarks` |
| Prop. 9.2: Context & $s(m)$ jump-ahead | `formal_wolfram12/wolfram_12_benchmarks.lean` | `FormalWolfram12.decideContextHalts_exact`, `jump_ahead_sPrefix_exact` | $\mathsf{P}$ | `PureSJumpAheadOutcome` |
| Thm. 9.4: All-step $\to_{\mathrm{lo}}$ cubic laws | `formal_wolfram_frontier/lo_jump_ahead_and_goe.lean` | `FormalWolframFrontier.zachos_all_step_closed_form`, `wolfram2_vs_w2Twin_shift_14` | $\mathsf{PQ}$ | `ZachosExactLeafCount`, `Wolfram2ExactLeafCount` |
| Prop. 9.5: $A A A$ grammar & subterms | `formal_wolfram_frontier/lo_jump_ahead_and_goe.lean` | `FormalWolframFrontier.aaa_lo_and_multiway_master` | $\mathsf{PQ}$ | — |
| Thm. 9.7: Garden-of-Eden NFs | `formal_wolfram_frontier/lo_jump_ahead_and_goe.lean` | `FormalWolframFrontier.goe_s2_iff`, `decideGardenOfEdenNF_iff` | $\mathsf{PQ}$ | `IsGardenOfEdenNormalFormQ` |
| Thm. 9.8: $n \le 9$ minimality | `formal_census_and_minimality/minimality_theorems.lean` | `FormalMinimality.theorem_A_universal_sn_le_6`, `theorem_F_confluence_and_diamond_thresholds` | $\mathsf{PQ}$ | `PureSCatalanPhaseCensus` |
| Prop. 9.9, Thm. 9.10: Catalan laws | `formal_order_and_isolated/higher_order_catalan_laws.lean`, `formal_asymptotics/asymptotic_laws.lean` | `FormalOrderAndIsolated.exact_rational_order_catalan_densities_certified`, `FormalAsymptotics.sn_and_acceptP_exponential_decay_to_zero` | $\mathsf{PQ}$ | `PureSAsymptoticConstants` |

## References

1. Henk P. Barendregt, *The Lambda Calculus: Its Syntax and Semantics*, Revised edition, Studies in Logic and the Foundations of Mathematics, vol. 103, North-Holland, Amsterdam, 1984.
2. Henk P. Barendregt, Jan A. Bergstra, Jan Willem Klop, and Henri Volken, *Degrees, Reductions and Representability in the Lambda Calculus*, Preprint No. 22, Department of Mathematics, Utrecht University, 1976.
3. Henk P. Barendregt, Wil Dekkers, and Richard Statman, *Lambda Calculus with Types*, Perspectives in Logic, Cambridge University Press, Cambridge, 2013, `doi:10.1017/CBO9781139032636`.
4. Henk P. Barendregt, Jörg Endrullis, Jan Willem Klop, and Johannes Waldmann, "Dance of the Starlings," in Melvin Fitting and Brian Rayman (eds.), *Raymond Smullyan on Self Reference*, Outstanding Contributions to Logic, vol. 14, Springer, Cham, 2017, pp. 67–111, `doi:10.1007/978-3-319-68732-2_5`.
5. Maciej Bendkowski, Katarzyna Grygiel, Pierre Lescanne, and Marek Zaionc, "Combinatorics of $\lambda$-terms: a natural approach," *Journal of Logic and Computation* **27** (2017), no. 8, 2611–2630, `doi:10.1093/logcom/exx018`.
6. Maciej Bendkowski, Katarzyna Grygiel, and Marek Zaionc, "Asymptotic properties of combinatory logic," in *Theory and Applications of Models of Computation (TAMC 2015)*, Lecture Notes in Computer Science, vol. 9076, Springer, Cham, 2015, pp. 62–72, `doi:10.1007/978-3-319-17142-5_7`.
7. Maciej Bendkowski, Katarzyna Grygiel, and Marek Zaionc, "On the likelihood of normalisation in combinatory logic," *Journal of Logic and Computation* **27** (2017), no. 7, 2251–2269, `doi:10.1093/logcom/exx005`.
8. Alessandro Berarducci, "Infinite $\lambda$-calculus and non-sensible models," in Aldo Ursini and Paolo Aglianò (eds.), *Logic and Algebra*, Lecture Notes in Pure and Applied Mathematics, vol. 180, Marcel Dekker, New York, 1996, pp. 339–377, `doi:10.1201/9780203748671-17`.
9. Alessandro Berarducci and Corrado Böhm, "A self-interpreter of lambda calculus having a normal form," in *Computer Science Logic (CSL '92)*, Lecture Notes in Computer Science, vol. 702, Springer, Berlin, 1993, pp. 85–99, `doi:10.1007/3-540-57182-5_7`.
10. Olivier Bodini, Danièle Gardy, and Bernhard Gittenberger, "Lambda-terms of bounded unary height," in *Proceedings of the Eighth Workshop on Analytic Algorithmics and Combinatorics (ANALCO 2011)*, SIAM, 2011, pp. 23–32, `doi:10.1137/1.9781611973013.3`.
11. Olivier Bodini, Danièle Gardy, Bernhard Gittenberger, and Alice Jacquot, "Enumeration of generalized $BCI$ lambda-terms," *The Electronic Journal of Combinatorics* **20** (2013), no. 4, Paper P30, `doi:10.37236/3051`.
12. Mikołaj Bojańczyk and Thomas Colcombet, "Tree-walking automata do not recognize all regular languages," *SIAM Journal on Computing* **38** (2008), no. 2, 658–701, `doi:10.1137/050645427`.
13. Corrado Böhm, "Alcune proprietà delle forme $\beta$-$\eta$-normali nel $\lambda$-$K$-calcolo," Pubblicazioni dell'Istituto per le Applicazioni del Calcolo, no. 696, Rome, 1968, pp. 1–19.
14. Richard Canal, "Complexité de la réduction en logique combinatoire," *RAIRO – Informatique théorique* **12** (1978), no. 4, 339–367, `doi:10.1051/ita/1978120403391`.
15. Panagiotis Cheilaris, John Ramirez, and Stathis Zachos, "Checking in linear time if an $S$-term normalizes," in *8th Panhellenic Logic Symposium*, Ioannina, Greece, July 2011.
16. Alonzo Church, *The Calculi of Lambda-Conversion*, Annals of Mathematics Studies, vol. 6, Princeton University Press, Princeton, NJ, 1941.
17. John Cocke and Marvin L. Minsky, "Universality of tag systems with $P = 2$," *Journal of the ACM* **11** (1964), no. 1, 15–20, `doi:10.1145/321203.321206`.
18. Matthew Cook, "Universality in elementary cellular automata," *Complex Systems* **15** (2004), no. 1, 1–40, `doi:10.25088/ComplexSystems.15.1.1`.
19. Haskell B. Curry, "Grundlagen der kombinatorischen Logik," *American Journal of Mathematics* **52** (1930), no. 3–4, 509–536, 789–834, `doi:10.2307/2370619`.
20. Haskell B. Curry and Robert Feys, *Combinatory Logic, Volume I*, Studies in Logic and the Foundations of Mathematics, North-Holland, Amsterdam, 1958.
21. René David, Katarzyna Grygiel, Jakub Kozik, Christophe Raffalli, Guillaume Theyssier, and Marek Zaionc, "Asymptotically almost all $\lambda$-terms are strongly normalizing," *Logical Methods in Computer Science* **9** (2013), no. 1:2, 1–30, `doi:10.2168/LMCS-9(1:2)2013`.
22. Martin Davis, "A note on universal Turing machines," in Claude E. Shannon and John McCarthy (eds.), *Automata Studies*, Annals of Mathematics Studies, vol. 34, Princeton University Press, Princeton, NJ, 1956, pp. 167–175.
23. Martin Davis, "The definition of universal Turing machine," *Proceedings of the American Mathematical Society* **8** (1957), no. 6, 1125–1126, `doi:10.1090/S0002-9939-1957-0095781-8`.
24. Michael Drmota, "Systems of functional equations," *Random Structures & Algorithms* **10** (1997), no. 1–2, 103–124, `doi:10.1002/(SICI)1098-2418(199701/03)10:1/2<103::AID-RSA5>3.0.CO;2-Z`.
25. Jörg Endrullis, Roel C. de Vrijer, and Johannes Waldmann, "Local termination: theory and practice," *Logical Methods in Computer Science* **6** (2010), no. 3:20, 1–37, `doi:10.2168/LMCS-6(3:20)2010`.
26. Jörg Endrullis, Clemens Grabmayer, Dimitri Hendriks, Ariya Isihara, and Jan Willem Klop, "Productivity of stream definitions," *Theoretical Computer Science* **411** (2010), no. 4–5, 765–782, `doi:10.1016/j.tcs.2009.10.014`.
27. Alexander Filin, *Pure S Is Computationally Universal Under a Fixed Root-Restarted Finite Controller*, Technical manuscript, Predictive Universe Project, September 14, 2026.
28. Patrick C. Fischer, "On formalisms for Turing machines," *Journal of the ACM* **12** (1965), no. 4, 570–580, `doi:10.1145/321296.321308`.
29. Philippe Flajolet and Robert Sedgewick, *Analytic Combinatorics*, Cambridge University Press, Cambridge, 2009, `doi:10.1017/CBO9780511801655`.
30. Yannick Forster, Fabian Kunze, and Marc Roth, "The weak call-by-value $\lambda$-calculus is reasonable for both time and space," *Proceedings of the ACM on Programming Languages* **4** (POPL, 2020), Article 27, 27:1–27:23, `doi:10.1145/3371095`.
31. Georges Gonthier, "Formal proof—the Four-Color Theorem," *Notices of the American Mathematical Society* **55** (2008), no. 11, 1382–1393.
32. Georges Gonthier, Andrea Asperti, Jeremy Avigad, Yves Bertot, Cyril Cohen, François Garillot, Stéphane Le Roux, Assia Mahboubi, Russell O'Connor, Sidi Ould Biha, Ioana Pasca, Laurence Rideau, Alexey Solovyev, Enrico Tassi, and Laurent Théry, "A machine-checked proof of the Odd Order Theorem," in *Interactive Theorem Proving (ITP 2013)*, Lecture Notes in Computer Science, vol. 7998, Springer, Berlin, 2013, pp. 163–179, `doi:10.1007/978-3-642-39634-2_14`.
33. Katarzyna Grygiel and Pierre Lescanne, "Counting and generating lambda terms," *Journal of Functional Programming* **23** (2013), no. 5, 594–628, `doi:10.1017/S0956796813000157`.
34. Thomas Hales, Mark Adams, Gertrud Bauer, Tat Dat Dang, John Harrison, Le Truong Hoang, Cezary Kaliszyk, Victor Magron, Sean McLaughlin, Tat Thang Nguyen, Quang Truong Nguyen, Tobias Nipkow, Steven Obua, Joseph Pleso, Jason Rute, Alexey Solovyev, Ta Thi Hoai An, Tran Nam Trung, Thi Diep Trieu, Josef Urban, Ky Vu, and Roland Zumkeller, "A formal proof of the Kepler conjecture," *Forum of Mathematics, Pi* **5** (2017), e2, 1–29, `doi:10.1017/fmp.2017.1`.
35. Gabor T. Herman, "Simulation of one abstract computing machine by another," *Communications of the ACM* **11** (1968), no. 12, 802, 813, `doi:10.1145/364175.364181`.
36. J. Roger Hindley and Jonathan P. Seldin, *Lambda-Calculus and Combinators: An Introduction*, 2nd edition, Cambridge University Press, Cambridge, 2008, `doi:10.1017/CBO9780511809835`.
37. Gérard Huet, "The Zipper," *Journal of Functional Programming* **7** (1997), no. 5, 549–554, `doi:10.1017/S0956796897002864`.
38. Jan Willem Klop, Vincent van Oostrom, and Femke van Raamsdonk, "Reduction strategies and acyclicity," in *Rewriting, Computation and Proof*, Lecture Notes in Computer Science, vol. 4600, Springer, Berlin, 2007, pp. 89–112, `doi:10.1007/978-3-540-73147-4_5`.
39. Manfred Kudlek and Yurii Rogozhin, "A universal Turing machine with $3$ states and $9$ symbols," in *Developments in Language Theory (DLT 2001)*, Lecture Notes in Computer Science, vol. 2295, Springer, Berlin, 2002, pp. 311–318, `doi:10.1007/3-540-46011-X_25`.
40. Martin Kutrib and Uwe Meyer, "Deterministic real-time tree-walking-storage automata," in *Proceedings of the 13th International Workshop on Non-Classical Models of Automata and Applications (NCMA 2023)*, Electronic Proceedings in Theoretical Computer Science (EPTCS), vol. 388, 2023, pp. 48–62, `doi:10.4204/EPTCS.388.6`.
41. Martin Kutrib and Uwe Meyer, "Deterministic tree-walking-storage automata," *Acta Informatica* **63** (2026), no. 1, Article 9, `doi:10.1007/s00236-026-00522-5`.
42. Marvin L. Minsky, "Recursive unsolvability of Post's problem of 'Tag' and other topics in theory of Turing machines," *Annals of Mathematics* (2) **74** (1961), no. 3, 437–455, `doi:10.2307/1970290`.
43. Marvin L. Minsky, *Computation: Finite and Infinite Machines*, Prentice-Hall, Englewood Cliffs, NJ, 1967.
44. Turlough Neary, *Small Universal Turing Machines*, Ph.D. thesis, Department of Computer Science, National University of Ireland, Maynooth, October 2008.
45. Turlough Neary and Damien Woods, "Small fast universal Turing machines," *Theoretical Computer Science* **362** (2006), no. 1–3, 171–195, `doi:10.1016/j.tcs.2006.06.002`.
46. Turlough Neary and Damien Woods, "$\mathrm{P}$-completeness of cellular automaton Rule 110," in *Automata, Languages and Programming (ICALP 2006), Part I*, Lecture Notes in Computer Science, vol. 4051, Springer, Berlin, 2006, pp. 132–143, `doi:10.1007/11786986_13`.
47. Rohit J. Parikh, "On context-free languages," *Journal of the ACM* **13** (1966), no. 4, 570–581, `doi:10.1145/321356.321364`.
48. Emil L. Post, "Finite combinatory processes—Formulation 1," *The Journal of Symbolic Logic* **1** (1936), no. 3, 103–105, `doi:10.2307/2269031`.
49. Emil L. Post, *The Two-Valued Iterative Systems of Mathematical Logic*, Annals of Mathematics Studies, no. 5, Princeton University Press, Princeton, NJ, 1941.
50. Emil L. Post, "Formal reductions of the general combinatorial decision problem," *American Journal of Mathematics* **65** (1943), no. 2, 197–215, `doi:10.2307/2371809`.
51. Lutz Priese, "Towards a precise characterization of the complexity of universal and nonuniversal Turing machines," *SIAM Journal on Computing* **8** (1979), no. 4, 508–523, `doi:10.1137/0208039`.
52. Yurii Rogozhin, "Small universal Turing machines," *Theoretical Computer Science* **168** (1996), no. 2, 215–240, `doi:10.1016/S0304-3975(96)00077-1`.
53. Yurii Rogozhin, "A universal Turing machine with $22$ states and $2$ symbols," *Romanian Journal of Information Science and Technology* **1** (1998), no. 3, 259–265.
54. Moses Schönfinkel, "Über die Bausteine der mathematischen Logik," *Mathematische Annalen* **92** (1924), no. 3–4, 305–316, `doi:10.1007/BF01448013`.
55. Dana S. Scott, "Open problem," in Corrado Böhm (ed.), *$\lambda$-Calculus and Computer Science Theory*, Lecture Notes in Computer Science, vol. 37, Springer, Berlin, 1975, p. 368.
56. Alex Smith, "Universality of Wolfram's $2, 3$ Turing machine," *Complex Systems* **29** (2020), no. 1, 1–44, `doi:10.25088/ComplexSystems.29.1.1`.
57. Richard Statman, "On translating lambda terms into combinators; the basis problem," in *Proceedings of the First Annual IEEE Symposium on Logic in Computer Science (LICS 1986)*, IEEE Computer Society Press, 1986, pp. 378–382.
58. Richard Statman, "The word problem for Smullyan's lark combinator is decidable," *Journal of Symbolic Computation* **7** (1989), no. 2, 103–112, `doi:10.1016/S0747-7171(89)80044-6`.
59. Masako Takahashi, "Parallel reductions in $\lambda$-calculus," *Information and Computation* **118** (1995), no. 1, 120–127, `doi:10.1006/inco.1995.1057`.
60. TeReSe, *Term Rewriting Systems*, Cambridge Tracts in Theoretical Computer Science, vol. 55, Cambridge University Press, Cambridge, 2003.
61. Alan M. Turing, "On computable numbers, with an application to the Entscheidungsproblem," *Proceedings of the London Mathematical Society* (2) **42** (1937), 230–265, `doi:10.1112/plms/s2-42.1.230`; correction, ibid. **43** (1937), 544–546.
62. Peter van Emde Boas, "Machine models and simulations," in Jan van Leeuwen (ed.), *Handbook of Theoretical Computer Science, Volume A: Algorithms and Complexity*, Elsevier / MIT Press, 1990, pp. 1–66.
63. Johannes Waldmann, *Nimm Zwei*, Technical Report IR-432, Vrije Universiteit Amsterdam, 1997.
64. Johannes Waldmann, "Normalization of $S$-terms is decidable," in Tobias Nipkow (ed.), *Rewriting Techniques and Applications (RTA '98)*, Lecture Notes in Computer Science, vol. 1379, Springer, Berlin, 1998, pp. 138–150, `doi:10.1007/BFb0052367`.
65. Johannes Waldmann, *The Combinator S*, Ph.D. thesis, Fakultät für Mathematik und Informatik, Friedrich-Schiller-Universität Jena, 1998.
66. Johannes Waldmann, "The combinator $S$," *Information and Computation* **159** (2000), no. 1–2, 2–21, `doi:10.1006/inco.2000.2874`.
67. Shigeru Watanabe, "$5$-symbol $8$-state and $5$-symbol $6$-state universal Turing machines," *Journal of the ACM* **8** (1961), no. 4, 476–483, `doi:10.1145/321088.321090`.
68. Stephen Wolfram, *A New Kind of Science*, Wolfram Media, Champaign, IL, 2002.
69. Stephen Wolfram, "The prize is won; the simplest universal Turing machine is proved," *Stephen Wolfram Writings*, October 24, 2007, `https://writings.stephenwolfram.com/2007/10/the-prize-is-won-the-simplest-universal-turing-machine-is-proved/`.
70. Stephen Wolfram, "Combinators and the story of computation," *Stephen Wolfram Writings*, December 2020, `arXiv:2102.09658`.
71. Stephen Wolfram, "1920, 2020 and a \$20,000 prize: announcing the $S$ Combinator Challenge," *Stephen Wolfram Writings*, June 8, 2021, `doi:10.31855/7709b85c-8e6`, official rules at `https://www.combinatorprize.org/`.
72. Stephen Wolfram, *Combinators: A Centennial View*, Wolfram Media, Champaign, IL, 2021, `arXiv:2103.12811`.
73. Alan R. Woods, "Colouring rules for finite trees, and probabilities of monadic second order sentences," *Random Structures & Algorithms* **13** (1998), no. 3–4, 307–334.
74. Damien Woods and Turlough Neary, "On the time complexity of $2$-tag systems and small universal Turing machines," in *Proceedings of the 47th Annual IEEE Symposium on Foundations of Computer Science (FOCS 2006)*, IEEE, 2006, pp. 439–446, `doi:10.1109/FOCS.2006.57`.
75. Damien Woods and Turlough Neary, "The complexity of small universal Turing machines: a survey," *Theoretical Computer Science* **410** (2009), no. 4–5, 443–450, `doi:10.1016/j.tcs.2008.09.051`.
76. Efstathios Zachos, *Kombinatorische Logik und S-Terme*, Dissertation ETH Nr. 6214 (Berichte des Instituts für Informatik, Nr. 26), Eidgenössische Technische Hochschule Zürich, 1978, `doi:10.3929/ethz-a-000136021`.
77. Hans Zantema, "Termination of term rewriting by semantic labelling," *Fundamenta Informaticae* **24** (1995), no. 1–2, 89–105, `doi:10.3233/FI-1995-24124`.
