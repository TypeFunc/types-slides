# Type Theory Crash Course<br> based on<br> [Thorsten Altenkirch's notes](http://www.cs.nott.ac.uk/~psztxa/ewscs-17/notes.pdf)
lectures/slides by William DeMeo [&lt;williamdemeo@gmail.com&gt;](mailto:williamdemeo@gmail.com)  
UH MFC Bootcamp, 29--31 March 2017  

# Part 0: What is Type Theory?

---

## References

The material we cover here is based on the following:

+ Altenkirch (2016) [Naive Type Theory short course](http://www.cs.nott.ac.uk/~psztxa/ntt/)  
  www.cs.nott.ac.uk/~psztxa/ntt/

+ Capretta (2002) [Abstraction and Computation, PhD thesis](http://www.cs.nott.ac.uk/~vxc/publications/Abstraction_Computation.pdf)  
www.cs.nott.ac.uk/~vxc/publications/Abstraction_Computation.pdf

+ Harper (2013) [CMU course on HoTT](http://www.cs.cmu.edu/~rwh/courses/hott/)  
  www.cs.cmu.edu/~rwh/courses/hott/

+ Pfenning (2009) [Lecture notes on natural deduction](http://www.cs.cmu.edu/~fp/courses/15317-f09/lectures/02-natded.pdf)  
  www.cs.cmu.edu/~fp/courses/15317-f09/lectures/02-natded.pdf

---

## Two Iterpretations

+ <a style="color:#e7ad52">**Type Theory** (TT)</a> (with caps) is an 
  alternative foundation for Mathematics---an alternative to Set Theory (ST)

+ pioneered by Swedish mathematician <a style="color:#e7ad52">**Per Martin-Löf**</a>

+ <a style="color:#e7ad52">**type theory** (tt)</a> (w/out caps) is the theory of types in programming languages 

+ <a style="color:#e7ad52">TT</a> and <a style="color:#e7ad52">tt</a> are related 
  but different subjects

---

## Type Theory: the basic idea

+ organize mathematical objects into <a style="color:#e7ad52">**Types**</a> instead of 
  <a style="color:green">**Sets**</a>   
  eg, the <a style="color:#e7ad52">**Type** $\mathbb N$</a> of natural numbers,
  the <a style="color:#e7ad52">**Type** $\mathbb R$</a> of reals, etc

+ to say that $\pi$ is real, write <a style="color:#e7ad52">$\pi : \mathbb R$</a>

+ *Wait a minute!* <a style="color:#e7ad52">Type Theory</a> is merely <a style="color:green">Set Theory</a> 
  with the word   
  <a style="color:green">Set</a> replaced by <a style="color:#e7ad52">Type</a> and the 
  symbol <a style="color:green">$\in$</a> replaced by <a style="color:#e7ad52">$:$</a> ??<br><br>
  **WTF?!**

+ Of course not.  In <a style="color:#e7ad52">Type Theory</a> we can only make objects of a certain 
  type---*the type comes first*---and then we can construct elements of that type.

+ In <a style="color:green">Set Theory</a> all objects are there already and we can organize 
  them into different sets; we might have an object $x$ and ask wether this object is a 
  **nat** ($x\in \mathbb N$) or a **real** ($x \in \mathbb R$).

---

## Type Theory vs. Set Theory

+ In <a style="color:#e7ad52">Type Theory</a> we think of <a style="color:#e7ad52">$x : \mathbb N$</a> as
  meaning that $x$ is a natural number "by birth" and we can ask whether $x$ is a real number.
 
+ We say <a style="color:#e7ad52">$x : \mathbb N$</a> is a **judgement** while 
  <a style="color:green">$x \in \mathbb N$</a> is a **proposition**

+ We will revisit these ideas again and again, and they will become clearer once we gain some experience with Type Theory.

---

## End of Part 0

---

# Part 1: Constructive Math 

---

+ What is a good language for writing proofs?

+ What kind of math do we want to do? 

+ In principle all math can be formalized in ZFC.

+ Usually a much weaker theory is sufficient  
  (PA suffices for much of Number Theory)   
  (Analysis can be formalized in PA2)

+ In fact, we don't need to commit, as long as our proofs use 
  standard techniques that we believe are formalizable in *some* system.

---

<!-- ------ JPS ------------ -->
<img src="img/jps.jpg" alt="Choices" style="width: 350px;float: right"/>

+ But to do math on a computer  
  *we must make a choice!*
  
+ A computer program must be  
  based on *some* formal system 
  
+ **ZFC** is not the obvious choice

+ **constructive type theory**  
  can be justified on both  
  philosophical   and practical grounds 

---

**Question:** Why do math on a computer?

+ Because computers can check whether proofs are correct?
  <a style="color:#e7ad52">No, the peer review process works.</a>

+ Because computers can prove many things humans can't?
  <a style="color:#e7ad52">No, at least not anytime soon.</a>

+ Because computers are really good at computing?
  <a style="color:#e7ad52">Yes!!</a>

---

<p class="fragment fade-left"> 
Nobody would question the utility of computer programs on the grounds that we 
can write those programs on a piece of paper faster and more easily in pseudo-code.
This would be silly, since <a style="color:#e7ad52">*programs written on paper cannot be executed*</a>
</p>

<p class="fragment fade-left"> 
The objection that formalizing math on computer
is pointless because we can more easily write it down on a piece of paper can
be disputed on similar grounds.  But...  
</p>
<p class="fragment fade-left"> 
<a style="color:#e7ad52">*proofs of math theorems cannot be executed*</a>  
</p>
<p class="fragment fade-left"> ...or can they? </p>

---

+ *Classical* proofs cannot always be executed,   
but *constructive* proofs can, in a sense.

+ Constructive proofs give algorithms to  
compute all objects claimed to exist and  
decide all properties claimed decidable.
<!-- ------ DVF ------------ -->
<div class="fragment fade-left">
<img src="img/Darth-Vader-faith.jpg" alt="Darth Vader faith" style="width: 300px;float: right"/>
</div>
+ It may seem strange to think of a proof  
as a program, even stranger that there  
can be different proofs of the same  
result that differ in "efficiency." 

---

### A Change of Tack

+ Instead of discussing ways to formalize math, let's consider
ways to extend programming languages, e.g. richer data types,
new paradigms/techniques.

+ We will consider a high level functional language and see
how it makes programming easier; some classical algorithms become easy or obvious;
previously inconceivable programs are possible.

+ We don't mention logic and math at first.

---

### Curry-Howard Correspondence

<p class="fragment fade-left">
Eventually, we see <a style="color:#e7ad52">*programs as proofs*</a> 
of theorems and <a style="color:#e7ad52">**constructive math**</a>
as a subsystem of the programming language.</p>

<p class="fragment fade-left">**The most important advantage:**  
<a style="color:#e7ad52">*programs are guaranteed correct*</a>   
by virtue of the their inherent logical content!</p>

---

## End of Part 1

(time for a break)

---

# Part 2: Type Theory vs Set Theory

---

## Sets vs Types

* In <a style="color:green">Set Theory</a>, 
	$3 \in \mathbb N$ means  
	"3 is an element of the <a style="color:green">set</a> of natural numbers"

* In <a style="color:#e7ad52">Type Theory</a>, 
	$3 : \mathbb N$ means  
	"3 is an element of the <a style="color:#e7ad52">type</a> of natural numbers"

* Seems trivial... but here's the significance...
    <!-- 1. $3 \in \mathbb N$ is a <a style="color:green">proposition</a>  -->
    <!-- 2. $3 : \mathbb N$ is a <a style="color:#e7ad52">judgment</a>, ie a piece  -->
    <!--    of <em>static information</em> -->
    <!-- 3. In <a style="color:#e7ad52">Type Theory</a> every object and expression  -->
    <!--    has a unique type that is statically determined. It doesn't make sense to call   -->
    <!--    <a style="color:#e7ad52">$a : A$</a> a proposition. -->

---

## Sets vs Types

* While  <a style="color:green">$3 \in \mathbb N$</a> is a proposition,  <a style="color:#e7ad52">$3 : \mathbb N$</a> is a *judgment*; ie a piece of static information.
  
* In <a style="color:#e7ad52">Type Theory</a> every object and every expression has a (unique) type
  which is statically determined.
  
* Hence it doesn't make sense to use <a style="color:#e7ad52">$a : A$</a> as a proposition.

<!-- * This is similar to the distinction between statically and dynamically typed -->
<!--   programming languages. While in dynamically typed languages there are -->
<!--   runtime functions to check the type of an object this doesn't make sense -->
<!--   in statically typed languages. -->
* In <a style="color:green">Set Theory</a> we define $P \subseteq Q$ as $\forall x . x \in P \to x \in Q$.  
  This doesn't work in <a style="color:#e7ad52">Type Theory</a> since $x \in P$ is not a proposition.
  
* <a style="color:green">Set theoretic</a> operations like $\cup$ or $\cap$ are not operations on 
  <a style="color:#e7ad52">types</a>  
  ...but they can be defined as operations on predicates (subsets) of
  a given type. $\subseteq$ can be defined as a predicate on such subsets.

---

* <a style="color:#e7ad52">Type Theory</a> is **extensional** in the sense that we 
  can't talk about details of encodings.

* In <a style="color:green">Set Theory</a> we can ask whether 
  <a style="color:green">$\mathbb N \cap \mathsf{Bool} = \emptyset$</a>    
  Or whether <a style="color:green">$2 \in 3$</a>. 
  The answer to these questions depends on  
  the choice of representation of the objects and sets involved.

* In addition to the judgment <a style="color:#e7ad52">$a : A$</a>, we introduce the 
  judgment <a style="color:#e7ad52">$a \equiv_A b$</a> which means <a style="color:#e7ad52">$a$</a> 
  and <a style="color:#e7ad52">$b$</a> are **definitionally equal**. 

* Definitional equality is a *static* property, hence it doesn't make sense as a proposition. 
  (Later we introduce **propositional equality** <a style="color:#e7ad52">$a =_A b$</a> 
  which can be used in propositions) 

* We write definitions using <a style="color:#e7ad52">$:\equiv$</a>, eg
  <a style="color:#e7ad52">$n :\equiv 3$</a> defines <a style="color:#e7ad52">$n : \mathbb N$</a> to be 
  <a style="color:#e7ad52">3</a>

* <a style="color:#e7ad52">Type Theory</a> is more restrictive than 
  <a style="color:green">Set Theory</a>...   
  but this has some benefits...
  
---

## Univalence Axiom 

Since we can't talk about intensional aspects (implementation details), 
we can identify objects which have the same extensional behavior. 
This is reflected in the univalence axiom, 
which identifies **extensionally equivalent** types.

---

## Truth Vs. Evidence
Another important difference between Set Theory and Type Theory is the
way propositions are treated: Set Theory is formulated using predicate logic
which relies on the notion of **truth**. Type Theory is self-contained and doesn't
refer to **truth**, but rather **evidence**.

---

## Curry-Howard Correspondence

Using the <a style="color:#e7ad52">propositions-as-types</a> translation 
we can assign to any proposition $P$ the type of its evidence $[[P]]$ 
as follows:

\begin{align*}
[[P \Rightarrow Q]] &\equiv [[P]] \to [[Q]]\\
[[P ∧ Q]] &≡ [[P ]] × [[Q]]\\
[[\mathsf{True}]] &≡ 1\\
[[P ∨ Q]] &≡ [[P ]] + [[Q]]\\
[[\mathsf{False}]] &≡ 0\\
[[∀x : A.P ]] &≡ Πx : A.[[P ]]\\
[[∃x : A.P ]] &≡ Σx : A.[[P ]]
\end{align*}

0 is the empty type, 1 is the type with exactly one element

disjoint union +, product ×, and → (function) types are familiar

Π and Σ may be less familiar; we look at them later.

---

## End of Part 2

---

# Part 3: Non-dependent types

---

## Universes

+ To get started we have to say what a *type* is. We could introduce another judgement, but
  instead we'll use **universes.** 

+ A **universe** is a type of types. For example, to say that $\mathbb N$ is a type, 
  we write <a style="color:#e7ad52">$\mathbb N : \mathsf{Type}$</a>, where
  <a style="color:#e7ad52">$\mathsf{Type}$</a> is a universe.

+ But what is the type of <a style="color:#e7ad52">$\mathsf{Type}$</a>? Do we have 
  <a style="color:#e7ad52">$\mathsf{Type} : \mathsf{Type}$</a>? 

+ This doesn't work in   <a style="color:green">Set Theory</a> due to **Russell's paradox**  
  (consider the set of all sets that don't contain themselves)
  
+ In Type Theory <a style="color:#e7ad52">$a : A$</a> is not a Prop, hence it's not immediately clear wether 
  the paradox still occurs.

---

+ It turns out that a Type Theory with <a style="color:#e7ad52">$\mathsf{Type} : \mathsf{Type}$</a> does 
  exhibit **Russell's paradox**.

+ Construct the tree <a style="color:#e7ad52">$T : \mathsf{Tree}$</a> of all trees 
  that don't have themselves as immediate subtrees. Then <a style="color:#e7ad52">$T$</a> 
  is a subtree of itself iff it isn't.

+ To avoid this, we introduce a hierarchy of universes
  <a style="color:#e7ad52">
  $$\mathsf{Type}_0 : \mathsf{Type}_1 : \mathsf{Type}_2 : \cdots$$
  </a>
  and we decree that any <a style="color:#e7ad52">$A : \mathsf{Type}_i$</a>
  can be *lifted* to <a style="color:#e7ad52">$A^+ : \mathsf{Type}_{i+1}$</a>

+ Being explicit about universe levels can be quite annoying.  
  In notation we ignore the levels, but take care to avoid using universes in a cyclic way. 

+ That is we write <a style="color:#e7ad52">$\mathsf{Type}$</a> as a metavariable for 
  <a style="color:#e7ad52">$\mathsf{Type}_i$</a> and assume that all levels 
  act the same unless stated otherwise.

---

## Functions

+ In <a style="color:green">Set Theory</a> **function** is a derived concept 
  (a subset of the cartesian product with certain properties)

+ In <a style="color:#e7ad52">Type Theory</a> **function** is a primitive concept. 

+ The basic idea is the same as in functional programming: a
  function is a **black box**; you feed it elements from its domain and out come
  elements of its codomain. 

+ Hence given $A, B : \mathsf{Type}$ we introduce the type of
  functions $$A \to B : \mathsf{Type}$$ 
  
+ We can define a function
  $f : \mathbb{N} \to \mathbb{N}$ 
  explicitly, eg, $f (x) :\equiv x + 3$. 
  
+ We can now apply, $f (2) : \mathbb{N}$, and
  evaluate this application by replacing all 
  $x$'s in the body with 2; hence $f (2) \equiv 2 + 3$

+ If we know how to calculate $2 + 3$ we can conclude $f (2) \equiv 5$

---

## A word about syntax 

- In Type Theory, as in functional programming, we usually
try to save parentheses and write $f x :\equiv x + 3$ 
and $f 2$

- The explicit definition of a function requires a name but we want 
**anonymous functions** as well---this is the justification for the  
<a style="color:#e7ad52">λ-notation</a> 

- We write $\lambda x.x + 3 : \mathbb{N} \to \mathbb{N}$ 
to avoid naming the function. 

- We can apply: $(\lambda x . x + 3)(2)$

- The equivalence
$(\lambda x . x + 3)(2) \equiv 2 + 3$
is called <a style="color:#e7ad52">β-reduction</a>

- The explicit definition $f x \equiv x + 3$ can now be understood
as a shorthand for $f \equiv \lambda x . x + 3$.

---

## Products and sums

+ Given $A, B : \mathsf{Type}$ we can form 
    - their product <a style="color:#e7ad52">$A \times B : \mathsf{Type}$</a>
    - their sum <a style="color:#e7ad52">$A + B : \mathsf{Type}$</a> 

+ The elements of a product are tuples, that is  
  $(a, b) : A \times B$ if $a : A$ and $b : B$ 

+ The elements of a sum are injections, that is  
  $\mathsf{inl}\ a : A + B$ if $a : A$ and $\mathsf{inr}\ b : A + B$, if $b : B$

---

+ To define a function from a product or a sum it suffices to say   
  what the function returns for the
  constructors  
  (tuples for products; injections for sums)

+ As an example we derive the tautology
$$P ∧ (Q ∨ R) ⇔ (P ∧ Q) ∨ (P ∧ R)$$
using the propositions as types translation. 

+ Assuming $P, Q, R : \mathsf{Type}$, we must
  construct an element of   
  the following type
  $$((P × (Q + R) → (P × Q) + (P × R))$$
  $$\qquad ×((P × Q) + (P × R) → P × (Q + R))$$

---

## Solution

Define $f : P × (Q + R) \to (P × Q) + (P × R)$ as follows:

$$f (p, \mathsf{inl}\ q) :\equiv \mathsf{inl}\ (p, q)$$

$$f (p, \mathsf{inr}\ r) :\equiv \mathsf{inr}\ (p, r)$$

Define $g : (P × Q) + (P × R) \to P × (Q + R)$ as follows:

$$g (\mathsf{inl}\ (p, q)) :\equiv (p, l\mathsf{inl}\ q)$$

$$g (\mathsf{inr} (p, r))) :\equiv (p, \mathsf{inr}\ r)$$

The tuple $(f, g)$ is an element of the desired type!

---

## Exercise 1 

Using the propositions as types translation, try to prove the following tautologies
(where P, Q, R : Type are propositions represented as types)

1. (P ∧ Q ⇒ R) ⇔ (P ⇒ Q ⇒ R)
2. ((P ∨ Q) ⇒ R) ⇔ (P ⇒ R) ∧ (Q ⇒ R)
3. ¬(P ∨ Q) ⇔ ¬P ∧ ¬Q
4. ¬(P ∧ Q) ⇔ ¬P ∨ ¬Q
5. ¬(P ⇔ ¬P )

---

## Exercise 2

**Law of Excluded Middle** $(\forall P) (P \vee \neg P)$ 
is not provable in TT

However, we can prove its double negation (ie "LEM is not refutable")

Using the **propositions-as-types** translation, prove

$$(\forall P)\neg \neg(P \vee \neg P )$$

If for a particular proposition $P$ we can establish $P \vee \neg P$ 
then we can also derive the principle of indirect proof $\neg \neg P \Rightarrow P$
for the same proposition. 

Show $(P \vee \neg P ) \Rightarrow (\neg \neg P \Rightarrow P )$

The converse does not hold **locally** (Counterexample?) 

...but it holds **globally**. Show that the two principles are equivalent. 
That is, prove:

$$(\forall P)(P \vee \neg P ) \Longrightarrow (\forall P)(\neg \neg P \Rightarrow P )$$

---

Functions out of products and sums can be reduced to using a fixed set of
**combinators** called <a style="color:#e7ad52">*non-dependent eliminators*</a> 
or <a style="color:#e7ad52">*recursors*</a> (even though there
is no recursion going on).

$R^\times : (A → B → C) → A × B → C$

$R^\times f\ (a, b) :\equiv f a b$

$R^+ : (A → C) → (B → C) → A + B → C$

$R^+ f g\ (\mathsf{inl}\ a) :\equiv f a$

$R^+ f g\ (\mathsf{inr}\ b) :\equiv g b$

+ The **recursor** $R^\times$ for products maps a **curried** function $f : A → B → C$
to its **uncurried** form, taking tuples as arguments. 

+ The **recursor** $R^+$ basically implements the case function performing case 
analysis over elements of $A + B$.

---

## Exercise 3 

Show that using the **recursor** $R^\times$ we can define the projections:

fst : A × B → A

fst (a, b) :≡ a

snd : A × B → B

snd (a, b) :≡ b

Vice versa: can the recursor be defined using only the projections?

---

## The unit and empty types

+ Denote by $\mathbf{1}$ the empty product, called the <a style="color:#e7ad52">*unit type*</a>

+ Denote by $\mathbf{0}$ the empty sum, called the <a style="color:#e7ad52">*empty type*</a>

+ $() : \mathbf{1}$ is the only inhabitant of the unit type

+ Nothing inhabits $\mathbf{0}$ (it's the *empty* type!)

+ We introduce the corresponding recursors:<br>
$R^\mathbf{1} : C → (\mathbf{1} → C)$ is defined by $R^\mathbf{1} c () :\equiv c$<br>
$R^\mathbf{0} : \mathbf{0} → C$ (no defining eqn since it won't be applied)

+ The recursor for $\mathbf{1}$ is pretty useless. It just defines a constant function. 

+ The recursor for the empty type implements the logical principle *ex falso quod libet*

---

## Exercise 4 

Construct solutions to exercises 1 and 2 using only the eliminators.

---

+ The use of arithmetical symbols for operators on types is justified because
they act like the corresponding operations on finite types. 

+ Let us identify the number $n$ with a **type** inhabited by the following elements:
$0_n, 1_n, \dots, (n - 1)_n : \underline{n}$

+ Then we observe that
\begin{align*}
\underline{0} &= 0\\
\underline{m+n} &= \underline{m} + \underline{n}\\
\underline{1} &= 1\\
\underline{m \times n} &= \underline{m}\times \underline{n}
\end{align*}

+ Read $=$ here as "has the same number of elements"  
This use of equality will be justified later when we introduce the 
**univalence principle**

---

## Function Types are Exponentials

The arithmetic interpretation of types also extends to the function type,
which corresponds to exponentiation. Indeed, in Mathematics the function type
$A \to B$ is often written as $B^A$, and indeed we have:
$\underline{m^n} = \underline{n} \to \underline{m}$.

---

## End of Part 3

---

# Part 4: Dependent Types

---

## What are Dependent Types?

<p class="fragment fade-left">
You may be familiar with <a style="color:#e7ad52">polymorphic types</a> (aka generics)  
These are types that are indexed by other types  
</p>

<div class="fragment fade-left">
<a style="color:olivedrab">**Example**</a>

```java
Array<Integer>      // Java

List[(String, Int)] // Scala
```
</div>

<p class="fragment fade-left">
A <a style="color:#e7ad52">*dependent type*</a> is
indexed by an <u>*element*</u> of another type
</p>

<div class="fragment fade-left">
<a style="color:olivedrab">**Examples**</a>

<a style="color:#e7ad52">$A^n : \mathsf{Type}$</a>, the *type of $n$-tuples* whose inhabitants are $(a_0, a_1, \dots, a_{n-1}) : A^n$ where $a_i : A$

<a style="color:#e7ad52">$\underline{n} : \mathsf{Type}$</a>, the *finite type* whose inhabitants are $0_n, 1_n, \dots, (n - 1)_n : \underline{n}$
</div>

---

## What are Dependent Types?

The **$n$-tuple type**
<a style="color:#e7ad52">$A^n : \mathsf{Type}$</a>
is indexed by \underline{*two*} parameters

$$\underline{n} : \mathsf{Type} \quad \text{ and } \quad A : \mathsf{Type}$$  

<div class="fragment fade-left">
In general, a <a style="color:#e7ad52">*dependent type*</a> is obtained by applying a 
function with codomain $\mathsf{Type}$.
</div>

<div class="fragment fade-left">
<a style="color:olivedrab">**Example 1**</a>

$\mathsf{Vec} : \mathsf{Type} \to \mathbb{N} \to \mathsf{Type}$

$\mathsf{Vec}\; A\; n :\equiv A^n$
</div>

<div class="fragment fade-left">
<a style="color:olivedrab">**Example 2**</a>

$\mathsf{Fin} : \mathbb{N} \to \mathsf{Type}$

$\mathsf{Fin}\; n :\equiv \underline{n}$
</div>

---

## Curry-Howard again

In the *propositions-as-types* view, <a style="color:#e7ad52">**dependent types**</a> 
are used to encode predicates.

<div class="fragment fade-left">
<a style="color:olivedrab">**Example**</a>  
<a style="color:#e7ad52">$\mathsf{Prime} : \mathbb N \to \mathsf{Type}$</a>  
This takes <a style="color:#e7ad52">$n : \mathbb N$</a> as input and outputs 
<a style="color:#e7ad52">$\mathsf{Prime}\; n : \mathsf{Type}$</a>,  
the type representing *evidence that $n$ is a prime number*.
</div>

<div class="fragment fade-left">
If <a style="color:#e7ad52">$\varphi$</a> is a proof that <a style="color:#e7ad52">$n : \mathbb N$</a> is prime, then
<a style="color:#e7ad52">$\varphi : \mathsf{Prime}\; n$</a>.</div>
<!-- and say "<a style="color:#e7ad52">$\varphi$</a> has type <a style="color:#e7ad52">$\mathsf{Prime}\; n$</a>" -->
<!-- <a style="color:#e7ad52">$p$</a> has type <a style="color:#e7ad52">$\mathsf{Prime}\; n$</a> and we write -->

<div class="fragment fade-left">
Of course <a style="color:#e7ad52">$\mathsf{Prime}\; n$</a> could be uninhabited, eg <a style="color:#e7ad52">$\mathsf{Prime}\; 4$</a>.
</div>

---

## Codifying Relations

By <a style="color:#e7ad52">currying</a> we can also use dependent types to represent **relations**

<a style="color:olivedrab">**Example**</a>
<a style="color:#e7ad52">$\leq\; : \mathbb N \to \mathbb N \to \mathsf{Type}$</a>  
<a style="color:#e7ad52">$m \leq n : \mathsf{Type}$</a>,
the type of *evidence that <a style="color:#e7ad52">$m$</a> is less or equal to <a style="color:#e7ad52">$n$</a>*

<div class="fragment fade-left">
If <a style="color:#e7ad52">$\varphi$</a> is a proof of
<a style="color:#e7ad52">$m \leq n$</a>, then 
<a style="color:#e7ad52">$\varphi : m \leq n$</a>
</div>

<div class="fragment fade-left">
<a style="color:olivedrab">**Example**</a> Let 
<a style="color:#e7ad52">$\mathbf A$</a> be an algebra and 
<a style="color:#e7ad52">$\theta \in \operatorname{Con} \mathbf A$</a> a congruence
</div>

<div class="fragment fade-left">
<a style="color:#e7ad52">$\theta : A \to A \to \mathsf{Type}$</a> takes inputs
<a style="color:#e7ad52">$a, b : A$</a> and outputs <a style="color:#e7ad52">$a \mathrel{\theta} b : \mathsf{Type}$</a>, 
the type of *evidence for <a style="color:#e7ad52">$(a,b) \in \theta$</a>*
</div>

<div class="fragment fade-left">
If <a style="color:#e7ad52">$\varphi$</a> is a proof of
<a style="color:#e7ad52">$a \mathrel{\theta} b$</a>, then 
<a style="color:#e7ad52">$\varphi : a \mathrel{\theta} b$</a>
</div>

---

## Martin-Lof intensional type theory

+ <a style="color:rgb(231,173,82)">Intensional type theory</a> is the brand of type 
theory used in systems like 
<a style="color:mediumpurple">Agda</a> and <a style="color:orangered">Coq</a> 

+ <a style="color:crimson">NuPrl</a> 
  is based on extensional type theory  

+ This is an important distinction and it centers around different notions of 
**equality**

---

+ In the original formulation by Martin-Lof, there is a judgement called
*definitional equality*, which is asserted when two terms denote the same value.

+ Today, this is most often replaced by a reduction relation.  Two terms are
called *convertible* when they can be reduced to a common decendant using the
reduction rules.  If we reduce a term as much as possible, we always obtain
after a finite number of steps, a unique *normal form* (that 
cannot be simplified further).  Convertible terms are interchangeable.

+ *extensional* versions of type theory, 
  like <a style="color:crimson">NuPrl</a>,
  have a stronger notion of **definitional equality**   
  for example, two functions can be identified if their graphs are the same  
  
+ However, the price to pay is *undecidability of type checking*

---

## <a style="color:crimson">Extensional Type Theory</a>

<a style="color:mediumpurple">Intensional</a>
<a style="color:crimson">Extensional</a>

+ <a style="color:crimson">ETT</a>
  does not distinguish between **definitional equality** (computational) 
  and **propositional equality** (requires proof) 
  
+ Type checking is **undecidable** in 
  <a style="color:crimson">ETT</a>  
  *programs in the theory might not terminate*
  
+ <a style="color:olivedrab">**Example**</a>
  In <a style="color:crimson">ETT</a> we can give a type to the **Y-combinator** 

+ This does not prevent <a style="color:crimson">ETT</a> from being a basis 
  for a practical tool, as <a style="color:crimson">NuPRL</a> demonstrates.

+ From a practical standpoint, there's no difference between a program which doesn't terminate and a program which takes a million years to terminate

---

## <a style="color:mediumpurple">Intensional Type Theory</a>

<a style="color:mediumpurple">Intensional</a>
<a style="color:crimson">Extensional</a>

+ <a style="color:mediumpurple">ITT</a>
  has decidable type checking, but the representation of 
  standard math concepts can be more cumbersome.
  
+ In <a style="color:mediumpurple">ITT</a>
  **extensional reasoning** requires using 
  <a style="color:rgb(231,173,82)">setoids</a> or similar constructions. 
  
+ There are many common math objects that are hard to work 
  with and/or can't be represented without this.
  
+ **Examples:** Integers and rational numbers can be 
  represented without setoids, but the representations are not
  easy to work with; Reals cannot be represented without 
  setoids or something similar.

---

## Homotopy type theory 

+ <a style="color:olivedrab">HoTT</a> works on resolving these problems 

+ <a style="color:olivedrab">HoTT</a>
  allows one to define <a style="color:rgb(231,173,82)">higher inductive types</a> 
  that not only define **first-order constructors** (values or points), but **higher-order 
  constructors** (equalities between elements--paths), equalities between equalities 
  (homotopies), ad infinitum.

