
This project contains the development of DEC (a Deep Embedding of a
terminating C-style language with effects) as a domain-specific
language embedded in Gallina, including language definition and
semantic boilerplate.

Relying on Coq modules, the definition of DEC is parametric in the
type of the mutable state and in the type of identifiers, which are
both specified in a module type (IdModType.v).

The syntax of DEC, defined in terms of inductive datatypes (in
StaticSemA.v, together with its static semantics), allows for
sequencing, local variables (let-style bindings), conditional
expressions, function call, and generic effects. The construct for
generic effects allows for the import in DEC of Gallina functions that
can access and modify the state (in this sense, DEC could also be
considered as a syntactic extension of Gallina).

DEC functions can be defined by bounded primitive recursion, using an
iteration scheme. They are not treated as first-class objects
(i.e. they are never returned). Each function definition is required
to be a closed term and it includes a bound as a natural number. DEC
distinguishes between value variables and function variables, while
relying on a single name space for identifiers. Correspondingly, DEC
semantics distinguishes between value environment and function
environment.

DEC types include primitive value types, which are specified by an
admissibility type class over Gallina types, and function types on
primitive types.

Each syntactic category of DEC program terms is defined as an
inductive datatype. DEC values are defined by lifting Gallina terms,
further hiding their admissible Gallina types. Expression head normal
forms (which include values and value variables) are called
quasi-values. Functions, function head normal forms (called
quasi-functions), expressions, and lifted list of expressions (called
parameters) are defined by mutual induction.

DEC programs do not bear type annotation, save for function
parameters. The typing relation for expressions is defined with
respect to a value typing context, a function environment and a
matching function typing context, and it is defined by mutual
induction with respect to the typing relations for the associated
categories (functions, quasi-functions, and parameters). The typing
relation for functions is defined recursively on the bound, so that
only terminating programs are well-typed. Hence, DEC has type-based
termination (bearing in mind that imported Gallina functions are
always terminating).

The dynamic semantics (in DynamicSemA.v) is specified in the style of
structural operational semantics (SOS) using a small-step transition
relation on configurations that for each category include a program
term of that category and a state of the store. In general, the
transition relation depends on a value environment and on a function
environment.

DEC has the following language properties:

1) it satisfies type soundness (no well-typed program gets stuck on a
non-value, and when a well-typed program terminates it gives a value
of the right type).

2) it ensures termination (every execution of a well-typed program
ends with a value).

3) it satisfies subject reduction (the execution of a well-typed
program preserves its type at each step).

4) it is deterministic (given an initial state, each well-typed
program can only evaluate to one value and one new state -- indeed, at
each non-terminal state in a well-typed program execution there is
just one possible step).

5) it is a strongly typed language (each program has at most one
type).

These results have been proven: 1 and 2 together as a strong type
soundness theorem (in TSoundnessA.v), 3 (in SReducA.v), 4 (in
DetermA.v), and 5 (in STypingA.v). All the proofs are essentially by
mutual induction on the typing relation, using a defined mutual
induction principle (in TRInductA.v).

The type soundness theorem, which has been proved constructively,
allows in principle the extraction of the return value and the final
state for each execution of a program, hence providing an interpreter
for the SOS specification. The determinism proof makes these specified
values formally available without actually computing them.

DEC supports Hoare logic reasoning, providing valid Hoare logic rules
in an untyped form (in HoareA.v) and in a typed one (in
THoareA.v). The proofs of the auxiliary lemmas (in InvertA.v) used in
the logic proofs make use of all of the 1--5 properties.

DEC has been developed by Paolo Torrini as intermediate language for
the translation of Pip to C, and it is currently used by a translator
tool called Digger, expected to be part of the next Pip release.

