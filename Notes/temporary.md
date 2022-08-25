<!-- ## Terms: $e$

- Variable reference: $x$
- Application: $e\;e$ 
- Lambda-abstraction: $\lambda x. e$
- `let`-binding: $\textbf{let}\ x : t = e\ \textbf{in}\ e$
- Unit: $()$

## Types: $t$

- Type variable reference: $a$
- Arrows: $t \rarr t$
- Universal quantification: $\textbf{forall}\ a.\ t$
- Holes: $?h$

## Typing Rules

### Contexts: $\Gamma$

Each entry in a context has a scope, notated as $\ell_f$ or $\ell_b$, being an integer notating the DeBruijn level or index respectively. These are confusing terms, so in this explanation we will use "forward level" and "backward level", where you count the number of binders from/to the variable reference in the given direction. Thus, "forward levels" are counting the number of binders to the given variable reference from the outside in, whereas "backward levels" are counting from the inside out.

- Empty context: $\emptyset$
- With type variable: $\Gamma, a \dashleftarrow \ell_b$
- With term variable: $\Gamma, e : t \dashleftarrow \ell_b$
- With hole: $\Gamma, ?h \dashleftarrow \ell_f$

**N.B.** Type variables, term variables, and term levels are always backward levels, whereas holes are always forward levels.

Contexts have a notion of "substitution", where a hole can be substituted with a type to fill that hole: $\Gamma [t / ?h]$. The process of doing this will be explained in the section on unification.

### Check: $\Gamma \vdash e \Rightarrow t$

### Infer: $\Gamma \vdash e \Leftarrow t$-->
