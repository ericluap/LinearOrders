# LinearOrders
Formalization of results regarding linear orders in Lean.


## Main Theorems Formalized
### Theorem (Lindenbaum)
If $X$ and $Y$ are linear orders such that $X$ embeds in an initial segment of $Y$ and $Y$ embeds in a final segment of $X$, then $X \cong Y$.

### Theorem (Sum Refinement)
If $X$, $Y$, $A$, and $B$ are linear orders such that $X + Y \cong A+B$, then there exists a linear order $E$ such that either
- $A + E \cong X$ and $E + Y \cong B$, or
- $X + E \cong A$ and $E + B \cong Y$
