# Original-statement correspondence

The source is Erdős problem 566, also posed in Erdős, Faudree, Rousseau, and Schelp, *Ramsey size linear graphs* (1993), Question 1 on page 398. The current JSP mapping is JSP-000456.

The prose sources leave the lower range of subgraph orders implicit. This submission uses the canonical Formal Conjectures convention of at least two vertices. At orders zero and one, the integer bound `2k - 3` is negative, so including those orders literally would make the premise impossible. The mathematical paper and both formal statements explicitly use `k ≥ 2`. Organizer review is requested for this precise formulation.

| Original requirement | Representation and argument |
| --- | --- |
| Finite simple graphs | `SimpleGraph (Fin p)` represents each finite order. The counterexample is explicitly on a fixed `Fin` type. |
| Every vertex subset of size at least two | `OriginalStatement` quantifies over every `Finset`, with `2 ≤ S.card`. The induced edge cardinality is bounded by `2 * S.card - 3`. |
| The graph is fixed | `counterexampleGraph` uses base size 10,000,000 and 20,000 transitions. Its definition is independent of the target index. |
| Ordinary complete-host Ramsey number | `PrizeStatement.graphRamsey` takes the infimum of complete-host orders for which every edge coloring contains the required ordinary subgraph. |
| The constant depends on the fixed graph | `IsRamseySizeLinear` places the positive real existential constant before the quantifier over H. |
| All target sizes and positive degrees | The definition quantifies over every finite target order and includes `∀ v, 0 < H.degree v`. Clique witnesses have positive degree. |
| Full negation | The sampled-cube existence theorem is proved. The final theorem refutes the complete universal statement without an extra unproved sampling assumption. |
| Independent statement | `Verification.lean` defines the original question directly and proves its negation using the submission. |

The mathematical paper proves the same fixed-graph disproof. Its clique order is `2^(570*m)`, and its complete-host lower bound is `2^(1144*m - 1)` for all sufficiently large positive integers m. The ratio to the clique edge count exceeds `2^(4*m)`.

The original question has one universal assertion. A fixed graph satisfying all its premises and violating its conclusion for unbounded clique targets resolves that assertion negatively. The neighboring Erdős problems 567 and 568 are outside this submission.
