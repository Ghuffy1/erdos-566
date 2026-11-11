/-
Original-problem check for the Erdős 566 submission.

The definitions below independently spell out the ordinary Ramsey number and
the question's quantifiers. The source formulation is Erdős problem 566 and
Erdős--Faudree--Rousseau--Schelp, Ramsey size linear graphs (1993), Question 1.
The canonical formulation was checked against Formal Conjectures revision
2f91d251c07fbbaf9435166d47c11e884a08a6cf.

The Formal Conjectures definitions are copyright 2025 The Formal Conjectures
Authors, under Apache License 2.0. See NOTICE and LICENSE.
-/
import Erdos566

namespace Verification

noncomputable def ramseyNumber {α β : Type*} [Fintype α] [Fintype β]
    (G : SimpleGraph α) (H : SimpleGraph β) : ℕ :=
  sInf {n : ℕ | ∀ C : SimpleGraph (Fin n), G.IsContained C ∨ H.IsContained Cᶜ}

def ramseySizeLinear {α : Type*} [Fintype α] (G : SimpleGraph α) : Prop :=
  ∃ c > (0 : ℝ), ∀ (n : ℕ) (H : SimpleGraph (Fin n)) [DecidableRel H.Adj],
    (∀ v, 0 < H.degree v) →
    (ramseyNumber G H : ℝ) ≤ c * H.edgeSet.ncard

def originalProblem : Prop :=
  ∀ (p : ℕ) (G : SimpleGraph (Fin p)),
    (∀ S : Finset (Fin p), 2 ≤ S.card →
      (G.induce S).edgeSet.ncard ≤ 2 * S.card - 3) →
    ramseySizeLinear G

theorem statement_agreement : originalProblem = Erdos566.OriginalStatement := rfl

theorem original_problem_false : ¬originalProblem :=
  Erdos566.original_statement_false

end Verification
