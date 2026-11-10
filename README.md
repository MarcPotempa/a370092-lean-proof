# A machine-checked proof of Bala's periodicity conjecture for OEIS A370092

**Statement.** Let a(0) = 1 and a(n) = (-1)^n + (1/2) * Sum_{j=1..n} (1 - (-1)^j - (-2)^j) * binomial(n,j) * a(n-j)
([OEIS A370092](https://oeis.org/A370092), e.g.f. 2*exp(x)/(1 + exp(x) + exp(2x) - exp(3x))).
Peter Bala conjectured (Feb 16 2024) that for every integer k > 2 the sequence a(n) mod k is eventually periodic
with period dividing phi(k).

**What is here.** `Solution.lean` is a complete Lean 4 / Mathlib proof (no `sorry`, axioms: `propext`, `Quot.sound`,
`Classical.choice`) of the statement exactly as formalized in the *OEIS Open* benchmark
(`oeis_370092_conjecture_0`; `Challenge.lean` is the unmodified benchmark file). It proves the sharper fact

> a(n + phi(k)) ≡ a(n) (mod k) for all n ≥ k.

**Priority.** The theorem itself is not new: it was proved by Payam Danesh, *Eventual periodicity of weighted Stirling
transforms and two conjectures of Bala*, Cambridge Open Engage (2026), doi:10.33774/coe-2026-4d6jr (Theorem 5.3),
using Kwong's period bounds for Stirling numbers. This repository adds an independent, self-contained proof,
an explicit threshold (n ≥ k), and, to our knowledge, the first formal verification.

**Idea of the proof.** The generating function is G(e^x - 1) with G(t) = (1+t)/(1 - t^2 - t^3/2), which is not an
integral power series, so the usual Stirling-number argument fails at the prime 2. Instead we expand in differences
with step 2, separately on odd and even arguments:

    a(n) = Sum_{m=0..n} [ h_m * D^m[(2s+1)^n](0) + r_m * D^m[(2s)^n](0) ],   with 2^m h_m and 2^m r_m integers,

where D is the forward difference in s. The identity follows from a telescoping sum. The odd prime powers of k are
then handled term by term. For the 2-part one shows (2X+1)^P = 1 + 2^(e+1) (c X(X+1) + 2R(X)) whenever 2^e | P
(e ≥ 1), which makes every difference D^m of (2s+1)^(n+P) - (2s+1)^n divisible by 2^(a+1) m! for m ≥ 3
(2^a being the exact power of 2 in k), while 2 m! h_m and 4 m! r_m are integers; the even arguments contribute
multiples of 2^(n-2).

**Checking.** Lean v4.27.0 with the Mathlib version pinned by
[formal-conjectures](https://github.com/google-deepmind/formal-conjectures) (branch `auto_oeis`).
With `Challenge.lean` and `Solution.lean` as libraries of that project, the
[Comparator](https://github.com/leanprover/comparator) run with `comparator.json` ends with
`Lean default kernel accepts the solution` / `Your solution is okay!`.

**Credits.** The choice of problem, the proof and its Lean formalization were produced by Claude Fable 5.2
(an AI model by Anthropic; model ID `claude-fable-5-2`, working in Claude Code) on 10 Nov 2026.
The work was commissioned by Dr. Marc Potempa, who set the task and decided to publish it, but did not contribute to
the mathematical content. No human has checked the proof beyond the machine verification described above.

**License.** `Challenge.lean` and the definitions in `Solution.lean` are from formal-conjectures (Apache 2.0);
the remaining content is released under Apache 2.0 as well.
