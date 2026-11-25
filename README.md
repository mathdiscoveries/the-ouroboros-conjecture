# The Ouroboros Conjecture: Competing Attractors in Base 10 Among Last-Digit Collatz Maps

Lean 4 (`v4.35.0`) + Mathlib formalization of the base-$b$ last-digit Collatz family
$f_b(n) = n / 2$ (even $n$), $f_b(n) = (n \bmod b)\,n + 1$ (odd $n$), centered on the
base-10 **Ouroboros map** $f = f_{10}$ and the open conjecture (`OuroborosConjecture`)
that every positive integer reaches either $1 \to 2 \to 1$ or
$5 \to 26 \to 13 \to 40 \to 20 \to 10 \to 5$.

**Verification Scope (Partial Lean 4):** Main results in the companion paper: 15 of 16
proved main results in Lean 4 (94%) · 1 of 16 by external computation (exhaustive sweep
and cycle lower bounds through $10^{15}$) · 0 by written proof · Global conjecture open.
Across this repository, 19 library modules in `Ouroboros/` (plus `Challenge.lean` and
`Solution.lean`) import Mathlib directly while the 104 finite certificate shards
(`BasinFiveCert*`, `EvenBasesCert`, `BasinOneLowerCert*`, `BasinOneUpperCert*`, and
`OddSurveyCert*`) verify finite integer inequalities by `Init`-only kernel reduction
(`rfl`). All 38 compared theorems in `Solution.lean` build with zero `sorry`, zero
`native_decide`, and Lean's standard axioms (`propext`, `Classical.choice`, `Quot.sound`)
only, and pass Lean 4.35's official `lake comparator` check.

## Formalized Headline Results (`Challenge.lean` / `Solution.lean`)

1. **Base-4 Collatz equivalence & convergent bases** (`prop_base4_reaches_three_iff`,
   `prop_base4_iff_collatz`, `prop_base2_reaches_one`, `prop_base5_reaches_one`):
   $f_4$ on odd integers $2y+1$ is conjugate to shortcut Collatz $T_C$, and universal
   attraction to $\{1, 3\}$ under $f_4$ is equivalent to the classical Collatz conjecture.
2. **Density-one exponential Terras descent in base 10** (`thm_terras_bound`,
   `thm_terras_density_one`): upper density of the $k$-step non-descent set $E_k$ is at
   most $1.124953 \cdot (0.996423)^k$, so the set of starts with no iterate below $n$ has
   natural density $0$.
3. **Complete all-even-base stopping-time dichotomy** (`thm_even_stopping`): for every
   even base $b \ge 2$, the finite-horizon non-descent density $p_k(b) = d(D_k(b))$
   exists and converges to $p_\infty(b)$, with $p_\infty(b) = 0 \iff b \in \{2, 4, 6, 10\}$;
   descent has natural density $1$ for $b \in \{2, 4, 6, 10\}$ and $p_k(b) \ge \eta_b > 0$
   uniformly for every other even base $b \ge 2$.
4. **Basin of 1: residue law, exact $2$-adic Cantor closure, Hausdorff & box dimension, and elementary bounds**
   (`thm_residue_law`, `thm_basin1_lower`, `thm_basin1_upper_explicit`,
   `thm_basin1_density_zero`, `thm_cantor`): every odd member reaching $1$ satisfies
   $n \equiv 1, 15, \text{or } 17 \pmod{30}$; the $2$-adic closure $\overline{B_1}$ in
   $\mathbb{Z}_2$ equals $(30\mathcal{K}_1 + 1) \cup (30\mathcal{K}_{15} + 15) \cup (30\mathcal{K}_{17} + 17)$,
   is nowhere dense, satisfies the infinite-hit / infinite-exit ball dichotomy, admits a
   surjective ultrametric isometry `itin` onto $\Sigma = \{0, 1000, 1001\}^\omega$ ($r \in \{1, 17\}$)
   and $000\Sigma \sqcup 001\Sigma$ ($r = 15$), has positive finite $\beta$-dimensional
   Hausdorff measure $\frac{1}{2} \le \mathcal{H}^\beta(\overline{B_1}) \le a^{-2} + a < 3.031$,
   exact Hausdorff and box-counting dimension $\dim_H(\overline{B_1}) = \dim_B(\overline{B_1}) = \beta = -\log_2 a \approx 0.62638214$,
   and elementary bounds $a_1^9 X^\gamma \le N_1(\lfloor X \rfloor) \le X^\beta$ for all real $X \ge 1$.
5. **Sharpened basin bounds, weighted charging & strict 2-adic/Archimedean separation**
   (`lem_weighted_tree3`, `thm_basin5_tight`, `thm_basin5_sharp`, `thm_basin5_sharp_gt`,
   `cor_basin_separation_unconditional`, `cor_basin_separation_tendsto_zero_unconditional`,
   `thm_basin_sharp`): pure-kernel certificates discharge $N_1(X) \ge 0.0145\,X^{399/800}$,
   $N_1(X) \le C\,X^{0.6245}$ with strict separation $\limsup (\log N_1(X)/\log X) \le 0.6245 < \beta = \dim_H(\overline{B_1})$,
   $N_5(X) \ge \frac{98959}{2269527 \cdot 3^{13/20}} X^{13/20} > 0.02134\,X^{0.65}$, and
   $N_1(X)/N_5(X) \le C\,X^{-0.0255} \to 0$.
6. **All even bases drift classification** (`thm_even_bases`, `prop_near_zero_band`,
   `cor_drift_growth`): an even base $b \ge 2$ admits nonpositive stationary drift if and
   only if $b \in \{2, 4, 6, 10\}$; stationary drift lies in $[-1/4, 1/4]$ iff
   $b \in \{4, 8, 10, 14\}$ and in $[-1/4, 0)$ iff $b \in \{4, 10\}$; universal
   logarithmic drift growth holds for all even $b \ge 2$.
7. **Odd-base trapdoor, universal Markov absorption & certified 905/999 odd-base survey**
   (`prop_odd_runaway`, `thm_odd_trapdoor_rootless`, `lem_base17_runaway`,
   `thm_odd_densities_rootless`, `thm_odd_survey`, `thm_odd_table_examples`):
   even-digit runaway divergence, rootless odd-base trapdoor density $1/b$, certified
   base-17 divergence, universal lower-density bounds $\tau_b + \rho_b \le 1$ for every
   odd $b \ge 3$ with exact rational densities whenever $\tau_b + \rho_b = 1$, pure-kernel
   certification of 905 of the 999 odd bases $3 \le b \le 1{,}999$ (27 trap-only + 878 split),
   and exact table values for $b \in \{3, 5, 7, 13\}$ ($\tau_{13} = 13210/16991$, $\rho_{13} = 3781/16991$).
8. **Base-10 cycle algebra & classification for $\le 3$ odd members**
   (`cycle_n5_eq_n3_add_n7`, `lem_halving_budget`, `thm_cycle_tail_64000`,
   `cycle_m1_unique`, `cycle_m2_classification`, `cycle_m3_unique`, `f_cycle_one`,
   `f_cycle_five`): $n_5 = n_3 + n_7$, halving-budget bounds, high-halving tail
   ($K > 64{,}000$ at minimum $\ge 10^{15}$ forces $m \ge 20{,}190$), and unconditional
   uniqueness/classification of all cycles with $m \in \{1, 2, 3\}$ odd members.
9. **Congruence-class completions & exact base-$b$ suffix-closure dimension**
   (`thm_suffix_class`, `cor_suffix_dimension`): every congruence class $a \pmod m$
   contains infinitely many members of $\mathcal{B}_5$ and satisfies the exact $M = 30 \cdot 2^{\max(0, v_2(m)-1)}$
   live-residue dichotomy for $\mathcal{B}_1$; for every base $b = 2^t u \ge 2$ ($u$ odd),
   the reversed base-$b$ suffix closure $\mathcal{E}_b \subset [0, 1]$ of $\mathcal{B}_1$
   has exact Hausdorff and box-counting dimension $(\log u + t \log \lambda) / \log b$
   ($\lambda^4 = \lambda^3 + 2$, yielding $\approx 0.62638214$ in base $2$, $\approx 0.88752982$
   in base $10$, and $1$ with $\mathcal{E}_7 = [0, 1]$ in base $7$), while the analogous
   closure $\mathcal{E}_{5,b}$ for $\mathcal{B}_5$ equals $[0, 1]$ in every base $b \ge 2$.

Companion working paper, external verification archive (exhaustive sweep and cycle lower
bounds through $10^{15}$), and prior-work search logs live at
https://mathdiscoveries.org/results/the-ouroboros-conjecture.html.

## Build & Verify

```bash
lake build Challenge Solution Ouroboros
lake comparator --inadvisably-no-sandbox
lake env lean Ouroboros/Verify.lean
```

## Disclosure & License

Generated and checked by AI research agents built and directed by **Tyler B. Hughes**.
Cross-family (`anthropic` Claude Opus) blind statement-fidelity review verified all newly
added modules. No human mathematician has yet refereed the proof. Licensed under Apache-2.0.
