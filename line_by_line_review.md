# Line-by-line review of `main.tex`

This review is keyed to the uploaded `main.tex` line numbers. I focus on lines that affect argument, tone, reviewer risk, or missing content. I do not comment on every LaTeX package line unless it affects the paper.

## Global diagnosis

The paper currently has a good formal spine, but the prose makes the result sound larger and more symmetrical than the mechanisation warrants. The reviewer concern is not fatal. The fix is to say the relationship between restriction and refinement is formally parallel but operationally asymmetric. That is the most important sentence to add.

The paper should sound less like: “We solve recovery.”

It should sound more like: “Here is a necessary discipline on safety claims made through observation interfaces.”

That is more Dijkstra-like. It is sharper and safer.

## Lines 28-34: title

Current title:

```latex
Structural Admissibility for Verification Systems:\
Warrant Debt, Observational Quotients, and Type-Theoretic Verification
```

Problem: strong but slightly overstuffed. “Type-Theoretic Verification” makes the paper sound broader than the presented argument. It also pulls attention away from the core contribution: observation and repair.

Suggested replacement:

```latex
Structural Admissibility for Verification Systems:\
Observation, Warrant Debt, and Factorisation Repair
```

Reason: shorter, more exact, less inflated.

## Lines 47-61: abstract

Current issue: the abstract is solid, but too assertive in two places.

Problem 1: “exactly when” is fine mathematically, but the surrounding prose risks sounding like the paper is claiming a complete theory of safety.

Problem 2: lines 57-60 say admissibility is recovered “only” by rejection/restriction or refinement. That is formally defensible, but a reviewer may object that real safety procedures have many interventions. The fix is to say “at the level of the factorisation criterion”.

Suggested replacement is in `main_dijkstra_revised.tex`.

Core wording to preserve:

```latex
The contribution is to state this discipline explicitly, and to show why
treating such failures as mere noise is unsafe.
```

This captures your actual point.

## Lines 64-82: Introduction TODO block

Current issue: the introduction is not written. The comments are good, but they need to become prose.

Required addition:

1. Verification sees through observation interfaces.
2. Observation interfaces collapse distinctions.
3. A safety claim is unsupported when it depends on a collapsed distinction.
4. This is often misdiagnosed as noise.
5. The paper supplies a precise factorisation test.

Suggested insertion is in `main_dijkstra_revised.tex`, Section 1.

Best Dijkstra-style sentence:

```latex
The problem may not be noise. It may be a failed factorisation.
```

## Lines 84-98: contributions

Current issue: good structure, but “We show that admissibility recovery has two principled forms” needs protection.

Suggested replacement for the last item:

```latex
\item We distinguish two repair forms: predicate rejection or restriction, and
observational refinement. These are formally parallel but not operationally
symmetric.
```

Reason: this directly answers the reviewer concern.

## Line 100: missing outline

Current issue: the paper needs the outline paragraph for submission polish.

Suggested insertion:

```latex
Section~\ref{sec:setting} states the factorisation criterion. Section~\ref{sec:warrant}
uses it to define warrant debt and non-recoverability. Section~\ref{sec:recovery}
explains restriction and refinement. Section~\ref{sec:rocq} describes the Rocq
development and its assumptions. Section~\ref{sec:casestudies} reports the case
studies. Sections~\ref{sec:related} to~\ref{sec:conclusion} place the result,
state its limits, and draw the practical lesson.
```

## Lines 107-118: mathematical setting

Current issue: clean and adequate. No major change needed.

Small improvement: none required. This is already the best kind of prose in the paper: simple, declarative, not grand.

## Lines 122-130: admissibility definition

Current issue: correct.

Suggested addition after line 130:

```latex
This is a support condition. It says that the observation contains enough
information for the predicate being asserted through it.
```

Reason: connects the formal definition to the paper's practical point.

## Lines 134-141: factorisation definition

Current issue: correct.

No change needed.

## Lines 145-154: theorem and empty proof

Current issue: empty proof environment looks unfinished. For a paper submission, do not leave this as a TODO.

Suggested replacement:

```latex
\begin{proof}
This is the standard quotient argument. If \(\Phi\) factors through \(M\), then
\(M(x)=M(y)\) immediately implies that \(\Phi(x)\) and \(\Phi(y)\) have the same
truth value. Conversely, if \(\Phi\) is constant on the fibres of \(M\), define
\(\widehat{\Phi}\) on each observable value by choosing any representative in its
fibre. The constancy condition makes this definition independent of the chosen
representative. In the Rocq development this is the theorem
\texttt{admissible\_iff\_constant\_on\_kernel}.
\end{proof}
```

## Lines 156-157: “formal heart”

Current:

```latex
This equivalence is the formal heart of the paper. All subsequent results
follow from it.
```

Issue: “All subsequent results follow from it” is slightly too strong.

Suggested replacement:

```latex
This equivalence is the formal spine of the paper. Later results use it; they do
not replace it.
```

Reason: stronger style, less overclaiming.

## Lines 166-178: warrant debt

Current issue: good, but “borrows from distinctions” is slightly metaphorical. That is acceptable, but tighten it.

Suggested replacement:

```latex
Warrant debt is the gap between what the observation supports and what the
predicate requires. The term is meant literally. A safety claim made through
\(M\) borrows distinctions that \(M\) does not provide.
```

## Lines 182-195: non-recoverability theorem and proof

Current issue: proof is empty.

Suggested proof:

```latex
\begin{proof}
By congruence of equality under \(f\). In the Rocq development this is the
non-recoverability lemma for post-processing maps over observations.
\end{proof}
```

## Lines 197-201: remark

Current issue: very strong, but good. This is the right Dijkstra tone.

Keep it.

## After line 201: add noise clarification

This is essential because it captures your intended point.

Add subsection:

```latex
\subsection{Why this can be mistaken for noise}

At the observational level, an inadmissibility witness may look unremarkable.
Two executions have the same local trace. Two sampled trajectories have the
same visible readings. Two distributed states have the same local view. It is
tempting to describe the disagreement as measurement noise, modelling
imprecision, or a benign abstraction artefact. Sometimes that is correct. But
when the predicate separates two states that the observation identifies, the
problem is structural. The observation is not merely noisy with respect to the
claim. It is insufficient for the claim.
```

This is one of the most important additions.

## Lines 205-210: consequence for verification

Current issue: good, but “bypasses” is doing a lot of work. Keep it.

Suggested final sentence:

```latex
The assumption merely moves the missing observation into the proof.
```

Reason: shorter and more Dijkstra-like than “relocates the hidden observation inside the proof”.

## Lines 213-218: recovery opening

Current:

```latex
When \(\Phi\) fails to factor through \(M\), there are exactly two principled
responses.
```

Problem: this is the sentence the reviewer will attack.

Replacement:

```latex
At the level of the factorisation criterion, there are two principled repair
forms.
```

Reason: it is mathematically precise and rhetorically protected.

## Lines 220-230: predicate rejection or restriction

Current issue: good, but can be sharper.

Suggested addition:

```latex
Rejection does not always mean weakening the predicate in a crude sense. It
means refusing to assert a claim whose truth is not determined by the available
observation. Restriction is the constructive version of that refusal.
```

## Lines 232-241: observational refinement

Current issue: correct.

No major change needed.

## After observational refinement: add asymmetry subsection

This is the central reviewer-response section.

Add:

```latex
\subsection{Formal duality is not operational symmetry}
\label{subsec:not-symmetric}

Restriction and refinement are formally parallel repair forms. They are not the
same engineering act. Restriction keeps the observation map fixed and changes
the claim. Refinement keeps the claim fixed and changes the observation. Both
can restore factorisation. They pay different costs.

Restriction pays in guarantee strength. The resulting claim may be narrower,
conditional, local, robust only within a margin, or valid only under a specified
synchronisation discipline. Refinement pays in observational burden. The system
must expose more structure, log more information, add a sensor, preserve a
trace, or reconstruct a richer state.
```

This directly answers the critique without conceding that the framework is wrong.

## After asymmetry subsection: add everyday safety subsection

This addresses your concern that both restriction and refinement are already used in everyday safety.

Add:

```latex
\subsection{Everyday safety procedures already use both repairs}
\label{subsec:safety-practice}

The distinction is not exotic. Everyday safety procedures already use both
moves. A restricted operating envelope is predicate restriction: the claim is no
longer that all states are safe, but that states inside a stated envelope are
safe. An added sensor is observational refinement: the claim is kept, but the
interface is strengthened. A lockout condition restricts admissible operation. A
new alarm channel refines observation. A conservative threshold restricts the
claim to a margin. A higher resolution measurement refines the observation.
```

## Lines 247-254: quote under “No invisible axioms”

Current issue: good, but too absolute.

Suggested replacement:

```latex
When a predicate fails to factor through the current observation map, the proof
must not be rescued by an assumption that bypasses the observation boundary. The
claim must be restricted to what the observation supports, or the observation
must be refined until the missing distinction is exposed.
```

## Lines 261-282: library structure

Current issue: useful, but it may overstate the scope if some folders are thin.

If all folders really exist, keep it. If not, compress.

No immediate textual change required unless the repository does not match these folder names.

## Lines 284-289: formal status

Current issue: good but needs modest wording.

Suggested replacement:

```latex
The accompanying Rocq development consists of 39 source files, all of which
compile to \texttt{.vo} files. It contains no admitted lemmas. The remaining
logical strength of the development is confined to eight named axioms. They are
not hidden. They are part of the mathematical specification.
```

## Lines 291-312: axioms

Current issue: this is where the critique is strongest. The text names only three axioms and then sends the reader to `ASSUMPTIONS.md` for the remaining five. That looks like hidden load-bearing material.

Necessary fix: add a table that gives the role of all eight axioms.

Caution: I cannot name the five application-level axioms because their exact names are not present in the uploaded `main.tex`. Do not invent names. Copy the exact Rocq names from `ASSUMPTIONS.md` before submission.

The revised file includes a table with role labels and an explicit TODO in the caption.

## Lines 314-321: mechanisation scope

Current issue: good and necessary.

Keep this. It is modest and protects the paper.

## Lines 324-328: case studies input

Current issue: this depends on `case-studies.tex`, which was not uploaded here. I cannot review that file line by line from the present upload.

Necessary addition after the input:

```latex
\subsection{Comparing the burden across domains}
```

This subsection should explain that the same factorisation failure appears across domains, but the mathematical burden differs. This directly addresses the “discrete vs physical” critique.

## Lines 331-362: related work

Current issue: currently only TODO comments. This must be written before submission.

Needed subsections:

1. Abstraction and abstract interpretation.
2. Runtime verification and monitorability.
3. Consensus and weak memory.
4. Type-theoretic and constructive verification.
5. Mereotopology and region-based spatial reasoning.

The revised file includes full prose and citations.

## Lines 365-379: limitations

Current issue: good, but expand modestly.

Add:

```latex
This asymmetry is a limitation of coverage, but it is not a contradiction. It
reflects the different repair costs of the three domains.
```

Also add:

```latex
Finally, warrant debt is not proposed as a quantitative risk metric here.
```

Reason: prevents overclaiming.

## Lines 382-415: discussion

Current issue: this whole section is still comments and TODOs. It must be written.

Use short, direct paragraphs. Avoid speculative flourish.

Best lines to include:

```latex
A safety property is not only a property of a system. It is also a property of
the relation between the system, the predicate, and the observation interface.
```

and:

```latex
If the missing distinction is irrelevant to the predicate, there is no debt. If
the predicate requires the missing distinction, then calling the discrepancy
noise is unsafe.
```

## Lines 418-432: conclusion

Current issue: mostly good, but too smooth. It should end harder.

Suggested conclusion ending:

```latex
The warning is simple. An admissibility failure may look like noise. It may look
like harmless underspecification. It may look like a modelling convention. But
if the safety predicate depends on a distinction the observation has collapsed,
the problem is structural. The correct response is not optimism. It is
restriction, rejection, or refinement.
```

That is the strongest ending.

## Lines 437-450: assumptions appendix

Current issue: useful audit commands, but the appendix repeats the “documented in ASSUMPTIONS.md” move that the critique objects to.

Add:

```latex
Before submission, this appendix should list all eight axiom names directly.
The current paper text gives the role of all eight, but the exact names of the
five application-level axioms must be copied from \texttt{ASSUMPTIONS.md}.
```

## Lines 453-475: file map

Current issue: good. Keep.

## Lines 480-481: bibliography

Current issue: the bibliography is external and invisible in the uploaded file. The paper needs a stronger cited base.

Add references for:

- Cousot and Cousot on abstract interpretation.
- Clarke et al. on CEGAR.
- Bauer, Leucker, and Schallhart on runtime verification.
- Lamport on Paxos.
- Owens, Sarkar, and Sewell on x86-TSO.
- Alglave, Maranget, and Tautschnig on weak memory.
- Randell, Cui, and Cohn on RCC.
- ISO 31000 and IEC 61508 for ordinary safety and risk practice.
- The Coq/Rocq proof assistant.

The revised file uses an inline `thebibliography` so it is self-contained. If your Springer template requires BibTeX, move those entries into `paper/refs.bib` instead.

## Final judgement

The critique should be answered, not obeyed blindly. Do not pretend the case studies are symmetrical. Do not rush to add new Rocq code unless you have time. The better move is to state the asymmetry as part of the result:

```latex
Restriction and refinement are formally parallel repair forms. They are not the
same engineering act.
```

That sentence should stay.
