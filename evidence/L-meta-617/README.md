# L-meta-617: no AND/OR circuit with at most 10 gates for the 3-cube edge function

Evidence for the step L-meta-617 of the pequalnp.com effort ("Find a circuit of AND and OR
gates with at most 10 gates for 'both ends of some edge are true' on the 3-cube, or show none
exists"). The step was withdrawn by the project on 2026-11-23. This is a computer search, not a
Lean proof, and it is not a submission to the project.

## Result

No monotone fan-in-two AND/OR circuit with at most 10 gates computes
f(x) = OR over edges uv of Q3 of (x_u AND x_v), with the edge list of the posted statement:
(0,1) (0,2) (0,4) (1,3) (1,5) (2,3) (2,6) (3,7) (4,5) (4,6) (5,7) (6,7).
So the least size is at least 11, which matches the project's paper count.

## Model (matches lean/PEqualNP/Defs)

- size = number of gates; inputs are wires 0..7, gate j is wire 8 + j.
- Monotone2: every gate is AND or OR with at most two inputs.
- Reduction to the search form, without gaining gates: 0-input gates are constants, 1-input or
  repeated-input gates are copies, reads of wires that do not exist yet are constant false; the
  output is a gate since f is neither constant nor a variable; unused gates can be dropped. So
  each gate is AND or OR of two distinct earlier wires, the output is the last gate, and every
  gate is used.
- Every candidate is checked on all 256 inputs.

## Runs (PySAT, CaDiCaL)

1. Plain encoding (s2.py): UNSAT for exactly 1..9 gates (out2.txt shows 8 and 9).
2. Encoding with symmetry breaking (s3.py): UNSAT for 1..10; size 10 took about 42 minutes
   (out10_sym.txt). Sound constraints: adjacent gates where the second does not read the first
   appear in lexicographic order of their input pairs, and no two gates are identical.
3. Independent route by restriction (s1n.py, run4.py): setting x7 := 0 in a minimal monotone
   circuit removes at least one gate, so L(Q3) >= L(Q3 - v) + 1. Q3 minus vertex 7 (7 inputs, 9
   edges) is UNSAT for 1..9 gates under both encodings (out_q3v_9.txt, out_q3v_plain.txt), so
   L(Q3) >= 11 by this route too.

Sanity check: on the path x0x1 + x1x2 + x2x3 both encodings find a 4-gate circuit and report UNSAT
at 3 gates (out_q3v_plain.txt).

Run with: python3 s3.py 10  (needs python-sat).
