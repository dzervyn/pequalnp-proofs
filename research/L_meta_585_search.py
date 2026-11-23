"""Search for a monotone circuit with at most four OR gates for L-meta-585.

Run: python -m pip install z3-solver cvc5
     python research/L_meta_585_search.py

AND gates are free here. Flattening AND-only subcircuits makes each OR
operand a conjunction of inputs and earlier OR outputs; the final output
is another conjunction. Thus the search imposes no bound on AND gates.
Redundant OR gates can pad a circuit to four OR gates. Absorption permits
distinct operand sets, so ordering them removes operand symmetry.

The encoding checks every one of the 32 assignments to the five inputs.
UNSAT is solver evidence, not a Lean-checked lower bound: formalizing the
normalization and checking an UNSAT certificate remain separate work.
"""
import json
import time
import z3

INPUTS = 5
OR_GATES = 4
ROWS = 1 << INPUTS
MASK = (1 << ROWS) - 1
EDGES = [(0, 1), (0, 2), (1, 2), (0, 3), (0, 4), (3, 4)]

solver = z3.Solver()
solver.set(timeout=120000)
values = [z3.BitVecVal(sum(((row >> i) & 1) << row for row in range(ROWS)), ROWS)
          for i in range(INPUTS)]

def conjunction(name):
    flags = [z3.Bool(f"{name}_{j}") for j in range(len(values))]
    value = z3.BitVecVal(MASK, ROWS)
    for flag, source in zip(flags, values):
        value = z3.If(flag, value & source, value)
    code = z3.Concat(*[z3.If(flag, z3.BitVecVal(1, 1), z3.BitVecVal(0, 1))
                       for flag in reversed(flags)])
    return value, code

for gate in range(OR_GATES):
    left, left_code = conjunction(f"left{gate}")
    right, right_code = conjunction(f"right{gate}")
    solver.add(left_code != 0, z3.ULT(left_code, right_code))
    output = z3.BitVec(f"gate{gate}", ROWS)
    solver.add(output == (left | right))
    values.append(output)

output, _ = conjunction("output")
target = sum(int(any(((row >> u) & 1) and ((row >> v) & 1) for u, v in EDGES)) << row
             for row in range(ROWS))
solver.add(output == target)
problem = "(set-logic QF_BV)\n" + solver.to_smt2()

start = time.monotonic()
print(json.dumps({"solver": "z3", "version": z3.get_version_string(),
                  "result": str(solver.check()), "seconds": round(time.monotonic() - start, 3)}),
      flush=True)

try:
    import cvc5
except ImportError:
    print("Install cvc5 to cross-check the same formula with a second solver.")
else:
    checker = cvc5.Solver()
    checker.setOption("tlimit-per", "120000")
    parser = cvc5.InputParser(checker)
    parser.setStringInput(cvc5.InputLanguage.SMT_LIB_2_6, problem, "L-meta-585")
    start = time.monotonic()
    while True:
        command = parser.nextCommand()
        if command.isNull():
            break
        answer = command.invoke(checker, parser.getSymbolManager()).strip()
        if answer:
            print(json.dumps({"solver": "cvc5", "version": cvc5.__version__,
                              "result": answer, "seconds": round(time.monotonic() - start, 3)}),
                  flush=True)
