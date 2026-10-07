#!/usr/bin/env python3
"""Line attribution for the Qhl Lean sources (the paper's code-metrics tables).

Every physical line of every .lean file under Qhl/ is put in exactly one bin:
  blank -- whitespace-only lines (uncounted in the tables);
  Com.  -- lines lying fully inside a block comment /- .. -/ (including
           /-- .. -/ and /-! .. -/), and lines whose first token is `--`;
  Proof -- lines strictly after the top-level `:=` of a theorem / lemma /
           example declaration, or of an instance whose body is a tactic
           proof (`:= by`), up to the end of that declaration (term and
           tactic proofs alike); the line carrying the `:=` itself is Spec;
  Spec  -- everything else (statements, definitions, notation, structure).
By construction Spec + Proof + Com. + blank equals `wc -l` per file; the
script re-checks that sum per directory and fails loudly if it ever drifts.
"""
import re, sys
from pathlib import Path

PROOF_KWS = ("theorem", "lemma", "example")
DECL_RE = re.compile(
    r"^(?:@\[[^\]]*\]\s*)*(?:(?:private|protected|noncomputable|scoped|local)\s+)*"
    r"(theorem|lemma|example|instance|def|abbrev|structure|inductive|class|axiom)\b")
OPEN, CLOSE = "([{⟨⦃", ")]}⟩⦄"

def code_of(line, depth):
    """Strip comments; return (code text, block-comment depth after the line)."""
    out, i, n = [], 0, len(line)
    while i < n:
        two = line[i:i + 2]
        if depth == 0 and two == "--":
            break
        if two == "/-":
            depth += 1; i += 2
        elif depth > 0 and two == "-/":
            depth -= 1; i += 2
        elif depth == 0:
            out.append(line[i]); i += 1
        else:
            i += 1
    return "".join(out), depth

def scan_assign(code, bdepth):
    """Scan one line for a top-level `:=` (outside brackets).
    Return (index after `:=` or None, bracket depth after the line)."""
    j = 0
    while j < len(code):
        ch = code[j]
        if ch in OPEN: bdepth += 1
        elif ch in CLOSE: bdepth -= 1
        elif bdepth == 0 and code[j:j + 2] == ":=":
            return j + 2, bdepth
        j += 1
    return None, bdepth

def after_assign(kind, rest):
    """Mode transition once the top-level `:=` is found; `rest` follows it.
    Return (mode, inst_pending)."""
    rest = rest.strip()
    if kind == "instance" and rest and not rest.startswith("by"):
        return "top", False         # term-mode instance: body stays Spec
    if kind == "instance" and not rest:
        return "proof", True        # decide on the first body line
    return "proof", False

def classify(path):
    """Return dict spec/proof/com/blank for one file."""
    c = {"spec": 0, "proof": 0, "com": 0, "blank": 0}
    depth = 0                      # block-comment nesting
    mode = "top"                   # top | head (decl seen, := pending) | proof
    kind = None                    # decl keyword of the current declaration
    bdepth = 0                     # bracket depth inside the current decl head
    inst_pending = False           # instance: proof-kind iff body starts `by`
    for raw in path.read_text(encoding="utf-8").splitlines():
        code, depth = code_of(raw, depth)
        if raw.strip() == "":
            c["blank"] += 1; continue
        if code.strip() == "":
            c["com"] += 1; continue
        # a fresh top-level (column-0) code line ends any open declaration
        if code[0] not in " \t" and mode != "top":
            mode, kind, bdepth, inst_pending = "top", None, 0, False
        if mode == "top":
            m = DECL_RE.match(code.strip())
            c["spec"] += 1
            if m and code[0] not in " \t":
                kind = m.group(1)
                if kind in PROOF_KWS or kind == "instance":
                    mode, bdepth = "head", 0
                    # the decl's own line may already carry the top-level `:=`
                    hit, bdepth = scan_assign(code, bdepth)
                    if hit is not None:
                        mode, inst_pending = after_assign(kind, code[hit:])
        elif mode == "head":
            # scan for a top-level `:=` outside (), [], {}, anglebrackets
            hit, bdepth = scan_assign(code, bdepth)
            c["spec"] += 1          # the `:=` line itself is Spec
            if hit is not None:
                mode, inst_pending = after_assign(kind, code[hit:])
        else:                       # proof body
            if inst_pending:        # first body line of a bare `instance ... :=`
                inst_pending = False
                if not code.strip().startswith("by"):
                    mode = "top"; c["spec"] += 1; continue
            c["proof"] += 1
    return c

def main():
    root = Path(sys.argv[1] if len(sys.argv) > 1 else ".") / "Qhl"
    comps = {}
    for f in sorted(root.rglob("*.lean")):
        comp = f.relative_to(root).parts[0] if f.relative_to(root).parts[:-1] else "(root)"
        comps.setdefault(comp, {}).setdefault(f, classify(f))
    hdr = f"{'component/file':44s} {'Spec':>7s} {'Proof':>7s} {'Com.':>6s} {'blank':>6s} {'wc -l':>7s}"
    print(hdr); print("-" * len(hdr))
    tot = {"spec": 0, "proof": 0, "com": 0, "blank": 0}
    for comp, files in comps.items():
        s = {k: sum(c[k] for c in files.values()) for k in tot}
        wc = sum(sum(1 for _ in f.open()) for f in files)
        assert sum(s.values()) == wc, f"{comp}: attribution does not sum to wc -l"
        print(f"{comp:44s} {s['spec']:7d} {s['proof']:7d} {s['com']:6d} {s['blank']:6d} {wc:7d}")
        for k in tot: tot[k] += s[k]
        if comp == "Examples":
            for f, cf in files.items():
                print(f"  {f.name:42s} {cf['spec']:7d} {cf['proof']:7d} "
                      f"{cf['com']:6d} {cf['blank']:6d} {sum(cf.values()):7d}")
    print("-" * len(hdr))
    print(f"{'total':44s} {tot['spec']:7d} {tot['proof']:7d} {tot['com']:6d} "
          f"{tot['blank']:6d} {sum(tot.values()):7d}")

if __name__ == "__main__":
    main()
