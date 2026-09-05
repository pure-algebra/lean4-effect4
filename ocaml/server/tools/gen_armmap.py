#!/usr/bin/env python3
"""Generate `e4d_armmap.ml` from the avatar's sources and from `src/Effect4/Machine/*.lean`.

Nothing in the daemon's `explain` answer is hand-copied. Everything below is read off the
avatar itself, so that seat W1's port -- which moved the store arms out of `deep_fibers.ml`
into `deep_stores.ml` and `deep_layer.ml`, and put the four store families behind one
`Op_store` carrying a `store_request` -- lands without this script changing.

The unit of attribution is a **handler label**, of two kinds:

  `arm_fork`          a named function, `arm_*` or `answer_*`, in any avatar module;
  `case Rref_make`    a match case in a dispatch table (`effc` in `deep_fibers.ml`,
                      `store_arm` in `deep_stores.ml`) whose body pushes the row itself
                      rather than calling a named arm.

Five tables are emitted:

  dispatch     (constructor, label, row-name argument) -- one row per case of a dispatch
               table. The constructor is the innermost one of the pattern, so `Op_store` is
               transparent and `Rref_get` is what a row resolves through.
  row_names    label -> the service row names its body pushes.
  arms         label -> its doc comment and the `` `…:N` `` citations in it, each resolved
               against the Lean file (see `resolve`).
  symbols      label -> the `src/Effect4/Machine/*.lean` declarations its doc names by name.
  step_ops     the corpus DSL's step table: step name -> the constructor it performs.
  caller_rows  a row a caller module pushes around a `perform` (`op yield`) -> that
               constructor.

Citations resolve against every Lean module of the machine (`src/Effect4/Machine/*.lean`
since "Prod cleanup 3", `src/Effect4/Machine/*.lean` before it), not only `Fibers.lean`: seat W1's
port moved the store arms into `deep_stores.ml`, whose arms cite `Stores.lean`. A bare `:N`
resolves against the *home* module of the avatar file it was written in (`deep_stores.ml`
-> `Stores.lean`), which is the avatar's own convention.

Usage:
  gen_armmap.py <lean1.lean,lean2.lean,...> <avatar module.ml> ... > e4d_armmap.ml
  gen_armmap.py <directory of .lean files>  <avatar module.ml> ... > e4d_armmap.ml
"""
import os
import re
import sys


def ocaml_string(s):
    out = s.replace("\\", "\\\\").replace('"', '\\"')
    return '"' + out.replace("\n", "\\n").replace("\t", "\\t").replace("\r", "\\r") + '"'


def read(path):
    with open(path, encoding="utf-8") as handle:
        return handle.read()


# --- reading the avatar ----------------------------------------------------------------

FUNCTION = re.compile(
    r"^(?:and|let(?: rec)?)\s+((?:arm|answer|park|fire|exit|interrupt|countdown|race|store)"
    r"_[a-z_0-9]+|guard|spawn|start|drive|exec|finish|run_control|run_under_handler|fail_op)\b")
CASE = re.compile(r"^(\s*)\|\s*(Op_[A-Za-z_0-9]+|R[a-z][A-Za-z_0-9]*)\b")
COMMENT_END = re.compile(r"\*\)\s*$")
CITE = re.compile(r"`([^`\n]*:\d[^`\n]*)`")
ROP = re.compile(r'push_row\s*\(\s*R(?:op|answer)\s*\(\s*"([A-Za-z0-9_]+)"')
LIT_AFTER_MF = re.compile(r'(?:arm_[a-z_0-9]+\s+m\s+f|(?<![a-z_])state)\s+"([A-Za-z0-9_]+)"')
NAME_BINDING = re.compile(r'let\s+name\s*=(?:.|\n)*?(?=\n\s*(?:let|match|push_row|in\b))')
LIT = re.compile(r'"([A-Za-z][A-Za-z0-9_]*)"')
ARM_CALL = re.compile(r"\b(arm_[a-z_0-9]+)\b")
# The innermost constructor of a pattern or an expression: `Op_store (Rref_get h)` is
# `Rref_get`, `Op_fork (code, daemon)` is `Op_fork`.
INNER = re.compile(r"\b(Op_[A-Za-z_0-9]+|R[a-z][A-Za-z_0-9]*)\b")


def doc_above(lines, index):
    j = index - 1
    while j >= 0 and lines[j].strip() == "":
        j -= 1
    if j < 0 or not COMMENT_END.search(lines[j]):
        return ""
    k = j
    while k >= 0 and "(*" not in lines[k]:
        k -= 1
    return "\n".join(lines[k:j + 1]).strip() if k >= 0 else ""


def home_lean(module_path, lean_paths):
    """The Lean module an avatar file is the port of: `deep_stores.ml` -> `Stores.lean`."""
    base = module_path.split("/")[-1]
    if base.startswith("deep_") and base.endswith(".ml"):
        stem = base[len("deep_"):-len(".ml")]
        for path in lean_paths:
            if path.split("/")[-1].lower() == stem + ".lean":
                return path
    for path in lean_paths:
        if path.endswith("Fibers.lean"):
            return path
    return lean_paths[0]


def blocks(text):
    """(label, body, doc) for every named function and every dispatch case."""
    lines = text.split("\n")
    marks = []  # (line index, label, indent or None)
    for i, line in enumerate(lines):
        function = FUNCTION.match(line)
        if function:
            marks.append((i, function.group(1), None))
            continue
        case = CASE.match(line)
        if case:
            marks.append((i, "case " + case.group(2), len(case.group(1))))
    out = []
    enclosing = {}
    latest_function = None
    for line_no, label, indent in marks:
        if indent is None:
            latest_function = label
        elif latest_function is not None:
            enclosing.setdefault(label, latest_function)
    for index, (line_no, label, indent) in enumerate(marks):
        end = len(lines)
        for later_no, _later_label, later_indent in marks[index + 1:]:
            # A function ends at the NEXT MARK OF EITHER KIND -- including the first case of
            # a dispatch table it opens, so `store_arm` is not credited with the rows of the
            # thirty cases inside it, and a function at the end of a file is not credited
            # with everything after it. A case ends at the next case at the same or smaller
            # indent, or at the next function.
            if indent is None:
                end = later_no
                break
            if later_indent is None or later_indent <= indent:
                end = later_no
                break
        out.append((label, "\n".join(lines[line_no:end]), doc_above(lines, line_no)))
    return out, enclosing


def row_names_of(body):
    names = list(dict.fromkeys(ROP.findall(body)))
    for lit in LIT_AFTER_MF.findall(body):
        if lit not in names:
            names.append(lit)
    for chunk in NAME_BINDING.findall(body):
        for lit in LIT.findall(chunk):
            if lit not in names:
                names.append(lit)
    return names


def dispatch_of(blocks_):
    """(constructor, label, row-name argument) for every dispatch case."""
    rows = []
    for label, body, _doc in blocks_:
        if not label.startswith("case "):
            continue
        constructor = label[len("case "):]
        head = body.split("->", 1)
        pattern = head[0]
        inner = INNER.findall(pattern)
        constructor = inner[-1] if inner else constructor
        rest = head[1] if len(head) > 1 else ""
        call = ARM_CALL.search(rest)
        target = call.group(1) if call else label
        literal = LIT_AFTER_MF.search(rest)
        rows.append((constructor, target, literal.group(1) if literal else None))
    return rows


# --- the Lean file ---------------------------------------------------------------------

DECL = re.compile(r"^\s*(?:@\[[^\]]*\]\s*)?(?:private\s+|partial\s+|noncomputable\s+)*"
                  r"(def|structure|inductive|abbrev|theorem|instance)\s+([^\s:(\[]+)")


def lean_index(text):
    lines = text.split("\n")
    decls = [(i + 1, DECL.match(line).group(2)) for i, line in enumerate(lines)
             if DECL.match(line)]
    return lines, decls


def decl_at(decls, line_no):
    found = None
    for start, name in decls:
        if start <= line_no:
            found = name
        else:
            break
    return found


def resolve(token, leans, home):
    """(kind, [(file, line, declaration or None)]).

    `exact`: the token occurs in one of the Lean modules as a whole citation token --
    delimited on both sides, so `:550` does not match inside `:5501`. `byLine`: the token
    names a line, either explicitly (`Stores.lean:653`) or bare (`:550`, which means a line
    of the avatar file's home module); reported unverified. Anything else is `unresolved`.
    """
    pattern = re.compile(r"(?<![0-9A-Za-z_:.-])" + re.escape(token) + r"(?![0-9])")
    sites = []
    for path, (lines, decls) in leans.items():
        for i, line in enumerate(lines):
            if pattern.search(line):
                sites.append((path, i + 1, decl_at(decls, i + 1)))
    if sites:
        return ("exact", sites[:4])
    named = re.fullmatch(r"([A-Za-z]+)\.lean:(\d+)(?:-\d+)?", token)
    if named:
        for path, (lines, decls) in leans.items():
            if path.split("/")[-1].lower() == named.group(1).lower() + ".lean":
                line_no = int(named.group(2))
                if 1 <= line_no <= len(lines):
                    return ("byLine", [(path, line_no, decl_at(decls, line_no))])
    bare = re.fullmatch(r":(\d+)(?:-\d+)?", token)
    if bare:
        lines, decls = leans[home]
        line_no = int(bare.group(1))
        if 1 <= line_no <= len(lines):
            return ("byLine", [(home, line_no, decl_at(decls, line_no))])
    return ("unresolved", [])


def repo_relative(path):
    """Paths in the answers are repo-relative: an absolute build path is not a citation."""
    path = path.replace("\\", "/")
    for marker in ("/src/Effect4/", "/Effect4/", "/workshop/"):
        cut = path.find(marker)
        if cut >= 0:
            return path[cut + 1:]
    return path.split("/")[-1]


def lean_files(argument):
    """The Lean modules: a comma-separated list, or a directory of `.lean` files (with
    `Fibers.lean` first, as the shell build listed it: it is the home module of every avatar
    file that is not a `deep_*` port)."""
    if os.path.isdir(argument):
        names = sorted(name for name in os.listdir(argument) if name.endswith(".lean"))
        names.sort(key=lambda name: (name != "Fibers.lean", name))
        return [os.path.join(argument, name).replace("\\", "/") for name in names]
    return argument.split(",")


def main():
    lean_paths = lean_files(sys.argv[1])
    modules = sys.argv[2:]
    leans = {path: lean_index(read(path)) for path in lean_paths}

    all_blocks = []
    homes = {}
    enclosing = {}
    for path in modules:
        home = home_lean(path, lean_paths)
        found, within = blocks(read(path))
        enclosing.update(within)
        for block in found:
            all_blocks.append(block)
            homes.setdefault(block[0], home)

    # one entry per label; a label defined twice keeps the first (the avatar has none)
    seen = {}
    ordered = []
    for label, body, doc in all_blocks:
        if label in seen:
            seen[label] = (seen[label][0] + "\n" + body, seen[label][1] or doc)
        else:
            seen[label] = (body, doc)
            ordered.append(label)

    dispatch = dispatch_of(all_blocks)

    # Every declaration of every Deep module, so a doc that names `interruptRecord` or
    # `Stores.empty` resolves wherever it lives.
    by_name = {}
    for lean_path, (lean_lines, decls) in leans.items():
      for start, decl_name in decls:
        by_name.setdefault(decl_name, (lean_path, start))
        by_name.setdefault(decl_name.split(".")[-1], (lean_path, start))
    CTOR = re.compile(r"^\s*\|\s*([a-zA-Z][A-Za-z0-9_']*)")
    FIELD = re.compile(r"^\s*([a-z][A-Za-z0-9_']*)\s*:")
    for lean_path, (lean_lines, _decls) in leans.items():
        current = None
        for i, line in enumerate(lean_lines):
            match = DECL.match(line)
            if match:
                current = match.group(2)
                continue
            if current is None:
                continue
            hit = CTOR.match(line) or FIELD.match(line)
            if hit:
                by_name.setdefault(current + "." + hit.group(1), (lean_path, i + 1))

    # the corpus DSL step table, and the rows a caller pushes around a `perform`
    step_ops, caller = [], []
    for path in modules:
        text = read(path)
        for line in text.split("\n"):
            hit = re.search(r'\|\s*"([A-Za-z0-9_]+)"\s*->\s*Effect\.perform\s*\((.*)$', line)
            if hit:
                inner = INNER.findall(hit.group(2))
                if inner and (hit.group(1), inner[-1]) not in step_ops:
                    step_ops.append((hit.group(1), inner[-1]))
        lines = text.split("\n")
        for i, line in enumerate(lines):
            hit = ROP.search(line)
            if not hit:
                continue
            window = "\n".join(lines[i:i + 4])
            perform = re.search(r"Effect\.perform\s*\((.*)", window)
            if perform:
                inner = INNER.findall(perform.group(1))
                if inner and (hit.group(1), inner[-1]) not in caller:
                    caller.append((hit.group(1), inner[-1]))

    print("(* GENERATED by ocaml/server/tools/gen_armmap.py (server/dune). Do not edit. *)")
    print("(* Sources: %s, and %s *)"
          % (", ".join(m.replace("\\", "/").split("/")[-1] for m in modules),
             ", ".join(repo_relative(p) for p in lean_paths)))
    print()
    print("(* (constructor, handler label, row-name argument) -- the dispatch tables. *)")
    print("let dispatch : (string * string * string option) list = [")
    for ctor, label, name in dispatch:
        print("  (%s, %s, %s);" % (ocaml_string(ctor), ocaml_string(label),
                                   "None" if name is None else "Some " + ocaml_string(name)))
    print("]")
    print()
    print("(* handler label -> the service row names its body pushes. *)")
    print("let row_names : (string * string list) list = [")
    for label in ordered:
        names = row_names_of(seen[label][0])
        if names:
            print("  (%s, [%s]);" % (ocaml_string(label),
                                     "; ".join(ocaml_string(n) for n in names)))
    print("]")
    print()
    print("(* corpus DSL step name -> the effect constructor it performs. *)")
    print("let step_ops : (string * string) list = [")
    for name, ctor in step_ops:
        print("  (%s, %s);" % (ocaml_string(name), ocaml_string(ctor)))
    print("]")
    print()
    print("(* row name -> the effect constructor a caller module brackets with it. *)")
    print("let caller_rows : (string * string) list = [")
    for name, ctor in caller:
        print("  (%s, %s);" % (ocaml_string(name), ocaml_string(ctor)))
    print("]")
    print()
    # A dispatch case with no doc of its own inherits the doc of the function whose match it
    # is a case of: `case Rref_make` is a case of `store_arm`, which cites `Stores.lean`.
    print("(* dispatch case -> the function whose match it is a case of. *)")
    print("let enclosing : (string * string) list = [")
    for label in ordered:
        if label in enclosing:
            print("  (%s, %s);" % (ocaml_string(label), ocaml_string(enclosing[label])))
    print("]")
    print()
    print("(* handler label -> the src/Effect4/Machine/*.lean declarations its doc names. *)")
    print("let symbols : (string * (string * string * int) list) list = [")
    IDENT = re.compile(r"`([A-Za-z][A-Za-z0-9_.']*)`")
    for label in ordered:
        found = []
        for ident in dict.fromkeys(IDENT.findall(seen[label][1])):
            target = by_name.get(ident) or by_name.get(ident.split(".")[-1])
            if target and (ident,) + target not in found:
                found.append((ident,) + target)
        if found:
            print("  (%s, [%s]);" % (ocaml_string(label),
                                     "; ".join("(%s, %s, %d)"
                                               % (ocaml_string(i), ocaml_string(repo_relative(f)), l)
                                               for i, f, l in found)))
    print("]")
    print()
    print("(* handler label -> (doc, citations). *)")
    print("type site = { file : string; line : int; decl : string option }")
    print("type citation = { token : string; resolution : string; sites : site list }")
    print()
    print("let arms : (string * string * citation list) list = [")
    for label in ordered:
        doc = seen[label][1]
        print("  (%s, %s, [" % (ocaml_string(label), ocaml_string(doc)))
        for token in dict.fromkeys(CITE.findall(doc)):
            kind, sites = resolve(token, leans, homes.get(label, lean_paths[0]))
            rendered = "; ".join(
                "{ file = %s; line = %d; decl = %s }"
                % (ocaml_string(repo_relative(f)), line, "None" if decl is None else "Some " + ocaml_string(decl))
                for f, line, decl in sites)
            print("    { token = %s; resolution = %s; sites = [%s] };"
                  % (ocaml_string(token), ocaml_string(kind), rendered))
        print("  ]);")
    print("]")
    print()
    print("let lean_sources : (string * int) list = [")
    for path, (lines, _decls) in leans.items():
        print("  (%s, %d);" % (ocaml_string(repo_relative(path)), len(lines)))
    print("]")
    print("let lean_source = %s" % ocaml_string(repo_relative(lean_paths[0])))


if __name__ == "__main__":
    main()
