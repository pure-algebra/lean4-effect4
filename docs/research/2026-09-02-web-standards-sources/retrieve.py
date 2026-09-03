"""Retrieve the finite bibliography supplied by the user; preserve source bytes."""
import concurrent.futures
import hashlib
import json
import subprocess
from datetime import datetime, timezone
from pathlib import Path

ROOT = Path(__file__).resolve().parent

# Group, title, credited authors, cited edition, filename, candidate URLs.
SOURCES = [
    ("Scheduling", "Semantics of Asynchronous JavaScript", "Matthew C. Loring; Mark Marron; Daan Leijen", "Microsoft Research technical report / DLS 2017", "01-semantics-of-asynchronous-javascript.pdf", ["https://www.microsoft.com/en-us/research/wp-content/uploads/2017/08/asyncNodeSemantics.pdf"]),
    ("Equivalence", "Interaction Trees: Representing Recursive and Impure Programs in Coq", "Li-yao Xia and coauthors", "POPL 2020", "02-interaction-trees.pdf", ["https://arxiv.org/pdf/1906.00046"]),
    ("Equivalence", "Choice Trees: Representing Nondeterministic, Recursive, and Impure Programs in Coq", "Nicolas Chappe; Paul He; Ludovic Henrio; Yannick Zakowski; Steve Zdancewic", "arXiv version 1, 2022", "03-choice-trees-arxiv-v1.pdf", ["https://arxiv.org/pdf/2211.06863v1"]),
    ("Equivalence", "Formal Reasoning about Layered Monadic Interpreters", "Irene Yoon; Yannick Zakowski; Steve Zdancewic", "ICFP 2022", "04-formal-reasoning-about-layered-monadic-interpreters.pdf", ["https://www.ireneyoon.com/paper/fralmi.pdf"]),
    ("Errors", "Handling Algebraic Effects", "Gordon Plotkin; Matija Pretnar", "LMCS 2013", "05-handling-algebraic-effects.pdf", ["https://arxiv.org/pdf/1312.1399"]),
    ("Rows", "Data Types a la Carte", "Wouter Swierstra", "JFP 2008", "06-data-types-a-la-carte.pdf", ["https://webspace.science.uu.nl/~swier004/publications/2008-jfp.pdf"]),
    ("Rows", "Freer Monads, More Extensible Effects", "Oleg Kiselyov; Hiromi Ishii", "Haskell 2015", "07-freer-monads-more-extensible-effects.pdf", ["https://okmij.org/ftp/Haskell/extensible/more.pdf"]),
    ("Rows", "Koka: Programming with Row-Polymorphic Effect Types", "Daan Leijen", "2014", "08-koka-row-polymorphic-effect-types.pdf", ["https://arxiv.org/pdf/1406.2061"]),
    ("Rows", "Generalized Evidence Passing for Effect Handlers", "Ningning Xie; Daan Leijen", "ICFP 2021", "09-generalized-evidence-passing-for-effect-handlers.pdf", ["https://xnning.github.io/papers/multip.pdf", "https://www.microsoft.com/en-us/research/wp-content/uploads/2021/08/genev-icfp21.pdf"]),
    ("Scoped syntax", "Effect Handlers in Scope", "Nicolas Wu; Tom Schrijvers; Ralf Hinze", "Haskell 2014", "10-effect-handlers-in-scope.pdf", ["https://www.cs.ox.ac.uk/people/nicolas.wu/papers/Scope.pdf"]),
    ("Scoped syntax", "Syntax and Semantics for Operations with Scopes", "Maciej Pirog; Tom Schrijvers; Nicolas Wu; Mauro Jaskelioff", "LICS 2018", "11-syntax-and-semantics-for-operations-with-scopes.pdf", ["https://www.fceia.unr.edu.ar/~mauro/pubs/ScopedOps.pdf"]),
    ("Scoped syntax", "A Calculus for Scoped Effects & Handlers", "Roger Bosman; Birthe van den Berg; Wenhao Tang; Tom Schrijvers", "LMCS 2024", "12-a-calculus-for-scoped-effects-and-handlers.pdf", ["https://lmcs.episciences.org/14832/pdf", "https://arxiv.org/pdf/2304.09697"]),
    ("Deferred and modular elaboration", "Latent Effects for Reusable Language Components", "Birthe van den Berg; Tom Schrijvers; Casper Bach-Poulsen; Nicolas Wu", "APLAS 2021", "13-latent-effects-for-reusable-language-components.pdf", ["https://arxiv.org/pdf/2108.11155"]),
    ("Deferred and modular elaboration", "Hefty Algebras: Modular Elaboration of Higher-Order Algebraic Effects", "Casper Bach Poulsen; Cas van der Rest", "POPL 2023", "14-hefty-algebras.pdf", ["https://casperbp.net/store/hefty-algebras.pdf"]),
    ("Deferred and modular elaboration", "A Framework for Higher-Order Effects and Handlers", "Birthe van den Berg; Tom Schrijvers", "2023 preprint", "15-a-framework-for-higher-order-effects-and-handlers-arxiv-v1.pdf", ["https://arxiv.org/pdf/2302.01415v1"]),
    ("Machines and compilation", "Defunctionalization at Work", "Olivier Danvy; Lasse R. Nielsen", "BRICS 2001", "16-defunctionalization-at-work.pdf", ["https://tidsskrift.dk/brics/article/download/21684/19120/49299"]),
    ("Machines and compilation", "Type Directed Compilation of Row-Typed Algebraic Effects", "Daan Leijen", "POPL 2017", "17-type-directed-compilation-of-row-typed-algebraic-effects.pdf", ["https://www.microsoft.com/en-us/research/wp-content/uploads/2016/12/algeff.pdf"]),
    ("Machines and compilation", "Liberating Effects with Rows and Handlers", "Daniel Hillerstrom; Sam Lindley", "TyDe 2016", "18-liberating-effects-with-rows-and-handlers.pdf", ["https://www.dhil.net/research/papers/liberating_effects-tyde2016.pdf", "https://www.pure.ed.ac.uk/ws/portalfiles/portal/27373347/links_effect.pdf"]),
    ("Machines and compilation", "Retrofitting Effect Handlers onto OCaml", "KC Sivaramakrishnan and coauthors", "PLDI 2021", "19-retrofitting-effect-handlers-onto-ocaml.pdf", ["https://anil.recoil.org/papers/2021-pldi-retroeff.pdf"]),
    ("Machines and compilation", "Handlers in Action", "Ohad Kammar; Sam Lindley; Nicolas Oury", "ICFP 2013", "20-handlers-in-action.pdf", ["https://homepages.inf.ed.ac.uk/slindley/papers/handlers.pdf", "https://www.cs.ox.ac.uk/people/ohad.kammar/publications/kammar-lindley-oury-handlers-in-action.pdf"]),
    ("Composition", "Reasoning about Effect Interaction by Fusion", "Zhixuan Yang; Nicolas Wu", "ICFP 2021", "21-reasoning-about-effect-interaction-by-fusion.pdf", ["https://yangzhixuan.github.io/pdf/fused-reasoning-appendices.pdf"]),
    ("Errors / web standard", "Web IDL", "WHATWG", "Living Standard, retrieved 2026-09-02; cited section: #idl-exceptions", "22-web-idl.html", ["https://webidl.spec.whatwg.org/"]),
]


def retrieve(source):
    group, title, authors, edition, filename, urls = source
    folder = "standards" if filename.endswith(".html") else "papers"
    target = ROOT / folder / filename
    target.parent.mkdir(parents=True, exist_ok=True)
    row = dict(id=filename[:2], group=group, title=title, authors=authors,
               cited_edition=edition, candidate_urls=urls,
               file=str(target.relative_to(ROOT)), attempts=[])
    if target.exists():
        raise FileExistsError(f"Refusing to overwrite {target}")
    for url in urls:
        part = target.with_suffix(target.suffix + ".part")
        command = ["curl", "--fail", "--location", "--silent", "--show-error",
                   "--proto", "=https", "--proto-redir", "=https",
                   "--connect-timeout", "15", "--max-time", "60",
                   "--max-filesize", "50000000", "--output", str(part),
                   "--write-out", "%{json}", url]
        result = subprocess.run(command, capture_output=True, text=True)
        try:
            info = json.loads(result.stdout)
        except json.JSONDecodeError:
            info = {}
        attempt = dict(url=url, http_status=info.get("http_code"),
                       final_url=info.get("url_effective"),
                       content_type=info.get("content_type"),
                       curl_exit=result.returncode,
                       retrieved_at=datetime.now(timezone.utc).isoformat())
        if result.stderr:
            attempt["error"] = result.stderr.strip()
        row["attempts"].append(attempt)
        data = part.read_bytes() if part.exists() else b""
        valid = (data.startswith(b"%PDF-") if folder == "papers"
                 else b"Web IDL" in data and b'id="idl-exceptions"' in data)
        if result.returncode == 0 and valid:
            part.rename(target)
            row.update(status="downloaded", source_url=url,
                       final_url=attempt["final_url"],
                       retrieved_at=attempt["retrieved_at"],
                       bytes=len(data), sha256=hashlib.sha256(data).hexdigest())
            print(f"DOWNLOADED {filename} ({len(data)} bytes)", flush=True)
            return row
        if result.returncode == 0:
            attempt["error"] = "Response did not match the expected document format"
        part.unlink(missing_ok=True)
    row["status"] = "unavailable"
    print(f"UNAVAILABLE {filename}: {row['attempts'][-1]}", flush=True)
    return row


if __name__ == "__main__":
    with concurrent.futures.ThreadPoolExecutor(max_workers=4) as pool:
        rows = list(pool.map(retrieve, SOURCES))
    manifest = dict(
        scope="The 21 papers and Web IDL reference named on the attached reading-map page.",
        requested_on="2026-09-02", sources=rows)
    (ROOT / "manifest.json").write_text(json.dumps(manifest, indent=2) + "\n")
    print(f"RESULT {sum(r['status'] == 'downloaded' for r in rows)}/{len(rows)} downloaded")
