#!/usr/bin/env python3
"""Build offline documentation; requires pandoc and Python Pygments."""
from html import escape
from pathlib import Path
import subprocess

from pygments import highlight
from pygments.formatters import HtmlFormatter
from pygments.lexers import get_lexer_by_name

ROOT = Path(__file__).resolve().parents[1]
formatter = HtmlFormatter(cssclass="highlight", style="friendly")
lexer = get_lexer_by_name("lean4")

THEMATIC_DIAGRAMS = [
    ("Endgame", "Paper assembly"),
    ("ComplexGaussianHermite", "Complex Gaussian and Hermite analysis"),
    ("GinibreMeasureGeometry", "Ginibre measure and holomorphic geometry"),
    ("DeficitsEquality", "Poincaré deficits and equality"),
    ("WeakSobolev", "Weak Sobolev domains and collision capacity"),
    ("GeneratorSemigroup", "Diffusion operators and analytic semigroups"),
    ("PolynomialRadial", "Polynomial, radial and equilibrium sectors"),
    ("GaussianLSI", "Gaussian log-Sobolev and entropy"),
    ("StochasticCalculus", "Stochastic calculus foundations"),
    ("StochasticDynamics", "Ginibre stochastic dynamics"),
    ("MatrixLift", "Matrix lift and eigenvector overlaps"),
    ("NonQuadratic", "Nonquadratic potentials"),
]
diagrams = "".join(
    f'<details{" open" if name == "Endgame" else ""}><summary>{escape(title)}</summary>'
    f'<div class="diagram">{(ROOT / "diagrams" / (name + ".svg")).read_text()}</div></details>'
    for name, title in THEMATIC_DIAGRAMS
)


def markdown(name):
    return subprocess.run(
        ["pandoc", "--from=gfm", "--to=html5", "--id-prefix=" + Path(name).stem.lower() + "-", str(ROOT / name)],
        check=True, capture_output=True, text=True,
    ).stdout


files = sorted((ROOT / "GinibrePoincare").rglob("*.lean"))
files += [ROOT / "GinibrePoincare.lean", ROOT / "AxiomAudit.lean"]
sources = []
for path in files:
    relative = path.relative_to(ROOT).as_posix()
    group = path.parent.name if path.parent != ROOT else "Project"
    anchor = "source-" + relative.replace("/", "-").replace(".", "-")
    sources.append(
        f'<details class="source" id="{anchor}" data-name="{escape(relative.lower())}">'
        f'<summary><span class="badge {group.lower()}">{group}</span> '
        f'{escape(relative)} <a href="#{anchor}" aria-label="Link to this module">#</a></summary>'
        + highlight(path.read_text(), lexer, formatter) + '</details>'
    )

css = """
:root { color-scheme: light; --ink:#172b43; --muted:#50647a; --line:#d6e0eb; }
* { box-sizing:border-box; }
body { margin:0; background:#f3f6fb; color:var(--ink); font:17px/1.65 system-ui,sans-serif; }
header { background:linear-gradient(120deg,#163354,#35539b); color:white; padding:3.5rem max(5vw,1rem); }
header h1 { font-size:clamp(2rem,5vw,3.5rem); line-height:1.15; margin:.4rem 0 1rem; }
header p { max-width:760px; margin:.5rem 0; }
.eyebrow { text-transform:uppercase; letter-spacing:.16em; font-size:.8rem; color:#bde9ff; }
nav { display:flex; flex-wrap:wrap; gap:.7rem 1.5rem; padding:1rem max(5vw,1rem); background:white; border-bottom:1px solid var(--line); }
a { color:#1859a3; text-underline-offset:3px; }
main { max-width:1200px; margin:auto; padding:2rem 1rem; }
section { background:white; padding:clamp(1rem,4vw,2.5rem); margin-bottom:2rem; border:1px solid var(--line); border-top:5px solid #2874bd; border-radius:10px; }
section#status { border-top-color:#16836d; } section#dependencies { border-top-color:#8057b5; } section#sources { border-top-color:#c07818; }
h1,h2,h3 { line-height:1.3; } section h1,section>h2 { margin-top:0; }
h2 { color:#244c7a; margin-top:2rem; } h3 { color:#166e60; }
li { margin:.35rem 0; } code { font-size:.88em; overflow-wrap:anywhere; }
:not(pre)>code { background:#edf2fa; color:#713d91; padding:.1rem .3rem; border-radius:4px; }
pre { overflow:auto; padding:1rem; background:#f4f7fa; border:1px solid var(--line); border-radius:6px; font-size:14px; line-height:1.6; tab-size:2; }
pre code { overflow-wrap:normal; }
.note { background:#edf7f5; border-left:4px solid #16836d; padding:.8rem 1rem; }
.diagram { overflow:auto; } .diagram svg { width:100%; height:auto; min-width:700px; }
input { width:100%; padding:.8rem; font:inherit; border:1px solid #8296b0; border-radius:6px; margin:.5rem 0; }
details { margin:.7rem 0; border:1px solid var(--line); border-radius:6px; }
summary { padding:.8rem; cursor:pointer; overflow-wrap:anywhere; font-size:.9rem; }
summary:hover { background:#eef4fc; } details .highlight { padding:0 .7rem; }
.badge { display:inline-block; border-radius:4px; padding:.1rem .4rem; background:#e7edf6; color:#344f72; font-size:.75rem; font-weight:700; }
.analysis { background:#e2f3ed; color:#12614f; } .concrete { background:#e2edff; color:#234d91; } .endgame { background:#f0e7fa; color:#704295; }
footer { text-align:center; padding:0 1rem 2rem; color:var(--muted); font-size:.85rem; }
:focus-visible { outline:3px solid #a75911; outline-offset:3px; }
[hidden] { display:none!important; }
@media print { body { background:white; font-size:11pt; } header { background:white; color:var(--ink); padding:1rem; } nav,.search { display:none; } section { break-inside:auto; border:0; padding:0; } .diagram svg { min-width:0; } pre { white-space:pre-wrap; } }
"""

html = f'''<!doctype html>
<html lang="en"><head><meta charset="utf-8"><meta name="viewport" content="width=device-width,initial-scale=1">
<title>Ginibre Poincaré — Lean documentation</title>
<style>{css}\n{formatter.get_style_defs('.highlight')}</style></head>
<body><header><div class="eyebrow">Mathematical formalization · Lean</div>
<h1>Ginibre Poincaré</h1><p>Full-paper formalization: project documentation, thematic dependencies, and Lean source.</p>
<p>Scope: all asserted results of arXiv:2608.19358v2, including Appendices A–B. Open Problems 1.11, 1.15 and 1.16 and Appendix C numerical experiments are outside theorem certification. Checked coverage and remaining work appear below.</p></header>
<nav aria-label="Contents"><a href="#overview">Overview &amp; build</a><a href="#status">Formalization status</a><a href="#review">Correspondence review</a><a href="#dependencies">Thematic dependency diagrams</a><a href="#sources">Lean sources ({len(files)})</a></nav>
<main><section id="overview">{markdown('README.md')}</section>
<section id="status"><p class="note">The status below reproduces the project's checked-in documentation. This HTML generation does not rerun the Lean build or axiom audit.</p>{markdown('STATUS.md')}</section>
<section id="review">{markdown('CORRESPONDENCE_REVIEW.md')}</section>
<section id="dependencies"><h2>Thematic dependency diagrams</h2><p>The twelve thematic subprojects cover the full-paper objective. These maps show relationships between subprojects; they do not certify that every paper result is complete. STATUS.md records verified scope and remaining work, and REPORT.md records numbered statement coverage. The complete imports and declarations appear in the source browser below.</p>{diagrams}</section>
<section id="sources"><h2>Lean source browser</h2><p>Expand a module to read its syntax-highlighted source. Colors distinguish analysis, concrete constructions, and endgame modules.</p>
<div class="search"><label for="module-search">Filter modules by path or name</label><input id="module-search" type="search" placeholder="For example: Hermite or ConcreteTheoremOneNine" aria-controls="module-list"><p id="count" role="status">{len(files)} modules</p></div>
<div id="module-list">{''.join(sources)}</div></section></main>
<footer>Standalone HTML · embedded styles, sources, and diagrams · no network connection required</footer>
<script>
const modules = [...document.querySelectorAll('details.source')];
document.getElementById('module-search').addEventListener('input', event => {{
  const query = event.target.value.toLowerCase().trim();
  modules.forEach(module => module.hidden = !module.dataset.name.includes(query));
  document.getElementById('count').textContent = modules.filter(module => !module.hidden).length + ' of ' + modules.length + ' modules';
}});
function openLinkedModule() {{
  const target = document.getElementById(location.hash.slice(1));
  if (target && target.matches('details.source')) {{ target.hidden = false; target.open = true; target.scrollIntoView(); }}
}}
window.addEventListener('hashchange', openLinkedModule);
openLinkedModule();
</script></body></html>'''

output = ROOT / "documentation.html"
output.write_text(html)
print(f"Wrote {output} ({len(files)} modules; {output.stat().st_size:,} bytes)")
