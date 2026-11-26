#!/usr/bin/env python3
"""Build paperl.tex (LaTeX article, the style of Papers I/K) from DRAFT.md.

Pipeline: DRAFT.md --(strip draft-meta + changelog appendix)--> pandoc -t latex --> post-process
(heading levels/numbers, \\src citation links, Unicode -> math outside code, tables, verbatim) -->
paperl.tex --> xelatex twice.

The markdown stays the working source; paperl.tex is the typeset artifact of record.
"""
import re
import subprocess
import sys

SRC = 'DRAFT.md'
OUT = 'paperl.tex'
BODY = '/tmp/paperl_body.tex'
COMMIT = '3df056f596e5dffa15c22292055bbd4b6a9e4299'
REPO = 'https://github.com/jpbald93/paperl_clifford_chain'

PREAMBLE = r"""\documentclass[11pt]{article}
\usepackage[margin=1in]{geometry}
\usepackage{amsmath,amssymb,amsthm}
\usepackage{fontspec}
\setmainfont{Latin Modern Roman}
\setsansfont{Latin Modern Sans}
\setmonofont{DejaVu Sans Mono}[Scale=0.86]
\usepackage{xcolor}
\usepackage{booktabs}
\usepackage{array}
\usepackage{calc}
\usepackage{longtable}
\usepackage{seqsplit}
\usepackage{fancyvrb}
\usepackage{fvextra}
\fvset{breaklines=true,breakanywhere=true,fontsize=\small}
\usepackage[hidelinks]{hyperref}
\usepackage{url}

\providecommand{\textquotesingle}{'}
\providecommand{\textquotedbl}{"}
\providecommand{\tightlist}{\setlength{\itemsep}{0pt}\setlength{\parskip}{0pt}}

\newtheorem{theorem}{Theorem}
\newtheorem{lemma}[theorem]{Lemma}
\newtheorem{proposition}[theorem]{Proposition}
\theoremstyle{definition}
\newtheorem{definition}[theorem]{Definition}
\theoremstyle{remark}
\newtheorem{remark}[theorem]{Remark}

% A declaration of the development; the name/line gate (layer 11) resolves every File:line anchor
% against the pinned tree.
\DeclareUrlCommand\decl{\urlstyle{tt}\def\UrlBreaks{\do\_\do\.}}
\newcommand{\plcommit}{__COMMIT__}
\newcommand{\src}[2]{\href{__REPO__/blob/__COMMIT__/#1\#L#2}{\texttt{\seqsplit{#1}}:#2}}
\newcommand{\PH}[1]{\textcolor{red}{\textbf{[PLACEHOLDER:} #1\textbf{]}}}

\title{Clifford's chain for every $n$: point--circle configurations on the Riemann sphere, formalised in Lean~4}
\author{Josh Bald\\ \small Independent researcher, Ontario, Canada\\ \small\texttt{jpbald93@gmail.com}\\
\small ORCID: \texttt{0009-0002-1317-6489}
\thanks{\copyright~2026 Josh Bald. Licensed under CC BY 4.0
(\url{https://creativecommons.org/licenses/by/4.0/}). The accompanying Lean code is licensed under
the Apache License 2.0.}}
\date{26 November 2026}
\emergencystretch=3em
\begin{document}
\sloppy
\maketitle

"""

UNICODE = [
    ('ℂ', r'$\mathbb{C}$'), ('ℕ', r'$\mathbb{N}$'), ('ℝ', r'$\mathbb{R}$'),
    ('⇄', r'$\rightleftarrows$'), ('↔', r'$\leftrightarrow$'), ('⇒', r'$\Rightarrow$'),
    ('→', r'$\to$'), ('←', r'$\leftarrow$'), ('↑', r'$\uparrow$'),
    ('∀', r'$\forall$'), ('∃', r'$\exists$'), ('∧', r'$\land$'), ('∨', r'$\lor$'),
    ('∈', r'$\in$'), ('⊆', r'$\subseteq$'), ('≤', r'$\le$'), ('≥', r'$\ge$'),
    ('≠', r'$\ne$'), ('¬', r'$\neg$'), ('∘', r'$\circ$'), ('·', r'$\cdot$'),
    ('−', r'$-$'), ('×', r'$\times$'), ('∞', r'$\infty$'),
    ('⟨', r'$\langle$'), ('⟩', r'$\rangle$'), ('‖', r'$\|$'),
    ('√3', r'$\sqrt{3}$'), ('²', r'$^2$'), ('≈', r'$\approx$'),
    ('₀', r'$_0$'), ('₄', r'$_4$'), ('₅', r'$_5$'), ('₆', r'$_6$'),
    ('•', r'$\bullet$'), ('′', r"$'$"),
    ('—', '---'), ('–', '--'), ('…', r'\ldots{}'), ('§', r'\S{}'),
    ('ö', r'\"o'),
]


def strip_source(text):
    # drop the H1 (the title lives in \title)
    text = re.sub(r'\A# .*?\n', '', text, count=1)
    # drop the draft-provenance paragraph that opens the markdown
    text = re.sub(r'\n\*\*Draft v[0-9.]+ — [^*]*\*\*.*?\n\n', '\n', text, count=1, flags=re.S)
    # the abstract paragraph is emitted separately into \begin{abstract}
    m = re.search(r'\n(\*\*Abstract\.\*\* .*?)\n\n', text, flags=re.S)
    abstract = None
    if m:
        abstract = m.group(1).replace('**Abstract.** ', '')
        text = text.replace(m.group(0), '\n', 1)
    return text, abstract


def convert(text):
    body = subprocess.run(['pandoc', '-f', 'markdown', '-t', 'latex', '--wrap=preserve', '--no-highlight'],
                          input=text, capture_output=True, text=True, check=True).stdout
    # heading levels: # -> title (gone), ## -> section, ### -> subsection
    body = body.replace('\\subsubsection{', '\\PAPERLSUB{')
    body = body.replace('\\subsection{', '\\section{')
    body = body.replace('\\PAPERLSUB{', '\\subsection{')
    # strip hand-written numbering ("1. Introduction", "1.1 What ...")
    body = re.sub(r'\\(section|subsection)\{(\d+(?:\.\d+)?)[. ]+\s*', r'\\\1{', body)
    # appendices: unnumbered top heading per appendix, version headings unnumbered
    body = re.sub(r'\\section\{Appendix ([ABC]) (?:---|--)\s*(.*?)\}',
                  lambda m: '\\section*{Appendix ' + m.group(1) + ' --- ' + m.group(2) + '}', body)
    body = re.sub(r'\\subsection\{v0\.\d+', r'\\subsection*{v0.', body)
    # File:line citations -> linked \src
    body = re.sub(r'\\texttt\{((?:Clifford/[A-Za-z0-9]+\.lean|Clifford\.lean|gate\.sh)):(\d+)\}',
                  r'\\src{\1}{\2}', body)
    # 64-hex digests: breakable inside the mono column
    def chunk_hash(m):
        h = m.group(1)
        chunks = [h[i:i + 8] for i in range(0, len(h), 8)]
        return '\\texttt{' + '\\allowbreak '.join(chunks) + '}'
    body = re.sub(r'\\texttt\{([0-9a-f]{64})\}', chunk_hash, body)
    # the reference list is unnumbered, like the appendices
    body = body.replace('\\section{References}', '\\section*{References}')
    # markdown horizontal rules between sections are not part of the typeset paper
    body = body.replace('\\begin{center}\\rule{0.5\\linewidth}{0.5pt}\\end{center}\n', '')
    body = body.replace('\\textasciitilde{}', '\\textasciitilde')
    # verbatim -> fancyvrb, small and breakable
    body = body.replace('\\begin{verbatim}', '\\begin{Verbatim}')
    body = body.replace('\\end{verbatim}', '\\end{Verbatim}')
    # tables: smaller type (they are wide)
    body = body.replace('\\begin{longtable}', '{\\scriptsize\\begin{longtable}')
    body = body.replace('\\end{longtable}', '\\end{longtable}}')
    return body



def breakable_texttt(text):
    """Insert \\allowbreak inside \\texttt{...} at punctuation, so long identifiers wrap."""
    def repl(m):
        body = m.group(1)
        if '\\seqsplit' in body:
            return m.group(0)
        body = body.replace('\\_', '\\_\\allowbreak ').replace('.', '.\\allowbreak ')
        body = body.replace('/', '/\\allowbreak ').replace(':', '\\allowbreak :')
        return '\\texttt{' + body + '}'
    return re.sub(r'\\texttt\{([^{}]*)\}', repl, text)


def latexify_unicode(text):
    """Replace Unicode outside code (\\texttt{...}) and verbatim blocks."""
    parts = re.split(r'(\\begin\{Verbatim\}.*?\\end\{Verbatim\}|\\texttt\{[^{}]*\})', text, flags=re.S)
    out = []
    for part in parts:
        if part.startswith('\\begin{Verbatim}') or part.startswith('\\texttt{'):
            out.append(part)
            continue
        for ch, rep in UNICODE:
            part = part.replace(ch, rep)
        out.append(part)
    text = ''.join(out)
    # combining macron: X̄ -> \=X
    text = re.sub(r'([A-Za-z])\u0304', r'\\=\1', text)
    return text


def main():
    src = open(SRC, encoding='utf-8').read()
    text, abstract = strip_source(src)
    body = convert(text)
    body = latexify_unicode(body)
    body = breakable_texttt(body)

    def expand_src(m):
        f, ln = m.group(1), m.group(2)
        shown = f.replace('/', '/\\allowbreak ')
        return ('\\href{' + REPO + '/blob/' + COMMIT + '/' + f + '\\#L' + ln + '}'
                '{\\texttt{' + shown + '}:' + ln + '}')
    body = re.sub(r'\\src\{([^{}]+)\}\{(\d+)\}', expand_src, body)
    abstract_tex = ''
    if abstract:
        a = subprocess.run(['pandoc', '-f', 'markdown', '-t', 'latex', '--wrap=preserve'],
                           input=abstract, capture_output=True, text=True, check=True).stdout
        abstract_tex = latexify_unicode(a)
    head = PREAMBLE.replace('__COMMIT__', COMMIT).replace('__REPO__', REPO)
    with open(OUT, 'w', encoding='utf-8') as f:
        f.write(head)
        if abstract_tex:
            f.write('\\begin{abstract}\n' + abstract_tex.strip() + '\n\\end{abstract}\n\n')
        f.write(body)
        f.write('\n\\end{document}\n')
    print(f'wrote {OUT}')


if __name__ == '__main__':
    main()
