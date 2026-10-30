#!/usr/bin/env python3
"""Render the statement and verification guide (ReportLab, macOS Arial fonts)."""
from pathlib import Path

from reportlab.lib import colors
from reportlab.lib.enums import TA_CENTER
from reportlab.lib.styles import ParagraphStyle, getSampleStyleSheet
from reportlab.lib.units import mm
from reportlab.pdfbase import pdfmetrics
from reportlab.pdfbase.ttfonts import TTFont
from reportlab.platypus import SimpleDocTemplate, Paragraph, PageBreak

ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / 'PDF/effective-freeness-guide.pdf'
OUT.parent.mkdir(exist_ok=True)
fonts = Path('/System/Library/Fonts/Supplemental')
for name, file in [('Guide', 'Arial.ttf'), ('GuideMath', 'Arial Unicode.ttf'),
                   ('GuideBold', 'Arial Bold.ttf')]:
    pdfmetrics.registerFont(TTFont(name, str(fonts / file)))
pdfmetrics.registerFontFamily('Guide', normal='Guide', bold='GuideBold',
                             italic='Guide', boldItalic='GuideBold')
ink, teal, muted = [colors.HexColor(c) for c in ['#183239', '#176b60', '#53666a']]
styles = getSampleStyleSheet()
styles.add(ParagraphStyle(name='TitleCustom', fontName='GuideBold', fontSize=24,
                         leading=30, textColor=ink, spaceAfter=10))
styles.add(ParagraphStyle(name='LeadCustom', fontName='Guide', fontSize=10.5,
                         leading=15.5, textColor=muted, spaceAfter=13))
styles.add(ParagraphStyle(name='HeadingCustom', fontName='GuideBold', fontSize=12,
                         leading=17, textColor=teal, spaceBefore=14, spaceAfter=7))
styles.add(ParagraphStyle(name='BodyCustom', fontName='Guide', fontSize=10,
                         leading=15, textColor=ink, spaceAfter=8))
styles.add(ParagraphStyle(name='SmallCustom', fontName='Guide', fontSize=8.5,
                         leading=12.5, textColor=muted, spaceAfter=5))
styles.add(ParagraphStyle(name='MathCustom', fontName='GuideMath', fontSize=14,
                         leading=23, textColor=ink, alignment=TA_CENTER,
                         spaceBefore=9, spaceAfter=12))


def p(text, style='BodyCustom'):
    return Paragraph(text, styles[style])


def footer(canvas, doc):
    canvas.saveState()
    canvas.setStrokeColor(colors.HexColor('#d5dfdb'))
    canvas.line(20*mm, 17*mm, 190*mm, 17*mm)
    canvas.setFont('Guide', 8)
    canvas.setFillColor(muted)
    canvas.drawString(20*mm, 12*mm, 'Effective freeness | Local package | 23 October 2026')
    canvas.drawRightString(190*mm, 12*mm, str(doc.page))
    canvas.restoreState()


story = [p('Effective base point freeness<br/>and its numerical variant', 'TitleCustom'),
         p('Statements, scope and verification guide', 'LeadCustom'),
         p('1. Common hypotheses', 'HeadingCustom'),
         p('Let (X, Δ) be a normal complex projective klt pair of dimension n, with an effective rational boundary. Let D be nef Cartier and a &ge; 1 an integer. Assume aD − (K<sub>X</sub> + Δ) is nef and big.'),
         p('2. The historical parent', 'HeadingCustom'),
         p('Kollár (1993), p.596, predicts the following linear coefficient after Theorem 1.1:'),
         p('(a + n + 1)D is globally generated.', 'MathCustom'),
         p('<b>Restriction.</b> The package proves the complex projective case with integer a &ge; 1. The original setting allows a &ge; 0, proper varieties and characteristic-zero fields. The full original range is not claimed.'),
         p('3. The numerical variant (F2)', 'HeadingCustom'),
         p('For an ample Cartier divisor J, put ν(D) = max {k : 0 &le; k &le; n and D<sup>k</sup>·J<sup>n−k</sup> &gt; 0}. F2 asks for:'),
         p('mD is globally generated for every m &ge; a + ν(D) + 1;<br/>ν(D) = 0 implies D ∼ 0.', 'MathCustom'),
         p('<b>Variant implies parent.</b> Since ν(D) &le; n, take m = a + n + 1. FCSolution.lean proves this implication. There is no Iitaka-dimension or nonvanishing input.'),
         p('The numerical bound, all-multiples conclusion and numerical-zero conclusion are this project’s variant. The complete F2 formula is not attributed verbatim to Kollár or OpenAI.', 'SmallCustom'),
         p('Source: J. Kollár, Effective base point freeness, Math. Ann. 296 (1993), 595–605, p.596. DOI: 10.1007/BF01445123.', 'SmallCustom'),
         PageBreak(),
         p('Proof and verification', 'TitleCustom'),
         p('Library-backed proofs and a separate proposed FC statement', 'LeadCustom'),
         p('4. Proof route', 'HeadingCustom'),
         p('<b>Nonvanishing.</b> The adjoint klt hypotheses supply an initial section. The numerical-zero argument uses exceptional twists and Euler polynomials; the positive-dimensional argument uses isolation and vanishing.'),
         p('<b>Freeness and dimension.</b> Qualitative base-point freeness supplies semiampleness, and the proof derives κ(D) = ν(D). It then applies the effective exponent bound. These facts are proved internally rather than added to the theorem hypotheses.'),
         p('<b>Main specialization.</b> The ν(D) &le; n lemma gives the historical linear coefficient. The numerical theorem also includes dimension zero and the principal-divisor conclusion.'),
         p('5. Entries and local checks', 'HeadingCustom'),
         p('<b>Main:</b> EffectiveFreenessPublication.kollar<br/><b>Variant:</b> EffectiveFreenessPublication.variants.numerical'),
         p('The two proof directories contain 2,871 identical shared Lean sources. Lean is pinned to v4.35.0-rc3 and Mathlib is fixed by the dependency lock. Both target axiom audits report only propext, Classical.choice and Quot.sound.'),
         p('The current Comparator replay, source hashes, export hashes and sandbox setting are recorded in verification/. The macOS command explicitly disables the Linux-only sandbox. An older combined F1/F2 result is not transferred to these new declarations.'),
         p('6. Scope of the FC draft', 'HeadingCustom'),
         p('FClikelean/EffectiveFreeness.lean is one 165-line problem file with seven definitions, no variable declarations, one instance and two statement holes. It imports only FormalConjecturesUtil.'),
         p('<b>Remaining connection.</b> The FC file uses local Cartier equations and differential lattices. The proof library uses sheaves and intersection theory. A Lean dictionary between these representations remains to be supplied; no formal_proof link is claimed.'),
         p('<b>Header audit.</b> The Mathlib-only body and the official FC audit with its standard header pass. The retained short header fails FC’s strict copyright linter. No linter is disabled.'),
         p('This is a statement and verification guide, not a full proof paper. No CI, push, publication or independent mathematical peer review is claimed.', 'SmallCustom'),
         p('Developed by Kenta Kitamura with assistance from ChatGPT and OpenAI Codex. Project code is Apache-2.0; vendored libraries retain their licenses, including MIT for SGA.', 'SmallCustom')]
doc = SimpleDocTemplate(str(OUT), pagesize=(210*mm, 297*mm), leftMargin=20*mm,
                        rightMargin=20*mm, topMargin=20*mm, bottomMargin=24*mm,
                        title='Effective base point freeness and its numerical variant',
                        author='Kenta Kitamura')
doc.build(story, onFirstPage=footer, onLaterPages=footer)
print(OUT)
