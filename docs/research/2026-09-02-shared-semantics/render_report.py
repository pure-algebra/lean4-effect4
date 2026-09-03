from pathlib import Path
import re, html, sys
from reportlab.pdfgen import canvas
from reportlab.platypus import SimpleDocTemplate, Paragraph, Spacer, Table, TableStyle, PageBreak, KeepTogether
from reportlab.lib.styles import ParagraphStyle
from reportlab.lib import colors
from reportlab.pdfbase import pdfmetrics
from reportlab.pdfbase.ttfonts import TTFont
from reportlab.lib.enums import TA_LEFT

ROOT=Path('/Users/pooks/Dev/lean4-effect4')
SOURCE=Path(sys.argv[1])
OUT=Path(sys.argv[2])
FONTS=Path('/Users/pooks/.cache/codex-runtimes/codex-primary-runtime/dependencies/native/libreoffice-headless/libreoffice/LibreOfficeDev.app/Contents/Resources/fonts/truetype')
for face,file in [('Body','DejaVuSans.ttf'),('Body-Bold','DejaVuSans-Bold.ttf'),('Body-Oblique','DejaVuSans-Oblique.ttf'),('Mono','DejaVuSansMono.ttf')]:
 pdfmetrics.registerFont(TTFont(face,str(FONTS/file)))
pdfmetrics.registerFontFamily('Body',normal='Body',bold='Body-Bold',italic='Body-Oblique',boldItalic='Body-Bold')
INK=colors.HexColor('#132C3B'); TEAL=colors.HexColor('#137A7F'); GRAY=colors.HexColor('#52616B')
styles={
 'body':ParagraphStyle('body',fontName='Body',fontSize=9.3,leading=14,spaceAfter=7,textColor=INK),
 'title':ParagraphStyle('title',fontName='Body-Bold',fontSize=25,leading=31,spaceAfter=14,textColor=INK),
 'h2':ParagraphStyle('h2',fontName='Body-Bold',fontSize=16,leading=21,spaceBefore=15,spaceAfter=9,textColor=INK,keepWithNext=True),
 'h3':ParagraphStyle('h3',fontName='Body-Bold',fontSize=11,leading=16,spaceBefore=9,spaceAfter=6,textColor=TEAL,keepWithNext=True),
 'small':ParagraphStyle('small',fontName='Body',fontSize=7.8,leading=11,spaceAfter=5,textColor=GRAY),
 'table':ParagraphStyle('table',fontName='Body',fontSize=8.1,leading=11.5,spaceAfter=0,textColor=INK),
 'thead':ParagraphStyle('thead',fontName='Body-Bold',fontSize=8.1,leading=11.5,textColor=colors.white),
 'code':ParagraphStyle('code',fontName='Mono',fontSize=7.6,leading=11,spaceAfter=8,textColor=INK,backColor=colors.HexColor('#F0F5F6'),borderPadding=7),
 'bullet':ParagraphStyle('bullet',fontName='Body',fontSize=9.3,leading=14,leftIndent=12,firstLineIndent=-9,spaceAfter=5,textColor=INK)
}
def inline(s):
 s=html.escape(s,quote=False)
 s=re.sub(r'\[([^\]]+)\]\(([^)]+)\)',lambda m:'<link href="'+html.escape(html.unescape(m[2]),quote=True)+'" color="#137A7F">'+m[1]+'</link>',s)
 s=re.sub(r'`([^`]+)`',r'<font name="Mono" size="8">\1</font>',s)
 s=re.sub(r'\*\*([^*]+)\*\*',r'<b>\1</b>',s)
 s=re.sub(r'(?<!\*)\*([^*]+)\*(?!\*)',r'<i>\1</i>',s)
 return s

class Report(SimpleDocTemplate):
 def afterFlowable(self,f):
  if isinstance(f,Paragraph) and f.style.name=='h2':
   title=f.getPlainText(); key='s'+str(getattr(self,'sectionCount',0)); self.sectionCount=getattr(self,'sectionCount',0)+1
   self.canv.bookmarkPage(key);self.canv.addOutlineEntry(title,key,0)
   self.canv.bookmarkPage(re.sub(r'[^a-z0-9]+','-',title.lower()).strip('-'))

def footer(c,d):
 c.saveState(); w,h=d.pagesize
 c.setStrokeColor(colors.HexColor('#D4E0E4'));c.line(45,41,w-45,41)
 c.setFont('Body',7);c.setFillColor(GRAY)
 c.drawString(45,28,'EFFECT4 / WEB STANDARDS SEMANTICS   |   Research, 2 September 2026')
 c.drawRightString(w-45,28,str(d.page))
 if d.page>1:
  c.setFont('Body',7);c.drawString(45,h-29,'RESEARCH FINDINGS AND PROPOSED CONTRACTS')
 c.restoreState()

lines=SOURCE.read_text().splitlines(); story=[];i=0
while i<len(lines):
 line=lines[i].strip()
 if not line:i+=1;continue
 if line=='<!-- pagebreak -->':story.append(PageBreak());i+=1;continue
 if line.startswith('```'):
  block=[];i+=1
  while i<len(lines) and not lines[i].startswith('```'):
   block.append(lines[i]);i+=1
  story.append(Paragraph('<br/>'.join(html.escape(x).replace(' ','&#160;') for x in block),styles['code']));i+=1;continue
 if line.startswith('|'):
  rows=[]
  while i<len(lines) and lines[i].strip().startswith('|'):
   cells=[x.strip() for x in lines[i].strip().strip('|').split('|')]
   if not all(re.fullmatch(r'[: -]+',x) for x in cells):rows.append(cells)
   i+=1
  n=len(rows[0]);width=505
  if n==2: widths=[155,350]
  elif n==3:widths=[190,150,165]
  elif n==4:widths=[230,85,95,95]
  elif n==5:widths=[145,90,90,90,90]
  else:widths=[width/n]*n
  data=[[Paragraph(inline(x),styles['thead' if j==0 else 'table']) for x in row] for j,row in enumerate(rows)]
  table=Table(data,colWidths=widths,repeatRows=1,hAlign='LEFT')
  table.setStyle(TableStyle([('BACKGROUND',(0,0),(-1,0),INK),('ROWBACKGROUNDS',(0,1),(-1,-1),[colors.HexColor('#F0F5F6'),colors.white]),('VALIGN',(0,0),(-1,-1),'TOP'),('LEFTPADDING',(0,0),(-1,-1),8),('RIGHTPADDING',(0,0),(-1,-1),8),('TOPPADDING',(0,0),(-1,-1),7),('BOTTOMPADDING',(0,0),(-1,-1),7),('LINEBELOW',(0,-1),(-1,-1),.5,colors.HexColor('#D4E0E4'))]))
  story.extend([table,Spacer(1,10)]);continue
 if line.startswith('# '):story.append(Paragraph(inline(line[2:]),styles['title']));i+=1;continue
 if line.startswith('## '):story.append(Paragraph(inline(line[3:]),styles['h2']));i+=1;continue
 if line.startswith('### '):story.append(Paragraph(inline(line[4:]),styles['h3']));i+=1;continue
 if line.startswith('- '):story.append(Paragraph('• '+inline(line[2:]),styles['bullet']));i+=1;continue
 para=[line];i+=1
 while i<len(lines) and lines[i].strip() and not lines[i].startswith(('#','|','- ','```','<!--')):
  para.append(lines[i].strip());i+=1
 joined=' '.join(para)
 style='small' if joined.startswith(('Sources:','Local evidence:','Evidence:','Access note:')) else 'body'
 story.append(Paragraph(inline(joined),styles[style]))

OUT.parent.mkdir(parents=True,exist_ok=True)
doc=Report(str(OUT),pagesize=(595,842),rightMargin=45,leftMargin=45,topMargin=48,bottomMargin=56,title='Effect4 and Web Standards Semantics',author='Research for the Effect4 project',pageCompression=1)
doc.build(story,onFirstPage=footer,onLaterPages=footer)
print(OUT)
