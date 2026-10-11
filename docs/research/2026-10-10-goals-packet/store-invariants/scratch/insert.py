import sys

probe, section_file, marker = sys.argv[1], sys.argv[2], sys.argv[3]
text = open(probe).read()
section = open(section_file).read()
if marker not in text:
    sys.exit("marker not found")
text = text.replace(marker, section + marker, 1)
open(probe, "w").write(text)
