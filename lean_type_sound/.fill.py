#!/usr/bin/env python3
"""Usage: fill.py FILE PATCH
PATCH contains blocks:
### PROOF name
<text replacing `sorry` after `theorem name ... :=`>
### BEFORE name
<text inserted before the HOL4 comment preceding theorem name>
"""
import sys, re
f, patch = sys.argv[1], sys.argv[2]
s = open(f, newline='').read()
crlf = '\r\n' in s
s = s.replace('\r\n', '\n')
blocks = re.split(r'^### ', open(patch).read(), flags=re.M)
for b in blocks:
    if not b.strip():
        continue
    head, _, body = b.partition('\n')
    kind, name = head.split()
    body = body.rstrip('\n')
    m = re.search(r'^theorem ' + re.escape(name) + r'\b', s, flags=re.M)
    if not m:
        print('NOT FOUND', name); sys.exit(1)
    if kind == 'PROOF':
        i = s.find(':= sorry', m.start())
        j = s.find('\ntheorem ', m.start() + 1)
        if i < 0 or (j >= 0 and i > j):
            print('NO SORRY', name); sys.exit(1)
        s = s[:i] + ':= ' + body + s[i + len(':= sorry'):]
    elif kind == 'BEFORE':
        k = s.rfind('/- HOL4', 0, m.start())
        prev = s.rfind('\ntheorem ', 0, m.start())
        prevend = s.rfind('-/', 0, m.start())
        if k < 0 or k < prev or s.find('-/', k) < 0 or s.find('-/', k) > m.start():
            k = m.start()
        s = s[:k] + body + '\n\n' + s[k:]
    elif kind == 'STMT':
        # replace whole theorem (from 'theorem name' to ':= sorry') by body
        i = s.find(':= sorry', m.start())
        s = s[:m.start()] + body + s[i + len(':= sorry'):]
    else:
        print('bad kind', kind); sys.exit(1)
if crlf:
    s = s.replace('\n', '\r\n')
open(f, 'w', newline='').write(s)
print('ok')
