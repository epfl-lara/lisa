import os, re

base = r'C:\Users\Simon\LisaProject\lisa\tptp-pure-fol'
for d in sorted(os.listdir(base)):
    dp = os.path.join(base, d)
    if not os.path.isdir(dp): continue
    easy = med = hard = 0
    for f in sorted(os.listdir(dp)):
        if not f.endswith('.p'): continue
        fp = os.path.join(dp, f)
        r = s = None
        with open(fp, encoding='utf-8', errors='ignore') as fh:
            for _ in range(25):
                l = fh.readline()
                m = re.search(r'Rating\s*:\s*(\S+)', l)
                if m:
                    try: r = float(m.group(1))
                    except: pass
                m = re.search(r'Status\s*:\s*(\S+)', l)
                if m: s = m.group(1)
        if s == 'Theorem':
            if r is not None and r <= 0.25: easy += 1
            elif r is not None and r <= 0.5: med += 1
            else: hard += 1
    t = easy + med + hard
    if t > 0:
        print(f'{d:5}: easy={easy:4} med={med:4} hard={hard:3} total={t:4}')
