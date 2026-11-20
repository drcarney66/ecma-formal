"""Unions the runs of reach.lean in this directory: dead.all.tsv (dead in every run that sees it), live.all.tsv,
and the files of lean/ no run imports."""
import glob, subprocess, collections, os
live=set()
for f in glob.glob("*.live.tsv"):
    if f.startswith(("dead.all","live.all")): continue
    live |= {l.rstrip("\n") for l in open(f) if l.strip()}
dead=set()
for f in glob.glob("*.dead.tsv"):
    if f.startswith(("dead.all","live.all")): continue
    dead |= {l.rstrip("\n") for l in open(f) if l.strip()}
dead -= live
mods=set()
for f in glob.glob("*.mods"): mods |= set(open(f).read().split())
files = subprocess.check_output("cd /Users/drcarney/src/ecma-formal && git ls-files lean | grep '\\.lean$'", shell=True, text=True).split()
unimp = [f for f in files if f[5:-5].replace("/", ".") not in mods
         and os.path.exists("/Users/drcarney/src/ecma-formal/" + f)]
print("live", len(live), "dead", len(dead), "unimported files", len(unimp)); print("\n".join(unimp[:40]))
print(collections.Counter(l.split("\t")[3] for l in dead))
print(collections.Counter(l.split("\t")[0] for l in dead).most_common(60))
open("dead.all.tsv","w").write("\n".join(sorted(dead))+"\n"); open("live.all.tsv","w").write("\n".join(sorted(live))+"\n")
