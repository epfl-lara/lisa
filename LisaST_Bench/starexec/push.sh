#!/usr/bin/env bash
#
# Drive StarExec from the command line, via the official StarExecCommand client.
#
#   ./push.sh solver [archive.tgz]       upload a solver package (default lisaST.tgz)
#   ./push.sh bench <archive.tgz>        upload a benchmark archive as a subspace
#   ./push.sh job <qid> <w> <cpu> <mem>  create a job over the space (seconds, seconds, GB)
#
# `mem` differs by experiment and is not a safety margin — the run scripts size their heaps from it:
#
#   e1a, e1b   mem=128 cpu=1500   eight workers in parallel, each pinned to a core and wanting 12 GiB. The
#                                 arithmetic is exact: 128 GiB / 8 = 16 GiB per worker, of which the run script
#                                 gives 12 GiB to the heap and leaves 4 GiB for everything a JVM reserves
#                                 outside it. That 4 GiB is where the safety lives, and it is what fixed the
#                                 "could not allocate compressed class space" death recorded in build.sh.
#                                 128 is also CASC's own cap on a solver, so the runs sit inside the
#                                 competition's limit. Jobs 7435, 7437, 7442, 7443 and 7446 used mem=160,
#                                 which produces identical runs: the per-worker heap cap of 12 GiB binds
#                                 either way, and the extra 32 GiB of address space was never asked for.
#                                 The CPU limit must cover eight cores for the wall clock: 8 x 180 s, plus a
#                                 little. It is a backstop, not the bound; the wall clock is the bound.
#   everything else  mem=16 cpu=200    single-threaded and pinned to one core, leaving a 12 GiB heap — the
#                                 same allowance one portfolio worker gets, which is what makes them
#                                 comparable. Because the run is pinned, its CPU time is its wall clock, so a
#                                 CPU limit just above the 180 s wall clock is a real 180 s CPU bound rather
#                                 than a trap: unpinned, the JVM's GC and JIT threads charge CPU to the other
#                                 seven cores and 180 s of CPU arrives at 167 s of wall clock. If a node ever
#                                 reports `pinning=no` in `starexec-node.txt`, raise this and say so, because
#                                 the runs from that node are not CPU-bounded the way the others are.
#   ./push.sh fetch <jobid> [dir]        download a job's info CSV and output archive
#   ./push.sh queue <id>                 show a queue (ids come from the Cluster page)
#   ./push.sh solvers                    list the solvers in the space
#   ./push.sh configs <solverid>         list a solver's configurations
#   ./push.sh shell                      an interactive StarExecCommand session, already logged in
#
# Credentials are read from the environment and never stored or passed on a command line that ends up in
# shell history:
#
#   export STAREXEC_USER=you@example.com
#   read -rs STAREXEC_PASS && export STAREXEC_PASS      # typed, not echoed
#
# SPACE defaults to the personal space id; ADDR to the Miami instance, which is not StarExecCommand's own
# default (it targets www.starexec.org unless `addr` says otherwise, and `addr` must name the home page and
# end in a slash).

set -uo pipefail

here="$(cd "$(dirname "$0")" && pwd)"
jar="$here/sec/StarexecCommand.jar"
addr="${ADDR:-https://starexec.acorn.miami.edu/starexec/}"
space="${SPACE:-28487}"

[ -f "$jar" ] || { echo "missing $jar — download starexeccommand.zip and unpack it into sec/" >&2; exit 2; }
# The client is a jar, so this needs a JDK; `env.sh` finds the one under $HOME/tools.
command -v java >/dev/null 2>&1 || . "$here/../env.sh" >/dev/null
command -v java >/dev/null 2>&1 || { echo "no java on PATH, and ../env.sh did not provide one" >&2; exit 2; }
: "${STAREXEC_USER:?set STAREXEC_USER}"
: "${STAREXEC_PASS:?set STAREXEC_PASS}"

# Commands are fed on stdin so the password never appears in an argument list.
# `-cp … dependencies/*` rather than `java -jar`: the client's manifest names each dependency individually and
# the distributed zip omits slf4j altogether, so `-jar` dies with NoClassDefFoundError before doing anything.
# The wildcard also picks up the jars added to `sec/dependencies/` to fill that gap.
# Under Git Bash the JVM is a Windows one: it cannot read a `/c/…` path and its classpath separator is `;`,
# not `:`. `cygpath` is what translates, and its absence is the test for being on a real Unix. `-m` keeps
# forward slashes (`C:/…`), which both Java and the client's own argument parser take; `-w` backslashes would
# be eaten as escapes on the way through.
if command -v cygpath >/dev/null 2>&1; then
  cp="$(cygpath -m "$here/sec/StarexecCommand.jar");$(cygpath -m "$here/sec/dependencies")/*"
  winpath() { cygpath -m "$1"; }
else
  cp="$here/sec/StarexecCommand.jar:$here/sec/dependencies/*"
  winpath() { printf '%s' "$1"; }
fi
run() { printf 'login u=%s p=%s addr=%s\nreturnids\n%s\nlogout\n' "$STAREXEC_USER" "$STAREXEC_PASS" "$addr" "$1" | java -cp "$cp" org.starexec.command.Shell; }

case "${1:-}" in
  solver)
    # An explicit archive so a dry-run package (a subset of the configurations) can go up beside the full one.
    archive="${2:-$here/lisaST.tgz}"
    [ -f "$archive" ] || { echo "no such archive: $archive" >&2; exit 2; }
    run "pushsolver id=$space f=$(winpath "$archive") n=LisaST-$(date +%Y%m%d-%H%M) d=LisaST superposition prover downloadable=" ;;
  bench)
    archive="${2:?usage: push.sh bench <archive.tgz>}"
    # bt=0 is "no type": the TPTP benchmark type validates `include('Axioms/…')` against the community's axiom
    # space and rejects problems whose axioms are not there, which ours resolve from inside the solver instead.
    # hier= keeps the archive's directory as a subspace.
    run "pushbenchmarks id=$space f=$(winpath "$archive") bt=0 hier= downloadable=" ;;
  job)
    qid="${2:?usage: push.sh job <qid> <wallclock_s> <cpu_s> <mem_gb>}"
    w="${3:-180}"; cpu="${4:-1440}"; mem="${5:-12}"
    # `cpu` deliberately far above `w`: the JVM's GC and JIT threads accrue CPU in parallel with the search, so
    # a CPU limit equal to the wall clock kills a run early (180 s of CPU arrived at 167 s of wall clock), and
    # CASC imposes no CPU limit at all.
    run "createjob id=$space qid=$qid n=lisast-$(date +%H%M) w=$w cpu=$cpu mem=$mem" ;;
  fetch)
    # Both halves of a job's results: the info CSV (one row per pair: status, CPU, wall clock, SZS) and the
    # output archive (each pair's stdout and its preserved output directory, which is where `result.csv` is).
    id="${2:?usage: push.sh fetch <jobid> [destdir]}"
    dest="${3:-$here/../results}"
    mkdir -p "$dest"
    run "getjobinfo id=$id out=$(winpath "$dest/Job${id}_info.zip") ow=
getjobout id=$id out=$(winpath "$dest/Job${id}_output.zip") ow=" ;;
  queue)
    # There is no list-all-queues command; only this one, by id. Ids come from the Cluster page, which shows
    # `id = N` beside a queue's name. `all.q` is 1, and it has no nodes — the work runs on `public.q`.
    run "viewqueue id=${2:?usage: push.sh queue <id>}" ;;
  solvers)
    run "lssolvers id=$space" ;;
  configs)
    run "lsconfigs id=${2:?usage: push.sh configs <solverid>}" ;;
  shell)
    # The rest of the session comes from `/dev/tty`, not `/dev/stdin`: stdin here is the pipe carrying the
    # login line, so reading it again just hits the end of that pipe and the shell exits at once.
    { printf 'login u=%s p=%s addr=%s\n' "$STAREXEC_USER" "$STAREXEC_PASS" "$addr"; cat /dev/tty; } | java -cp "$cp" org.starexec.command.Shell ;;
  *)
    sed -n '3,12p' "$0"; exit 2 ;;
esac
