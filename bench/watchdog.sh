#!/bin/bash
# Kill any single process exceeding LIMIT_KB before it can OOM the machine.
# eggregate's saturation can run away (max_nodes is not actually enforced), and a
# runaway there took down a 12 GB box earlier.
LIMIT_KB=${LIMIT_KB:-8000000}
while pgrep -f "bench_v2.py" > /dev/null; do
  while read -r pid rss cmd; do
    [ "$rss" -gt "$LIMIT_KB" ] && { echo "$(date +%T) killing pid=$pid rss=$((rss/1024))MB : ${cmd:0:60}"; kill -9 "$pid"; }
  done < <(ps -eo pid,rss,args --no-headers --sort=-rss | head -5)
  sleep 5
done
