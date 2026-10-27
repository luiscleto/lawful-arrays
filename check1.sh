#!/bin/sh
# usage: ./check1.sh file.bend  (quick check of one file)
timeout 1800 env BEND_NO_TELEMETRY=1 nice -n 19 bend "$1" --check-only 2>&1 | head -${2:-40}
