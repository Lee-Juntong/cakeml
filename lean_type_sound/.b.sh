#!/bin/bash
# build module(s), show only errors and a count of sorry warnings
cd /workspace/request-project
lake build "$@" > /tmp/build.log 2>&1
st=$?
grep -E "error" -A8 /tmp/build.log | grep -v "^trace\|LEAN_PATH" | head -${LINES_MAX:-60}
echo "sorry-warnings: $(grep -c "declaration uses .sorry" /tmp/build.log)"
echo "EXIT $st"
exit 0
