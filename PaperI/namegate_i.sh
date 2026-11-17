#!/bin/bash
# Paper I name gate (layer 11). Thin wrapper: see namegate_i.py for the checks.
exec python3 "$(dirname "$0")/namegate_i.py" "$@"
