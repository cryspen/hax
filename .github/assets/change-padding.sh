#!/usr/bin/env bash
# set padding so that logos are centered when rendered by GH

set -euo pipefail
X="${1:?Usage: $0 <new Y value>}"

find . -type f -name '*.svg' -exec sd 'id="__topPaddingWrapper" transform="translate\(0, \d+\)"' "id=\"__topPaddingWrapper\" transform=\"translate(0, ${1})\"" {} +
