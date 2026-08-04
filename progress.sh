#!/usr/bin/env bash
# Show how far through the course you are.
#
#   ./progress.sh
#
# Counts the exercises in each chapter and how many still contain `sorry`,
# according to Lean itself (not a text search) -- so it's honest.

set -uo pipefail
cd "$(dirname "$0")"
export PATH="$HOME/.elan/bin:$PATH"

BOLD=$'\033[1m'; DIM=$'\033[2m'; GREEN=$'\033[32m'; YELLOW=$'\033[33m'
RED=$'\033[31m'; RESET=$'\033[0m'

echo "${DIM}building...${RESET}"
BUILD=$(lake build 2>&1)

total_ex=0
total_done=0
printf "\n%s%-28s %-14s %s%s\n" "$BOLD" "CHAPTER" "SOLVED" "" "$RESET"

for f in LearnLean/Ch*.lean; do
  base=$(basename "$f" .lean)
  # Exercises are marked "**N.M**" in their doc comments.
  n_ex=$(grep -c '\*\*[0-9]\+\.[0-9]\+\*\*' "$f")
  n_open=$(echo "$BUILD" | grep -c "$base.lean:.*declaration uses .sorry")
  n_done=$(( n_ex - n_open ))
  (( n_done < 0 )) && n_done=0

  total_ex=$(( total_ex + n_ex ))
  total_done=$(( total_done + n_done ))

  if   (( n_done == n_ex )); then color=$GREEN
  elif (( n_done > 0 ));     then color=$YELLOW
  else                            color=$DIM
  fi

  bar=""
  for ((i = 0; i < n_ex; i++)); do
    if (( i < n_done )); then bar+="█"; else bar+="░"; fi
  done

  printf "%-28s %s%2d/%-2d  %s%s\n" "$base" "$color" "$n_done" "$n_ex" "$bar" "$RESET"
done

# Anything that isn't a sorry-induced failure is a real mistake worth showing.
real_errors=$(echo "$BUILD" \
  | grep -E "^error: LearnLean" \
  | grep -vE "cannot evaluate code because|depends on the 'sorry' axiom" || true)

echo
printf "%stotal: %d/%d%s\n" "$BOLD" "$total_done" "$total_ex" "$RESET"

if [[ -n "$real_errors" ]]; then
  printf "\n%sreal errors (not just unsolved exercises):%s\n" "$RED" "$RESET"
  echo "$real_errors"
  exit 1
fi

if (( total_done == total_ex )); then
  printf "%sEverything solved. Go write something of your own.%s\n" "$GREEN" "$RESET"
fi
