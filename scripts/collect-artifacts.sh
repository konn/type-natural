#!/usr/bin/env bash
set -euo pipefail
DEST="$(pwd)/${1}"

echo "[*] Create directory tree"
TESTS="${DEST}"/tests
EXES="${DEST}"/exes
BENCHS="${DEST}"/benchs
set -x
mkdir -p "${TESTS}" "${BENCHS}" "${EXES}"
set +x

echo "[*] Setting-up cabal-plan"
if command -v cabal-plan; then
  echo "cabal-plan found."
  CABAL_PLAN="$(command -v cabal-plan)"
else
  echo "No cabal-plan found."
  set -x
  case "$(uname)" in
    Darwin) 
      CABAL_PLAN_URL=https://github.com/konn/cabal-plan/releases/download/v0.7.2.3/cabal-plan-0.7.2.3-macOS-x86_64.xz
    ;;
    *) 
      CABAL_PLAN_URL=https://github.com/haskell-hvr/cabal-plan/releases/download/v0.6.2.0/cabal-plan-0.6.2.0-x86_64-linux.xz
    ;;
  esac
  
  wget "${CABAL_PLAN_URL}" -O cabal-plan.xz

  xz -d <./cabal-plan.xz >cabal-plan
  chmod +x cabal-plan
  set +x
  CABAL_PLAN="$(pwd)/cabal-plan"
fi

echo "[*] Places artifacts into the correct place"

set -x
${CABAL_PLAN} list-bins | grep -v tasty | while read -r TARG; do
  COMPONENT=$(echo "${TARG}" | awk '{ print $1 }')
  BIN=$(echo "${TARG}" | awk '{ print $2 }')
  TYPE=$(echo "${COMPONENT}" | cut -d':' -f2)
  echo "---"
  echo "- Comp: ${COMPONENT}"
  echo "- Path: ${BIN}"
  echo "- TYPE: ${TYPE}"
  case "${TYPE}" in
    exe)
      COPY_DEST=${EXES}
    ;;
    test) 
      COPY_DEST=${TESTS}
    ;;
    *) 
      COPY_DEST=${BENCHS}
    ;;
  esac
  echo "Copying to ${COPY_DEST}"
  cp "${BIN}" "${COPY_DEST}/"
done

tar --use-compress-program="zstdmt -8" -caf "${DEST}.tar.zst" "./${1}"
