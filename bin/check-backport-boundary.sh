#!/usr/bin/env bash
# Reject changes to the SC proof kernel and basic-step API.
set -euo pipefail
cd "$(git rev-parse --show-toplevel)"
base=a234fb842ef8ab875647b7c83099b9dd47a716ba
git diff --exit-code "$base" -- \
  lisa-kernel/src/main/scala/lisa/kernel/proof \
  lisa-utils/src/main/scala/lisa/utils/prooflib/BasicStepTactic.scala \
  lisa-utils/src/main/scala/lisa/utils/prooflib/ProofTacticLib.scala \
  lisa-utils/src/main/scala/lisa/utils/prooflib/Exports.scala
for path in \
  lisa-kernel/src/main/scala/lisa/kernel/proof/Theorem.scala \
  lisa-kernel/src/main/scala/lisa/kernel/proof/Theory.scala \
  lisa-utils/src/main/scala/lisa/utils/prooflib/ProofCarrier.scala \
  lisa-utils/src/main/scala/lisa/utils/prooflib/BasicStep.scala \
  lisa-utils/src/main/scala/lisa/utils/kernel/LinearProof.scala; do
  if [[ -e "$path" ]]; then
    echo "Forbidden LCF module: $path" >&2
    exit 1
  fi
done
echo 'SC kernel and basic-step boundary preserved.'
