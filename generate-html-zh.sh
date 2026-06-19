#!/usr/bin/env bash
set -euo pipefail

# Generate the Chinese reference manual with support for preview and production modes.

case "$(uname -s 2>/dev/null || true)" in
  MINGW*|MSYS*|CYGWIN*)
    export PATH="$(pwd)/scripts/windows-bin:/d/Program Files/Git/usr/bin:$PATH"
    ;;
esac

MODE="preview"
VERSION=""
OUTPUT="_out/site-zh"
DRAFT_FLAG=""

while [[ $# -gt 0 ]]; do
  case $1 in
    --mode)
      MODE="$2"
      shift 2
      ;;
    --version)
      VERSION="$2"
      shift 2
      ;;
    --output)
      OUTPUT="$2"
      shift 2
      ;;
    --draft)
      DRAFT_FLAG="--draft"
      shift
      ;;
    *)
      echo "Unknown option: $1"
      echo "Usage: $0 [--mode preview|production] [--version VERSION] [--output DIR] [--draft]"
      exit 1
      ;;
  esac
done

if [ "$MODE" = "production" ]; then
  if [ -z "$VERSION" ]; then
    echo "Error: --version required for production mode"
    exit 1
  fi
  if [ -n "$DRAFT_FLAG" ]; then
    echo "Error: --draft not supported in production mode"
    exit 1
  fi
fi

if [ "$MODE" = "preview" ]; then
  REF_REMOTE_CONFIG="test-data/reference-remotes.json"
else
  REF_REMOTE_CONFIG="_build/production-remotes-reference.json"
  mkdir -p _build
  sed "s/__VERSION__/$VERSION/g" config/production-remotes-reference.json.template > "$REF_REMOTE_CONFIG"
  echo "Generated production config with version $VERSION"
fi

if [ -n "$DRAFT_FLAG" ]; then
  MANUAL_OUTPUT_FLAG="--output _out/draft-zh"
  REF_SOURCE="_out/draft-zh/html-multi"
else
  MANUAL_OUTPUT_FLAG="--output _out/zh"
  REF_SOURCE="_out/zh/html-multi"
fi

echo "Running generate-manual-zh with args --depth 2 --verbose --delay-html-multi multi-zh.json --remote-config $REF_REMOTE_CONFIG --with-word-count words-zh.txt $MANUAL_OUTPUT_FLAG $DRAFT_FLAG"
lake --quiet exe generate-manual-zh --depth 2 --verbose --delay-html-multi multi-zh.json --remote-config "$REF_REMOTE_CONFIG" --with-word-count "words-zh.txt" $MANUAL_OUTPUT_FLAG $DRAFT_FLAG

echo "Running generate-manual-zh with args --verbose --resume-html-multi multi-zh.json --remote-config $REF_REMOTE_CONFIG $MANUAL_OUTPUT_FLAG $DRAFT_FLAG"
lake --quiet exe generate-manual-zh --verbose --resume-html-multi multi-zh.json --remote-config "$REF_REMOTE_CONFIG" $MANUAL_OUTPUT_FLAG $DRAFT_FLAG

mkdir -p "$OUTPUT"
cp -r "$REF_SOURCE"/* "$OUTPUT/"

echo "Done! Chinese manual generated at $OUTPUT/"
