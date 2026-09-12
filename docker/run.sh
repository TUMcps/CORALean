#!/bin/sh
# Build the image and start the container, or restart it if it already exists.
#
# A script rather than a compose file: glados carries docker-compose 1.29, which
# predates the spec, and there is nothing here that compose would express better.
#
# The container idles. Work happens in `docker exec`, so a build survives an SSH
# disconnect and an interrupted Claude Code session is reattached, not restarted.

set -eu

NAME=ladner-CORALean
IMAGE=ladner/coralean:latest
SRC=${CORALEAN_SRC:-$HOME/work/CORALean}
TOKEN=$HOME/.config/coralean/gl.token
STATE=$HOME/docker-state/$NAME

[ -d "$SRC" ] || { echo "no checkout at $SRC"; exit 1; }
mkdir -p "$STATE"

# `~/.claude.json` carries the login and is rewritten by atomic rename, which a
# single-file bind mount does not survive -- so it is carried across the
# replacement by hand rather than mounted. `~/.claude` is a volume and needs
# none of this.
if docker inspect "$NAME" >/dev/null 2>&1; then
  docker cp "$NAME:$HOME/.claude.json" "$STATE/claude.json" 2>/dev/null \
    && chmod 600 "$STATE/claude.json" \
    && echo "saved the login from the running container"
fi

docker build \
  --build-arg UID="$(id -u)" \
  --build-arg GID="$(id -g)" \
  --build-arg USERNAME="$(id -un)" \
  -t "$IMAGE" "$(dirname "$0")"

docker rm -f "$NAME" >/dev/null 2>&1 || true

# The token is mounted, never copied: `scripts/gl.py` reads it, and so does the
# git credential helper at push time, so the container holds no copy of its own.
[ -f "$TOKEN" ] && TOKEN_MOUNT="-v $TOKEN:$TOKEN:ro" || TOKEN_MOUNT=""

# shellcheck disable=SC2086 # TOKEN_MOUNT is two words or none, deliberately
docker run -d \
  --name "$NAME" \
  --hostname coralean \
  --restart unless-stopped \
  --init \
  -w /work/CORALean \
  -v "$SRC:/work/CORALean" \
  -v "${NAME}-claude:$HOME/.claude" \
  $TOKEN_MOUNT \
  -e "LEAN_NUM_THREADS=${LEAN_NUM_THREADS:-16}" \
  -e TERM=xterm-256color \
  --cpus "${CORALEAN_CPUS:-16}" \
  --memory "${CORALEAN_MEM:-64g}" \
  "$IMAGE" sleep infinity

if [ -s "$STATE/claude.json" ]; then
  docker cp "$STATE/claude.json" "$NAME:$HOME/.claude.json"
  docker exec -u 0 "$NAME" chown "$(id -u):$(id -g)" "$HOME/.claude.json"
  echo "restored the login -- no need to authenticate again"
fi

echo "$NAME is up. Next:"
echo "  docker exec -it $NAME claude       # log in once, then work"
echo "  docker exec -it $NAME tmux new -A -s work"
