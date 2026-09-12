# CORALean on a build host: a Lean toolchain and Claude Code, nothing else.
#
# Mathlib is deliberately not in the image. `lake exe cache get` pulls prebuilt
# oleans into the mounted checkout on first run, which is faster than baking
# 7.6 GB of packages into a layer that any toolchain bump invalidates.

FROM debian:bookworm-slim

# mawk and findutils are what `scripts/check-conventions.sh` is written in,
# python3 is what `scripts/gl.py` needs, and tmux is what keeps a session alive
# across an SSH disconnect.
RUN apt-get update -qq && apt-get install -y -qq --no-install-recommends \
      ca-certificates curl git python3 mawk findutils \
      build-essential ripgrep tmux less procps \
 && rm -rf /var/lib/apt/lists/*

# Node 22 from NodeSource: Claude Code needs 18+, and bookworm ships 18.13.
RUN curl -fsSL https://deb.nodesource.com/setup_22.x | bash - \
 && apt-get install -y -qq --no-install-recommends nodejs \
 && rm -rf /var/lib/apt/lists/* \
 && npm install -g @anthropic-ai/claude-code

# Matched to the host account so the bind-mounted checkout is writable and
# files it creates are not owned by root.
ARG UID=1000
ARG GID=1000
ARG USERNAME=ladner
RUN groupadd -g "$GID" "$USERNAME" \
 && useradd -m -u "$UID" -g "$GID" -s /bin/bash "$USERNAME"

USER $USERNAME

# Created here so the volume mounted over it inherits this ownership: docker
# makes an absent mountpoint root-owned, and the user then cannot write its
# own credentials.
RUN mkdir -p /home/$USERNAME/.claude

ENV ELAN_HOME=/home/$USERNAME/.elan
ENV PATH=/home/$USERNAME/.elan/bin:$PATH

# The toolchain is baked in rather than left to first run: it is a 3 GB
# download, and it changes only when `lean-toolchain` does.
ARG LEAN_TOOLCHAIN=leanprover/lean4:v4.32.0
RUN curl -sSfL https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh \
      | sh -s -- -y --default-toolchain "$LEAN_TOOLCHAIN" \
 && lake --version

WORKDIR /work/CORALean
CMD ["sleep", "infinity"]
