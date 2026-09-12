# CORALean in a container

A Lean toolchain and Claude Code on a build host, so `lake build` runs somewhere
other than a laptop and keeps running once the laptop is off. The container
idles; the work happens in `docker exec`.

## Setup

On the host, once:

```sh
git clone https://gitlab.lrz.de/cps/CORALean.git ~/work/CORALean
sh ~/work/CORALean/docker/run.sh
```

`run.sh` builds the image and starts the container. Most of the build is the
Lean toolchain, which is baked in so a fresh container does not re-download it.
Then fetch Mathlib's prebuilt oleans into the checkout -- once, and they stay
there across every image rebuild, because the checkout is a bind mount:

```sh
docker exec -it ladner-CORALean lake exe cache get
docker exec -it ladner-CORALean lake build
```

## Claude Code

```sh
docker exec -it ladner-CORALean claude --remote-control coralean-glados
```

The first run asks you to log in: it prints a URL to open in a browser on your
own machine and a code to paste back. Credentials land in the container's
`.claude` volume, so this is a one-off and outlives `run.sh` being run again.

`--remote-control` is what makes the laptop optional: the session registers
under your account and is drivable from claude.ai or from Claude Code on
another machine, so closing the lid steers it rather than stopping it.
`claude --teleport <session>` picks an existing session up from elsewhere.

Wrap it in tmux as well, so a dropped SSH connection leaves the session running
rather than killing the terminal it was attached to:

```sh
docker exec -it ladner-CORALean tmux new -A -s work
```

`Ctrl-b d` detaches, the same command reattaches. An interactive session stops
at the end of its turn waiting for input; for something that should grind on
unattended, start it headless instead:

```sh
docker exec -d ladner-CORALean tmux new -d -s build 'claude -p "<task>"'
```

## GitLab access

`~/.config/coralean/gl.token` is mounted read-only, which is where
`scripts/gl.py` looks. Put it there without it passing through a terminal or a
shell history:

```sh
ssh ladnert@glados.cps.cit.tum.de \
  'mkdir -p ~/.config/coralean && cat > ~/.config/coralean/gl.token \
   && chmod 600 ~/.config/coralean/gl.token' < ~/.config/coralean/gl.token
```

`git push` needs it too, and reads it at use time rather than keeping a second
copy:

```sh
git config --global credential.helper \
  '!f() { echo username=oauth2; echo "password=$(cat ~/.config/coralean/gl.token)"; }; f'
```

Run that on the host (for cloning) and once inside the container (for pushing).
The token is write-scoped and shared with the laptop, so revoking it revokes it
there too, and root on a shared machine can read the file.

## Rebuilding

Only needed when `lean-toolchain` moves or Claude Code should be updated:

```sh
sh ~/work/CORALean/docker/run.sh
```

It rebuilds the image and replaces the container. The checkout is a bind mount
and is untouched, Mathlib included, and the login is carried across, so neither
has to be redone.

Anything running inside the container does not survive, so detach or finish a
Claude Code session first.
