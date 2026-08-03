#!/usr/bin/env bash
# Benchmark a submission.
#
#   1. Wipe stale ops.bin / score.json so a contestant cannot pre-seed them.
#   2. Run build_circuit (UNTRUSTED — runs contestant code in src/point_add)
#      under bubblewrap: read-only filesystem, no network, all capabilities
#      dropped, unprivileged uid, writable only in a throwaway scratch dir
#      (its cwd) where it emits ops.bin. Also run it in its own process group
#      and kill the whole group on exit so a forked child cannot survive and
#      tamper afterward. (Linux uses bubblewrap; macOS uses sandbox-exec; if
#      neither is available it falls back to an unconfined local-dev run.)
#   3. Verify ops.bin exists. If build_circuit exited early or crashed,
#      the file is missing and we fail closed.
#   4. Run eval_circuit (TRUSTED — never imports contestant code) which
#      re-simulates the op stream, validates correctness/reversibility/
#      phase, and writes the canonical score.json.
#
# All command-line arguments are forwarded to eval_circuit (e.g. --note ...).
set -euo pipefail

# shellcheck disable=SC1091
. "$HOME/.cargo/env" 2>/dev/null || true

pinned_rust_channel() {
  local channel=""
  if [[ -f rust-toolchain ]]; then
    channel="$(sed -n 's/^[[:space:]]*channel[[:space:]]*=[[:space:]]*"\([^"]*\)".*/\1/p' rust-toolchain | sed -n '1p')"
    if [[ -z "${channel}" ]]; then
      channel="$(sed -n '1s/^[[:space:]]*\([^[:space:]]*\)[[:space:]]*$/\1/p' rust-toolchain)"
    fi
  fi
  printf '%s\n' "${channel}"
}

installed_toolchain_for_channel() {
  local channel="$1"
  local line toolchain toolchains

  [[ -n "${channel}" ]] || return 1
  command -v rustup >/dev/null 2>&1 || return 1
  toolchains="$(rustup toolchain list 2>/dev/null || true)"

  while IFS= read -r line; do
    toolchain="${line%% *}"
    if [[ "${toolchain}" == "${channel}" || "${toolchain}" == "${channel}-"* ]]; then
      printf '%s\n' "${toolchain}"
      return 0
    fi
  done <<< "${toolchains}"

  return 1
}

require_offline_rust_toolchain() {
  if [[ -n "${RUSTUP_TOOLCHAIN:-}" ]] || ! command -v rustup >/dev/null 2>&1; then
    return 0
  fi

  local channel toolchain
  channel="$(pinned_rust_channel)"
  [[ -n "${channel}" ]] || return 0

  toolchain="$(installed_toolchain_for_channel "${channel}" || true)"
  if [[ -z "${toolchain}" ]]; then
    echo "!! pinned Rust toolchain '${channel}' is not installed; run ./setup.sh before offline benchmarking" >&2
    exit 1
  fi

  export RUSTUP_TOOLCHAIN="${toolchain}"
}

find_c_compiler() {
  if [[ -n "${CC:-}" ]] && command -v "${CC}" >/dev/null 2>&1; then
    command -v "${CC}"
    return 0
  fi

  local candidate
  for candidate in gcc cc clang; do
    if command -v "${candidate}" >/dev/null 2>&1; then
      command -v "${candidate}"
      return 0
    fi
  done

  return 1
}

compiler="$(find_c_compiler || true)"
if [[ -z "${compiler}" ]]; then
  echo "!! no C compiler/linker found; run ./setup.sh or install gcc/clang" >&2
  exit 1
fi
export CC="${compiler}"
require_offline_rust_toolchain

if ! command -v cargo >/dev/null 2>&1; then
  echo "!! cargo not found; run ./setup.sh before offline benchmarking" >&2
  exit 1
fi

export CARGO_NET_OFFLINE=true

# 1. Clean slate.
rm -f ops.bin score.json

# Make sure both binaries are present (cheap rebuild — no-op if up to date).
RUSTFLAGS="-C linker=${compiler}" cargo build --release --locked --offline --bin build_circuit --bin eval_circuit

build_circuit_bin="$(pwd)/target/release/build_circuit"

# 2. Run build_circuit (UNTRUSTED). Contestant code is compiled into this binary
#    and runs in-process, so at run time it has the binary's privileges. Confine
#    it: a read-only view of the whole filesystem, no network, all capabilities
#    dropped, dropped to an unprivileged uid, and writable ONLY in a throwaway
#    scratch dir that we make its working directory (no writable /tmp; TMPDIR
#    points at the scratch dir, so the scratch dir is the single writable path).
#    ops.bin is written there and copied out afterward. This stops contestant
#    code from overwriting score.json,
#    the trusted eval_circuit binary, or the repo sources, and from reaching the
#    network — none of which the process-group reap below covers at run time.
ops_scratch="$(cd "$(mktemp -d)" && pwd -P)"   # resolved real path (the macOS profile needs it)
chmod 1777 "${ops_scratch}"   # let the sandbox uid write without replacing runner-owned files

# Build the (possibly confined) invocation:
#   - Linux: bubblewrap (installed by setup.sh in the trusted sandbox).
#   - macOS: sandbox-exec (Seatbelt) with an equivalent read-only / no-network profile.
#   - neither available: unconfined fallback (local dev only; the platform always
#     scores in a sandbox, so this never applies to the official run).
bwrap_via_sudo=0
if command -v bwrap >/dev/null 2>&1; then
  # Blacksmith keeps /home/runner private from other users. Once bwrap drops to
  # uid 65534, executing the binary through its workspace path therefore fails
  # even though the file itself is executable. Stage a read-only copy in the
  # world-traversable scratch directory that is already mounted into the sandbox.
  sandbox_build_circuit_bin="${ops_scratch}/build_circuit"
  cp "${build_circuit_bin}" "${sandbox_build_circuit_bin}"
  chmod 0555 "${sandbox_build_circuit_bin}"

  # The sandbox runs this as a non-root user, and its bwrap carries Linux file
  # capabilities without setuid — which bwrap refuses when run non-root
  # ("Unexpected capabilities but not setuid, old file caps config?"). Get bwrap
  # to start unprivileged, in order of preference:
  #   - sudo: run bwrap as root (the sandbox is provisioned with sudo). bwrap
  #     then drops to uid 65534 with no caps for the actual run.
  #   - else setpriv --no-new-privs: makes the kernel ignore the file caps so
  #     bwrap takes the unprivileged user-namespace path (no sudo required).
  #   - else plain bwrap (setuid or no-caps installs).
  # Either way the run ends up read-only, no-network, unprivileged.
  bw=( bwrap )
  if [[ "$(id -u)" -ne 0 ]] && command -v sudo >/dev/null 2>&1 && sudo -n true >/dev/null 2>&1; then
    bw=( sudo -n bwrap )
    bwrap_via_sudo=1
  elif command -v setpriv >/dev/null 2>&1; then
    bw=( setpriv --no-new-privs bwrap )
  fi
  run_build=(
    "${bw[@]}"
      --ro-bind / / --dev /dev --ro-bind /proc /proc
      --bind "${ops_scratch}" "${ops_scratch}" --chdir "${ops_scratch}"
      --setenv TMPDIR "${ops_scratch}"
      --unshare-user --unshare-net --unshare-ipc --unshare-uts --unshare-cgroup
      --cap-drop ALL --new-session --die-with-parent
      --uid 65534 --gid 65534
      -- "${sandbox_build_circuit_bin}"
  )
elif [[ "$(uname -s)" == "Darwin" ]] && command -v sandbox-exec >/dev/null 2>&1; then
  # Read-only everywhere except the scratch dir (and /dev), and no network. TMPDIR
  # points at the scratch dir so any incidental temp writes stay inside it.
  macos_profile="(version 1)(allow default)(deny file-write*)(allow file-write* (subpath \"${ops_scratch}\"))(allow file-write* (subpath \"/dev\"))(deny network*)"
  run_build=(
    sandbox-exec -p "${macos_profile}"
      /bin/bash -c 'cd "$1" && export TMPDIR="$1" && exec "$2"' _ "${ops_scratch}" "${build_circuit_bin}"
  )
else
  echo "!! no sandbox available (bubblewrap/sandbox-exec); running build_circuit UNCONFINED (dev fallback)" >&2
  run_build=( bash -c 'cd "$1" && exec "$2"' _ "${ops_scratch}" "${build_circuit_bin}" )
fi

# Run it in its own process group, then nuke the group. `setsid` puts it in a
# fresh pgid; killing `-<pgid>` reaches every child including double-forked
# daemons. When bwrap ran via sudo (root + uid-65534 children), reap via sudo so
# we can signal them. We trap so we always reap and clean up the scratch dir.
cleanup_pgid=""
reap() {
  [[ -n "${cleanup_pgid}" ]] || return 0
  if [[ "${bwrap_via_sudo}" -eq 1 ]]; then
    sudo -n kill -KILL -"${cleanup_pgid}" 2>/dev/null || true
  else
    kill -KILL -"${cleanup_pgid}" 2>/dev/null || true
  fi
}
cleanup() {
  reap
  if [[ -n "${ops_scratch:-}" ]]; then
    rm -rf "${ops_scratch}" 2>/dev/null || true
  fi
}
trap cleanup EXIT

if command -v setsid >/dev/null 2>&1; then
  setsid "${run_build[@]}" &
  build_pid=$!
  cleanup_pgid="${build_pid}"
  set +e
  wait "${build_pid}"
  build_status=$?
  set -e
  reap
  cleanup_pgid=""
else
  # Fallback: bash job control puts the background pipeline in its own pgid.
  set -m
  "${run_build[@]}" &
  build_pid=$!
  cleanup_pgid="${build_pid}"
  set +e
  wait "${build_pid}"
  build_status=$?
  set -e
  reap
  cleanup_pgid=""
  set +m
fi

if [[ "${build_status}" -ne 0 ]]; then
  echo "!! build_circuit exited with status ${build_status}" >&2
  exit "${build_status}"
fi

# Copy the untrusted output out of the scratch dir into the repo for scoring.
if [[ -s "${ops_scratch}/ops.bin" ]]; then
  cp "${ops_scratch}/ops.bin" ./ops.bin
fi
rm -rf "${ops_scratch}"; ops_scratch=""

# 3. Verify ops.bin actually got produced.
if [[ ! -s ops.bin ]]; then
  echo "!! build_circuit did not produce ops.bin" >&2
  exit 1
fi

# 4. Trusted scoring stage (never imports contestant code).
./target/release/eval_circuit "$@"
