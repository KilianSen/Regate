# Grading protocol

The canonical, versioned spec is at the monorepo root: `../../GRADING_PROTOCOL.md`.

`grade.py` conforms to it (`backend = "leanregate"`). A copy is vendored into the
container image at build time so the container is self-contained.
