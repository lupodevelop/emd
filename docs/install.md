# emd

This archive contains the prebuilt CLI for the platform named in its filename.
No Rust installation is needed.

Run `./emd --help`, then `./emd run examples/hello.emd`.
In Windows PowerShell, use `.\emd.exe` instead.

Move the executable into a directory on your PATH to use it as `emd`.
Examples are in `examples/`, the manual in `docs/`, and the Neovim plugin in
`editors/nvim/`. The Studio needs Neovim 0.10 or later and `emd` on your PATH.

Check the archive against the release's `SHA256SUMS`. Use `emd --version`
to see its version. The source is at https://github.com/lupodevelop/emd.

MIT licensed; see LICENSE.
