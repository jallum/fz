# FZ VS Code Syntax Support

This folder contains a minimal VS Code extension for FZ syntax highlighting.

What it does:

- associates `*.fz` files with the `fz` language id
- provides Elixir-style editor defaults
- supplies a TextMate grammar tuned to FZ keywords, atoms, numbers, strings, and punctuation

Local install:

```sh
cd vscode-fz
code --install-extension .
```

The grammar is intentionally lightweight. It is meant to give immediate syntax highlighting first, then grow with the language surface as FZ evolves.
