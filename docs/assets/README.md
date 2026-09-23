# Verification workflow asset

`veripy-workflow.png` is the verification workflow from the VeriPy manuscript.
It is Figure 2 in the current manuscript. The root README intentionally uses a
stable descriptive label instead of a paper figure number.

`veripy-workflow.pdf` is the standalone vector export, copied without changes
from the manuscript figure on September 14, 2026. It contains only the diagram,
not the manuscript. Its SHA-256 is
`4edddf612dad5a013535b919ae26f96aaebe3fe26982d9573737ee6b99eee57f`.

## Rebuild the README image

With Poppler installed, run from the repository root.

```sh
pdftoppm -singlefile -r 300 -png \
  docs/assets/veripy-workflow.pdf docs/assets/veripy-workflow
```

Viewing the image or regenerating it from the vector export does not require
the paper source, workshop template, bibliography or a LaTeX installation.
The diagram was authored in TikZ. The standalone PDF preserves its labels,
arrows, colors and embedded logos.

## Logo provenance

- Lean, Hypothesis, CrossHair and basedpyright logos were supplied by the project
  author, as was the human developer icon.
- The Python logo is the Python Software Foundation's official two-snakes
  [PNG asset](https://s3.dualstack.us-east-2.amazonaws.com/pythondotorg-assets/media/community/logos/python-logo-only.png).
- The Dafny badge is a custom dark blue wordmark on a yellow rectangle.
- The robot is drawn in TikZ. Logical OR separates human and agent proof authors.

Third-party names and logos identify their respective projects and are not
covered by VeriPy's software license. Diagram layout and custom vector elements
use the repository's [MIT license](../../LICENSE).

## VeriPy brand

`veripy-logo.png` preserves the approved, AI-generated logo.
`veripy-logo.svg` is a presentation wrapper around that original raster,
with a tighter viewport and white backing for light and dark surfaces.
It is not a vector tracing. The documentation favicon is the matching
icon-only image in `docs-site/public/favicon-transparent.png`.
