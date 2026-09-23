# VeriPy documentation website

Starlight publishes to https://astrio-labs.github.io/veripy/.
Use Node 22.12 or newer and Python 3.11 or newer.

```sh
cd docs-site
npm ci
npm run dev
```

`npm run build` generates the site, its search index, and checks every rendered
local link, asset and anchor. `npm run preview` serves the built output.

## Editing

Edit `docs/guide/*.md` for tutorials or the existing `docs/*.md` reference guides.
Do not edit generated `src/content/docs/` pages. `scripts/prepare.py` adds page
metadata and translates repository links to site routes or GitHub links.
Run preparation again after editing Markdown while the dev server is running.
Navigation and appearance live in `astro.config.mjs` and `src/styles/custom.css`.

Executable tutorial blocks are validated by `scripts/check_examples.py` against
Dafny and Lean. Run it from the repository root with the Python development
environment and both provers installed. It uses temporary directories and checks
both successful and deliberately invalid implementations.

## Publishing

The documentation workflow builds and checks pull requests. Pushes to `main`
build and deploy through GitHub Pages. In repository Settings, Pages, select
GitHub Actions as the publishing source. The deployment uses the `github-pages`
environment and does not need a separate organization website repository.

Generated content, site output and dependencies are ignored by Git. The Python
package does not depend on Node or the documentation framework.
