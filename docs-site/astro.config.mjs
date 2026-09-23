import { defineConfig } from 'astro/config';
import starlight from '@astrojs/starlight';
export default defineConfig({
  site: 'https://astrio-labs.github.io',
  base: '/veripy',
  trailingSlash: 'always',
  integrations: [starlight({
    title: 'VeriPy',
    logo: { src: '../docs/assets/veripy-logo.svg', alt: '', replacesTitle: true },
    favicon: '/favicon-transparent.png',
    description: 'A practical guide to verifying Python components and checking compatibility.',
    social: [{ icon: 'github', label: 'GitHub', href: 'https://github.com/astrio-labs/veripy' }],
    customCss: ['./src/styles/custom.css'],
    sidebar: [
      { label: 'Start here', items: [
        { label: 'What is VeriPy?', slug: 'index' },
        { label: 'Installation', slug: 'guide/installation' },
        { label: 'Your first proof', slug: 'guide/first-proof' },
        { label: 'Understanding results', slug: 'guide/results' },
      ]},
      { label: 'Language guide', items: [
        { label: 'Contracts and values', slug: 'guide/contracts' },
        { label: 'Loops and invariants', slug: 'guide/loops' },
        { label: 'Proof support', slug: 'guide/proof-support' },
        { label: 'Python boundaries', slug: 'guide/boundaries' },
      ]},
      { label: 'Working with VeriPy', items: [
        { label: 'Compare two versions', slug: 'guide/compatibility' },
        { label: 'Dafny backend', slug: 'reference/dafny' },
        { label: 'Lean backend', slug: 'reference/lean' },
        { label: 'Agents and API', slug: 'reference/agent-interface' },
        { label: 'Editor integration', slug: 'reference/editor' },
      ]},
      { label: 'Reference', collapsed: true, items: [
        { label: 'Annotation grammar', slug: 'reference/spec-grammar' },
        { label: 'Supported fragments', slug: 'reference/supported-fragments' },
        { label: 'Python semantics', slug: 'reference/semantics' },
        { label: 'Compatibility contracts', slug: 'reference/callable-compatibility' },
        { label: 'Architecture', slug: 'reference/architecture' },
        { label: 'Trust and guarantees', slug: 'reference/assurance-argument' },
        { label: 'Repository layout', slug: 'reference/repository-layout' },
        { label: 'Output conventions', slug: 'reference/output-layout' },
      ]},
      { label: 'Research', collapsed: true, items: [
        { label: 'Case studies', slug: 'guide/case-studies' },
        { label: 'Evaluation', slug: 'reference/evaluation' },
        { label: 'Archives', slug: 'reference/research-archives' },
        { label: 'Replay', slug: 'reference/research-replay' },
        { label: 'Roadmap', slug: 'reference/roadmap' },
      ]},
    ],
  })],
});
