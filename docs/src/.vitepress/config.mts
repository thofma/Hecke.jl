import { defineConfig } from 'vitepress'
import { tabsMarkdownPlugin } from 'vitepress-plugin-tabs'
import mathjax3 from "markdown-it-mathjax3";
import footnote from "markdown-it-footnote";

// Placeholder for the base URL (replaced by DocumenterVitepress.jl)
const baseTemp = {
  base: 'REPLACE_ME_DOCUMENTER_VITEPRESS', // TODO: replace this in makedocs!
}

// https://vitepress.dev/reference/site-config
export default defineConfig({
  base: 'REPLACE_ME_DOCUMENTER_VITEPRESS', // TODO: replace this in makedocs!
  title: 'REPLACE_ME_DOCUMENTER_VITEPRESS',
  description: "Hecke - computational algebraic number theory",
  lastUpdated: true,
  cleanUrls: true,
  outDir: 'REPLACE_ME_DOCUMENTER_VITEPRESS', // This is required for MarkdownVitepress to work correctly...
  appearance: 'dark',
  ignoreDeadLinks: true,

  // -------------------------------------------------------------------------
  // Head Configuration
  // -------------------------------------------------------------------------
  head: [
    // 1. Fonts (Optimized: Preconnect + Single Request + Swap)
    ['link', { rel: 'preconnect', href: 'https://fonts.googleapis.com' }],
    ['link', { rel: 'preconnect', href: 'https://fonts.gstatic.com', crossorigin: '' }],
    ['link', {
      href: 'https://fonts.googleapis.com/css?family=Barlow:400,500,600,700|Space+Mono:regular,italic,700,700italic|Space+Grotesk:regular,italic,700,700italic&display=swap',
      rel: 'stylesheet'
    }],

    // 2. Favicons
    ['link', { rel: 'apple-touch-icon', sizes: '180x180', href: `${baseTemp.base}/assets/modular/apple-touch-icon.png` }],
    ['link', { rel: 'icon', type: 'image/png', sizes: '32x32', href: `${baseTemp.base}/assets/modular/favicon-32x32.png` }],
    ['link', { rel: 'icon', type: 'image/png', sizes: '16x16', href: `${baseTemp.base}/assets/modular/favicon-16x16.png` }],
    ['link', { rel: 'icon', href: `${baseTemp.base}/assets/modular/favicon.ico` }],

    // 3. Custom Scripts
    ['script', { src: '/versions.js' }],
    ['script', { src: `${baseTemp.base}warner.js` }],
    ['script', { src: `${baseTemp.base}siteinfo.js` }]
  ],

  // -------------------------------------------------------------------------
  // Markdown Configuration
  // -------------------------------------------------------------------------
  markdown: {
    math: true,
    config(md) {
      md.use(tabsMarkdownPlugin)
      md.use(mathjax3)
      md.use(footnote)
    },
    theme: {
      light: "github-light",
      dark: "github-dark"
    }
  },

  // -------------------------------------------------------------------------
  // Vite Build Configuration
  // -------------------------------------------------------------------------
  vite: {
    build: {
      assetsInlineLimit: 0, // so we can tell whether we have created inlined images or not, we don't let vite inline them
    },
    optimizeDeps: {
      exclude: [
        '@nolebase/vitepress-plugin-enhanced-readabilities/client',
        'vitepress',
        '@nolebase/ui',
      ],
    },
    ssr: {
      noExternal: [ // If there are other packages that need to be processed by Vite, you can add them here.
        '@nolebase/vitepress-plugin-enhanced-readabilities',
        '@nolebase/ui',
      ],
    },
  },

  // -------------------------------------------------------------------------
  // Theme Configuration
  // -------------------------------------------------------------------------
  themeConfig: {
    logo: '/assets/modular/Hecke_logo_modular2.png',
    editLink: 'REPLACE_ME_DOCUMENTER_VITEPRESS',
    socialLinks: [
      { icon: 'github', link: 'REPLACE_ME_DOCUMENTER_VITEPRESS' }
    ],

    search: {
      provider: 'local',
      options: { detailedView: true }
    },

    footer: {
      message: 'Made with <a href="https://luxdl.github.io/DocumenterVitepress.jl/dev/" target="_blank"><strong>DocumenterVitepress.jl</strong></a><br>',
      copyright: `© Copyright ${new Date().getUTCFullYear()}.`
    },

    nav: [
      { text: 'Home', link: '/' },
      { text: 'Manual', link: '/manual/' },
      { text: 'Tutorials', link: '/tutorials/' },
      { text: 'How-to Guides', link: '/howto/' },
      { component: 'VersionPicker' }
    ],

    sidebar: {
      '/manual/': [
        {
          text: 'Manual',
          collapsed: true,
          items: [
            { text: 'Introduction', link: '/manual/'},
            {
              text: 'Number Fields',
              collapsed: true,
              items: [
                { text: 'Introduction', link: '/manual/number_fields/intro'},
                { text: 'Number field operations', link: '/manual/number_fields/fields'},
                { text: 'Elements', link: '/manual/number_fields/elements'},
                { text: 'Complex embeddings', link: '/manual/number_fields/complex_embeddings'},
                { text: 'Class field theory', link: '/manual/number_fields/class_fields'},
                { text: 'Internals', link: '/manual/number_fields/internal'}
              ]
            },
            {
              text: 'Orders in Number Fields',
              collapsed: true,
              items: [
                { text: 'Introduction', link: '/manual/orders/introduction'},
                { text: 'Basics', link: '/manual/orders/orders'},
                { text: 'Elements', link: '/manual/orders/elements'},
                { text: 'Ideals', link: '/manual/orders/ideals'},
                { text: 'Fractional ideals', link: '/manual/orders/frac_ideals'},
              ]
            },
            {
              text: 'Quadratic and Hermitian Forms',
              collapsed: true,
              items: [
                { text: 'Introduction', link: '/manual/quad_forms/introduction'},
                { text: 'Basics', link: '/manual/quad_forms/basics'},
                { text: 'Lattices', link: '/manual/quad_forms/lattices'},
                { text: 'Integer lattices', link: '/manual/quad_forms/integer_lattices'},
                { text: 'Genera for hermitian lattices', link: '/manual/quad_forms/genusherm'},
                { text: 'Genera for integer lattices', link: '/manual/quad_forms/Zgenera'},
                { text: 'Discriminant groups', link: '/manual/quad_forms/discriminant_group'},
              ]
            },
            {
              text: 'Associative Algebras',
              collapsed: true,
              items: [
                { text: 'Introduction', link: '/manual/algebras/intro'},
                { text: 'Basics', link: '/manual/algebras/basics'},
                { text: 'Structure constant algebras', link: '/manual/algebras/structureconstant'},
                { text: 'Group algebras', link: '/manual/algebras/groupalgebras'},
                { text: 'Quaternion algebras', link: '/manual/algebras/quaternion'},
                { text: 'Ideals in algebras', link: '/manual/algebras/ideals'},
              ]
            },
            {
              text: 'Elliptic Curves',
              collapsed: true,
              items: [
                { text: 'Introduction', link: '/manual/elliptic_curves/intro'},
                { text: 'Basics', link: '/manual/elliptic_curves/basics'},
                { text: 'Finite fields', link: '/manual/elliptic_curves/finite_fields'},
                { text: 'Number fields', link: '/manual/elliptic_curves/number_fields'},
              ]
            },
            {
              text: 'Abelian Groups',
              collapsed: true,
              items: [
                { text: 'Introduction', link: '/manual/abelian/introduction'},
                { text: 'Elements', link: '/manual/abelian/elements'},
                { text: 'Operations', link: '/manual/abelian/structural'},
                { text: 'Morphisms', link: '/manual/abelian/maps'},
              ]
            },
            {
              text: 'Miscellaneous',
              collapsed: true,
              items: [
                { text: 'Elementary number theory', link: '/manual/misc/elementary'},
                { text: 'Factored elements', link: '/manual/misc/FacElem'},
                { text: 'Sparse linear algebra', link: '/manual/misc/sparse'},
                { text: 'Conjugacy of integer matrices', link: '/manual/misc/conjugacy'},
                { text: 'Multisets', link: '/manual/misc/mset'},
                { text: 'Pseudo-matrices', link: '/manual/misc/pmat'},
              ]
            },
          ]
        },
        {
          text: 'For Developers',
          collapsed: true,
          items: [
            { text: 'Introduction', link: '/manual/developer/'},
            { text: 'Tests', link: '/manual/developer/test'},
            { text: 'Documentation', link: '/manual/developer/documentation'},
          ]
        },
        { text: 'References', link: '/manual/references' }
      ],

      '/tutorials/': [
        {
          text: 'Tutorials',
          items: [
            { text: 'Introduction', link: '/tutorials/'},
            { text: 'Quaternion Algebras', link: '/tutorials/quaternion'},
          ]
        }
      ],

      '/howto/': [
        {
          text: 'How-to Guides',
          items: [
            { text: 'Introduction', link: '/howto/'},
            { text: 'Compute an order of a number field', link: '/howto/defineorder'},
            { text: 'Decompose a prime in the ring of integers', link: '/howto/decompose'},
            { text: 'Test if an ideal is principal', link: '/howto/pip'},
            { text: 'Construct a residue field', link: '/howto/resfield'},
            { text: 'Reduction of polynomials', link: '/howto/reduction'},
          ]
        }
      ],
    },
  }
})
