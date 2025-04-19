import{_ as s,c as n,o as a,a6 as e}from"./chunks/framework.BpDNY18y.js";const k=JSON.parse('{"title":"Testing","description":"","frontmatter":{},"headers":[],"relativePath":"manual/developer/test.md","filePath":"manual/developer/test.md","lastUpdated":null}'),t={name:"manual/developer/test.md"},i=e(`<h1 id="Testing" tabindex="-1">Testing <a class="header-anchor" href="#Testing" aria-label="Permalink to &quot;Testing {#Testing}&quot;">​</a></h1><h2 id="Structure" tabindex="-1">Structure <a class="header-anchor" href="#Structure" aria-label="Permalink to &quot;Structure {#Structure}&quot;">​</a></h2><p>The Hecke tests can be found in <code>Hecke/test/</code> and are organized in such a way that the file hierarchy mirrors the source directory <code>Hecke/src/</code>. For example, here is a subset of the <code>src/QuadForm</code> and the <code>test/QuadForm</code> directories:</p><div class="language- vp-adaptive-theme"><button title="Copy Code" class="copy"></button><span class="lang"></span><pre class="shiki shiki-themes github-light github-dark vp-code" tabindex="0"><code><span class="line"><span>├── src</span></span>
<span class="line"><span>│   ├── QuadForm</span></span>
<span class="line"><span>│   │   ├── Enumeration.jl</span></span>
<span class="line"><span>│   │   ├── Herm</span></span>
<span class="line"><span>│   │   │   ├── Genus.jl</span></span>
<span class="line"><span>│   │   ├── Quad</span></span>
<span class="line"><span>│   │   │   ├── Genus.jl</span></span>
<span class="line"><span>│   │   │   ├── GenusRep.jl</span></span>
<span class="line"><span>│   │   │   ├── NormalForm.jl</span></span>
<span class="line"><span>│   │   │   ├── Spaces.jl</span></span>
<span class="line"><span>│   │   │   ├── Types.jl</span></span>
<span class="line"><span>│   │   │   ├── ZGenus.jl</span></span>
<span class="line"><span>│   │   │   └── ZLattices.jl</span></span>
<span class="line"><span>│   │   ├── QuadBin.jl</span></span>
<span class="line"><span>│   │   ├── Torsion.jl</span></span>
<span class="line"><span>│   ├── QuadForm.jl</span></span>
<span class="line"><span>│</span></span>
<span class="line"><span>│</span></span>
<span class="line"><span>│</span></span>
<span class="line"><span>├── test</span></span>
<span class="line"><span>│   ├── QuadForm</span></span>
<span class="line"><span>│   │   ├── Enumeration.jl</span></span>
<span class="line"><span>│   │   ├── Herm</span></span>
<span class="line"><span>│   │   │   ├── Genus.jl</span></span>
<span class="line"><span>│   │   ├── Quad</span></span>
<span class="line"><span>│   │   │   ├── Genus.jl</span></span>
<span class="line"><span>│   │   │   ├── GenusRep.jl</span></span>
<span class="line"><span>│   │   │   ├── NormalForm.jl</span></span>
<span class="line"><span>│   │   │   ├── Spaces.jl</span></span>
<span class="line"><span>│   │   │   ├── ZGenus.jl</span></span>
<span class="line"><span>│   │   │   └── ZLattices.jl</span></span>
<span class="line"><span>│   │   ├── QuadBin.jl</span></span>
<span class="line"><span>│   │   └── Torsion.jl</span></span>
<span class="line"><span>│   ├── QuadForm.jl</span></span></code></pre></div><h3 id="Adding-tests" tabindex="-1">Adding tests <a class="header-anchor" href="#Adding-tests" aria-label="Permalink to &quot;Adding tests {#Adding-tests}&quot;">​</a></h3><ul><li><p>If one adds functionality to a file, say <code>src/QuadForm/Quad/Genus.jl</code>, a corresponding a test should be added to the corresponding test file. In this case this would be <code>test/QuadForm/Quad/Genus.jl</code>.</p></li><li><p>Assume one adds a new file, say <code>src/QuadForm/New.jl</code>, which is included in <code>src/QuadForm.jl</code>. Then a corresponding file <code>test/QuadForm/Test.jl</code> containing the tests must be added. This new file must then also be included in <code>test/QuadForm.jl</code>.</p></li><li><p>Similar to the above, if a new directory in <code>src/</code> is added, the same must apply in <code>test/</code>.</p></li></ul><h3 id="Adding-long-tests" tabindex="-1">Adding long tests <a class="header-anchor" href="#Adding-long-tests" aria-label="Permalink to &quot;Adding long tests {#Adding-long-tests}&quot;">​</a></h3><p>If one knows that running a particular test will take a long time, one can use <code>@long_test</code> instead of <code>@test</code> inside the test suite. When running the test suite, tests annotated with <code>@long_test</code> will not be run, unless specifically asked for (see below). The continuous integration servers will run at least one job including the long tests.</p><h2 id="Running-the-tests" tabindex="-1">Running the tests <a class="header-anchor" href="#Running-the-tests" aria-label="Permalink to &quot;Running the tests {#Running-the-tests}&quot;">​</a></h2><h3 id="Running-all-tests" tabindex="-1">Running all tests <a class="header-anchor" href="#Running-all-tests" aria-label="Permalink to &quot;Running all tests {#Running-all-tests}&quot;">​</a></h3><p>All tests can be run as usual with <code>Pkg.test(&quot;Hecke&quot;)</code>. The whole test suite can be run in parallel using the following options:</p><ul><li><p>Set the environment variable <code>HECKE_TEST_VARIABLE=n</code>, where <code>n</code> is the number of processes.</p></li><li><p>On julia &gt;= 1.3, run <code>Pkg.test(&quot;Hecke&quot;, test_args = [&quot;-j$(n)&quot;])</code>, where <code>n</code> is the number of processes.</p></li></ul><p>The tests annotated with <code>@long_test</code> can be invoked by setting <code>HECKE_TESTLONG=1</code> or adding &quot;long&quot; to the <code>test_args</code> keyword argument on julia &gt;= 1.3.</p><h3 id="Running-a-subset-of-tests" tabindex="-1">Running a subset of tests <a class="header-anchor" href="#Running-a-subset-of-tests" aria-label="Permalink to &quot;Running a subset of tests {#Running-a-subset-of-tests}&quot;">​</a></h3><p>Because the test structure mirrors the source directory, it is easy to run only a subset of tests. For example, to run all the tests in <code>test/QuadForm/Quad/Genus.jl</code>, one can invoke:</p><div class="language-julia vp-adaptive-theme"><button title="Copy Code" class="copy"></button><span class="lang">julia</span><pre class="shiki shiki-themes github-light github-dark vp-code" tabindex="0"><code><span class="line"><span style="--shiki-light:#24292E;--shiki-dark:#E1E4E8;">julia</span><span style="--shiki-light:#D73A49;--shiki-dark:#F97583;">&gt;</span><span style="--shiki-light:#24292E;--shiki-dark:#E1E4E8;"> Hecke</span><span style="--shiki-light:#D73A49;--shiki-dark:#F97583;">.</span><span style="--shiki-light:#005CC5;--shiki-dark:#79B8FF;">test_module</span><span style="--shiki-light:#24292E;--shiki-dark:#E1E4E8;">(</span><span style="--shiki-light:#032F62;--shiki-dark:#9ECBFF;">&quot;QuadForm/Quad/Genus&quot;</span><span style="--shiki-light:#24292E;--shiki-dark:#E1E4E8;">)</span></span></code></pre></div><p>This also works on the directory level. If one wants to add run all tests for quadratic forms, one can just run</p><div class="language-julia vp-adaptive-theme"><button title="Copy Code" class="copy"></button><span class="lang">julia</span><pre class="shiki shiki-themes github-light github-dark vp-code" tabindex="0"><code><span class="line"><span style="--shiki-light:#24292E;--shiki-dark:#E1E4E8;">julia</span><span style="--shiki-light:#D73A49;--shiki-dark:#F97583;">&gt;</span><span style="--shiki-light:#24292E;--shiki-dark:#E1E4E8;"> Hecke</span><span style="--shiki-light:#D73A49;--shiki-dark:#F97583;">.</span><span style="--shiki-light:#005CC5;--shiki-dark:#79B8FF;">test_module</span><span style="--shiki-light:#24292E;--shiki-dark:#E1E4E8;">(</span><span style="--shiki-light:#032F62;--shiki-dark:#9ECBFF;">&quot;QuadForm&quot;</span><span style="--shiki-light:#24292E;--shiki-dark:#E1E4E8;">)</span></span></code></pre></div>`,18),l=[i];function o(p,d,c,r,u,h){return a(),n("div",null,l)}const m=s(t,[["render",o]]);export{k as __pageData,m as default};
