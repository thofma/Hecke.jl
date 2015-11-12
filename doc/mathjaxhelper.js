


<!DOCTYPE html>
<html lang="en" class="">
  <head prefix="og: http://ogp.me/ns# fb: http://ogp.me/ns/fb# object: http://ogp.me/ns/object# article: http://ogp.me/ns/article# profile: http://ogp.me/ns/profile#">
    <meta charset='utf-8'>
    <meta http-equiv="X-UA-Compatible" content="IE=edge">
    <meta http-equiv="Content-Language" content="en">
    <meta name="viewport" content="width=1020">
    
    
    <title>pymc3/mathjaxhelper.js at master · pymc-devs/pymc3 · GitHub</title>
    <link rel="search" type="application/opensearchdescription+xml" href="/opensearch.xml" title="GitHub">
    <link rel="fluid-icon" href="https://github.com/fluidicon.png" title="GitHub">
    <link rel="apple-touch-icon" sizes="57x57" href="/apple-touch-icon-114.png">
    <link rel="apple-touch-icon" sizes="114x114" href="/apple-touch-icon-114.png">
    <link rel="apple-touch-icon" sizes="72x72" href="/apple-touch-icon-144.png">
    <link rel="apple-touch-icon" sizes="144x144" href="/apple-touch-icon-144.png">
    <meta property="fb:app_id" content="1401488693436528">

      <meta content="@github" name="twitter:site" /><meta content="summary" name="twitter:card" /><meta content="pymc-devs/pymc3" name="twitter:title" /><meta content="pymc3 - PyMC version 3" name="twitter:description" /><meta content="https://avatars2.githubusercontent.com/u/81121?v=3&amp;s=400" name="twitter:image:src" />
      <meta content="GitHub" property="og:site_name" /><meta content="object" property="og:type" /><meta content="https://avatars2.githubusercontent.com/u/81121?v=3&amp;s=400" property="og:image" /><meta content="pymc-devs/pymc3" property="og:title" /><meta content="https://github.com/pymc-devs/pymc3" property="og:url" /><meta content="pymc3 - PyMC version 3" property="og:description" />
      <meta name="browser-stats-url" content="https://api.github.com/_private/browser/stats">
    <meta name="browser-errors-url" content="https://api.github.com/_private/browser/errors">
    <link rel="assets" href="https://assets-cdn.github.com/">
    
    <meta name="pjax-timeout" content="1000">
    

    <meta name="msapplication-TileImage" content="/windows-tile.png">
    <meta name="msapplication-TileColor" content="#ffffff">
    <meta name="selected-link" value="repo_source" data-pjax-transient>

    <meta name="google-site-verification" content="KT5gs8h0wvaagLKAVWq8bbeNwnZZK1r1XQysX3xurLU">
    <meta name="google-analytics" content="UA-3769691-2">

<meta content="collector.githubapp.com" name="octolytics-host" /><meta content="github" name="octolytics-app-id" /><meta content="83F6840D:09B0:2056F00B:5645105C" name="octolytics-dimension-request_id" />

<meta content="Rails, view, blob#show" data-pjax-transient="true" name="analytics-event" />


  <meta class="js-ga-set" name="dimension1" content="Logged Out">
    <meta class="js-ga-set" name="dimension4" content="Current repo nav">




    <meta name="is-dotcom" content="true">
        <meta name="hostname" content="github.com">
    <meta name="user-login" content="">

      <link rel="mask-icon" href="https://assets-cdn.github.com/pinned-octocat.svg" color="#4078c0">
      <link rel="icon" type="image/x-icon" href="https://assets-cdn.github.com/favicon.ico">

    <meta content="799e3795632e7bcbabf99edcaf52b03cb720ac31" name="form-nonce" />

    <link crossorigin="anonymous" href="https://assets-cdn.github.com/assets/github-1c752772917b299240cebd0a813d83d4d81ef2d6b294a702adcb1e02e7ae10db.css" media="all" rel="stylesheet" />
    <link crossorigin="anonymous" href="https://assets-cdn.github.com/assets/github2-82f8f505e9548af8160aa908a24e2f745299264a7f503989d6fa2a392aaa967a.css" media="all" rel="stylesheet" />
    
    
    


    <meta http-equiv="x-pjax-version" content="0a42b326abced71f2c651e345a442f88">

      
  <meta name="description" content="pymc3 - PyMC version 3">
  <meta name="go-import" content="github.com/pymc-devs/pymc3 git https://github.com/pymc-devs/pymc3.git">

  <meta content="81121" name="octolytics-dimension-user_id" /><meta content="pymc-devs" name="octolytics-dimension-user_login" /><meta content="192904" name="octolytics-dimension-repository_id" /><meta content="pymc-devs/pymc3" name="octolytics-dimension-repository_nwo" /><meta content="true" name="octolytics-dimension-repository_public" /><meta content="false" name="octolytics-dimension-repository_is_fork" /><meta content="192904" name="octolytics-dimension-repository_network_root_id" /><meta content="pymc-devs/pymc3" name="octolytics-dimension-repository_network_root_nwo" />
  <link href="https://github.com/pymc-devs/pymc3/commits/master.atom" rel="alternate" title="Recent Commits to pymc3:master" type="application/atom+xml">

  </head>


  <body class="logged_out   env-production  vis-public page-blob">
    <a href="#start-of-content" tabindex="1" class="accessibility-aid js-skip-to-content">Skip to content</a>

    
    
    



      
      <div class="header header-logged-out" role="banner">
  <div class="container clearfix">

    <a class="header-logo-wordmark" href="https://github.com/" data-ga-click="(Logged out) Header, go to homepage, icon:logo-wordmark">
      <span class="mega-octicon octicon-logo-github"></span>
    </a>

    <div class="header-actions" role="navigation">
        <a class="btn btn-primary" href="/join" data-ga-click="(Logged out) Header, clicked Sign up, text:sign-up">Sign up</a>
      <a class="btn" href="/login?return_to=%2Fpymc-devs%2Fpymc3%2Fblob%2Fmaster%2Fdocs%2Fjs%2Fmathjaxhelper.js" data-ga-click="(Logged out) Header, clicked Sign in, text:sign-in">Sign in</a>
    </div>

    <div class="site-search repo-scope js-site-search" role="search">
      <!-- </textarea> --><!-- '"` --><form accept-charset="UTF-8" action="/pymc-devs/pymc3/search" class="js-site-search-form" data-global-search-url="/search" data-repo-search-url="/pymc-devs/pymc3/search" method="get"><div style="margin:0;padding:0;display:inline"><input name="utf8" type="hidden" value="&#x2713;" /></div>
  <label class="js-chromeless-input-container form-control">
    <div class="scope-badge">This repository</div>
    <input type="text"
      class="js-site-search-focus js-site-search-field is-clearable chromeless-input"
      data-hotkey="s"
      name="q"
      placeholder="Search"
      aria-label="Search this repository"
      data-global-scope-placeholder="Search GitHub"
      data-repo-scope-placeholder="Search"
      tabindex="1"
      autocapitalize="off">
  </label>
</form>
    </div>

      <ul class="header-nav left" role="navigation">
          <li class="header-nav-item">
            <a class="header-nav-link" href="/explore" data-ga-click="(Logged out) Header, go to explore, text:explore">Explore</a>
          </li>
          <li class="header-nav-item">
            <a class="header-nav-link" href="/features" data-ga-click="(Logged out) Header, go to features, text:features">Features</a>
          </li>
          <li class="header-nav-item">
            <a class="header-nav-link" href="https://enterprise.github.com/" data-ga-click="(Logged out) Header, go to enterprise, text:enterprise">Enterprise</a>
          </li>
          <li class="header-nav-item">
            <a class="header-nav-link" href="/pricing" data-ga-click="(Logged out) Header, go to pricing, text:pricing">Pricing</a>
          </li>
      </ul>

  </div>
</div>



    <div id="start-of-content" class="accessibility-aid"></div>

    <div id="js-flash-container">
</div>


    <div role="main" class="main-content">
        <div itemscope itemtype="http://schema.org/WebPage">
    <div class="pagehead repohead instapaper_ignore readability-menu">

      <div class="container">

        <div class="clearfix">
          

<ul class="pagehead-actions">

  <li>
      <a href="/login?return_to=%2Fpymc-devs%2Fpymc3"
    class="btn btn-sm btn-with-count tooltipped tooltipped-n"
    aria-label="You must be signed in to watch a repository" rel="nofollow">
    <span class="octicon octicon-eye"></span>
    Watch
  </a>
  <a class="social-count" href="/pymc-devs/pymc3/watchers">
    125
  </a>

  </li>

  <li>
      <a href="/login?return_to=%2Fpymc-devs%2Fpymc3"
    class="btn btn-sm btn-with-count tooltipped tooltipped-n"
    aria-label="You must be signed in to star a repository" rel="nofollow">
    <span class="octicon octicon-star"></span>
    Star
  </a>

    <a class="social-count js-social-count" href="/pymc-devs/pymc3/stargazers">
      1,260
    </a>

  </li>

  <li>
      <a href="/login?return_to=%2Fpymc-devs%2Fpymc3"
        class="btn btn-sm btn-with-count tooltipped tooltipped-n"
        aria-label="You must be signed in to fork a repository" rel="nofollow">
        <span class="octicon octicon-repo-forked"></span>
        Fork
      </a>

    <a href="/pymc-devs/pymc3/network" class="social-count">
      269
    </a>
  </li>
</ul>

          <h1 itemscope itemtype="http://data-vocabulary.org/Breadcrumb" class="entry-title public ">
  <span class="mega-octicon octicon-repo"></span>
  <span class="author"><a href="/pymc-devs" class="url fn" itemprop="url" rel="author"><span itemprop="title">pymc-devs</span></a></span><!--
--><span class="path-divider">/</span><!--
--><strong><a href="/pymc-devs/pymc3" data-pjax="#js-repo-pjax-container">pymc3</a></strong>

  <span class="page-context-loader">
    <img alt="" height="16" src="https://assets-cdn.github.com/images/spinners/octocat-spinner-32.gif" width="16" />
  </span>

</h1>

        </div>
      </div>
    </div>

    <div class="container">
      <div class="repository-with-sidebar repo-container new-discussion-timeline ">
        <div class="repository-sidebar clearfix">
          
<nav class="sunken-menu repo-nav js-repo-nav js-sidenav-container-pjax js-octicon-loaders"
     role="navigation"
     data-pjax="#js-repo-pjax-container"
     data-issue-count-url="/pymc-devs/pymc3/issues/counts">
  <ul class="sunken-menu-group">
    <li class="tooltipped tooltipped-w" aria-label="Code">
      <a href="/pymc-devs/pymc3" aria-label="Code" aria-selected="true" class="js-selected-navigation-item selected sunken-menu-item" data-hotkey="g c" data-selected-links="repo_source repo_downloads repo_commits repo_releases repo_tags repo_branches /pymc-devs/pymc3">
        <span class="octicon octicon-code"></span> <span class="full-word">Code</span>
        <img alt="" class="mini-loader" height="16" src="https://assets-cdn.github.com/images/spinners/octocat-spinner-32.gif" width="16" />
</a>    </li>

      <li class="tooltipped tooltipped-w" aria-label="Issues">
        <a href="/pymc-devs/pymc3/issues" aria-label="Issues" class="js-selected-navigation-item sunken-menu-item" data-hotkey="g i" data-selected-links="repo_issues repo_labels repo_milestones /pymc-devs/pymc3/issues">
          <span class="octicon octicon-issue-opened"></span> <span class="full-word">Issues</span>
          <span class="js-issue-replace-counter"></span>
          <img alt="" class="mini-loader" height="16" src="https://assets-cdn.github.com/images/spinners/octocat-spinner-32.gif" width="16" />
</a>      </li>

    <li class="tooltipped tooltipped-w" aria-label="Pull requests">
      <a href="/pymc-devs/pymc3/pulls" aria-label="Pull requests" class="js-selected-navigation-item sunken-menu-item" data-hotkey="g p" data-selected-links="repo_pulls /pymc-devs/pymc3/pulls">
          <span class="octicon octicon-git-pull-request"></span> <span class="full-word">Pull requests</span>
          <span class="js-pull-replace-counter"></span>
          <img alt="" class="mini-loader" height="16" src="https://assets-cdn.github.com/images/spinners/octocat-spinner-32.gif" width="16" />
</a>    </li>

      <li class="tooltipped tooltipped-w" aria-label="Wiki">
        <a href="/pymc-devs/pymc3/wiki" aria-label="Wiki" class="js-selected-navigation-item sunken-menu-item" data-hotkey="g w" data-selected-links="repo_wiki /pymc-devs/pymc3/wiki">
          <span class="octicon octicon-book"></span> <span class="full-word">Wiki</span>
          <img alt="" class="mini-loader" height="16" src="https://assets-cdn.github.com/images/spinners/octocat-spinner-32.gif" width="16" />
</a>      </li>
  </ul>
  <div class="sunken-menu-separator"></div>
  <ul class="sunken-menu-group">

    <li class="tooltipped tooltipped-w" aria-label="Pulse">
      <a href="/pymc-devs/pymc3/pulse" aria-label="Pulse" class="js-selected-navigation-item sunken-menu-item" data-selected-links="pulse /pymc-devs/pymc3/pulse">
        <span class="octicon octicon-pulse"></span> <span class="full-word">Pulse</span>
        <img alt="" class="mini-loader" height="16" src="https://assets-cdn.github.com/images/spinners/octocat-spinner-32.gif" width="16" />
</a>    </li>

    <li class="tooltipped tooltipped-w" aria-label="Graphs">
      <a href="/pymc-devs/pymc3/graphs" aria-label="Graphs" class="js-selected-navigation-item sunken-menu-item" data-selected-links="repo_graphs repo_contributors /pymc-devs/pymc3/graphs">
        <span class="octicon octicon-graph"></span> <span class="full-word">Graphs</span>
        <img alt="" class="mini-loader" height="16" src="https://assets-cdn.github.com/images/spinners/octocat-spinner-32.gif" width="16" />
</a>    </li>
  </ul>


</nav>

            <div class="only-with-full-nav">
                
<div class="js-clone-url clone-url open"
  data-protocol-type="http">
  <h3 class="text-small text-muted"><span class="text-emphasized">HTTPS</span> clone URL</h3>
  <div class="input-group js-zeroclipboard-container">
    <input type="text" class="input-mini text-small text-muted input-monospace js-url-field js-zeroclipboard-target"
           value="https://github.com/pymc-devs/pymc3.git" readonly="readonly" aria-label="HTTPS clone URL">
    <span class="input-group-button">
      <button aria-label="Copy to clipboard" class="js-zeroclipboard btn btn-sm zeroclipboard-button tooltipped tooltipped-s" data-copied-hint="Copied!" type="button"><span class="octicon octicon-clippy"></span></button>
    </span>
  </div>
</div>

  
<div class="js-clone-url clone-url "
  data-protocol-type="subversion">
  <h3 class="text-small text-muted"><span class="text-emphasized">Subversion</span> checkout URL</h3>
  <div class="input-group js-zeroclipboard-container">
    <input type="text" class="input-mini text-small text-muted input-monospace js-url-field js-zeroclipboard-target"
           value="https://github.com/pymc-devs/pymc3" readonly="readonly" aria-label="Subversion checkout URL">
    <span class="input-group-button">
      <button aria-label="Copy to clipboard" class="js-zeroclipboard btn btn-sm zeroclipboard-button tooltipped tooltipped-s" data-copied-hint="Copied!" type="button"><span class="octicon octicon-clippy"></span></button>
    </span>
  </div>
</div>



<div class="clone-options text-small text-muted">You can clone with
  <!-- </textarea> --><!-- '"` --><form accept-charset="UTF-8" action="/users/set_protocol?protocol_selector=http&amp;protocol_type=clone" class="inline-form js-clone-selector-form " data-form-nonce="799e3795632e7bcbabf99edcaf52b03cb720ac31" data-remote="true" method="post"><div style="margin:0;padding:0;display:inline"><input name="utf8" type="hidden" value="&#x2713;" /><input name="authenticity_token" type="hidden" value="y3FuJPTLQRX3AkBjptOlLJWo3ndFhiI5GibYTQT0s7R57FpMPm/tbUm1NkHsNFghts9iwmhZbhxA6Of4hxss3g==" /></div><button class="btn-link js-clone-selector" data-protocol="http" type="submit">HTTPS</button></form> or <!-- </textarea> --><!-- '"` --><form accept-charset="UTF-8" action="/users/set_protocol?protocol_selector=subversion&amp;protocol_type=clone" class="inline-form js-clone-selector-form " data-form-nonce="799e3795632e7bcbabf99edcaf52b03cb720ac31" data-remote="true" method="post"><div style="margin:0;padding:0;display:inline"><input name="utf8" type="hidden" value="&#x2713;" /><input name="authenticity_token" type="hidden" value="hG/njmaths4KT4KZjD0xDxichQlN0idj/Yj9x3ZAokAjM+kaOHsVrh5dqZN5joFHxAx/uUJBV9wM+yBqOUrfIQ==" /></div><button class="btn-link js-clone-selector" data-protocol="subversion" type="submit">Subversion</button></form>.
  <a href="https://help.github.com/articles/which-remote-url-should-i-use" class="help tooltipped tooltipped-n" aria-label="Get help on which URL is right for you.">
    <span class="octicon octicon-question"></span>
  </a>
</div>

              <a href="/pymc-devs/pymc3/archive/master.zip"
                 class="btn btn-sm sidebar-button"
                 aria-label="Download the contents of pymc-devs/pymc3 as a zip file"
                 title="Download the contents of pymc-devs/pymc3 as a zip file"
                 rel="nofollow">
                <span class="octicon octicon-cloud-download"></span>
                Download ZIP
              </a>
            </div>
        </div>
        <div id="js-repo-pjax-container" class="repository-content context-loader-container" data-pjax-container>

          

<a href="/pymc-devs/pymc3/blob/b466398d935ca7e4f0e6db45d57272fcd9f17321/docs/js/mathjaxhelper.js" class="hidden js-permalink-shortcut" data-hotkey="y">Permalink</a>

<!-- blob contrib key: blob_contributors:v21:142abce0c2993aea6b373893f8c22749 -->

  <div class="file-navigation js-zeroclipboard-container">
    
<div class="select-menu js-menu-container js-select-menu left">
  <button class="btn btn-sm select-menu-button js-menu-target css-truncate" data-hotkey="w"
    title="master"
    type="button" aria-label="Switch branches or tags" tabindex="0" aria-haspopup="true">
    <i>Branch:</i>
    <span class="js-select-button css-truncate-target">master</span>
  </button>

  <div class="select-menu-modal-holder js-menu-content js-navigation-container" data-pjax aria-hidden="true">

    <div class="select-menu-modal">
      <div class="select-menu-header">
        <span class="octicon octicon-x js-menu-close" role="button" aria-label="Close"></span>
        <span class="select-menu-title">Switch branches/tags</span>
      </div>

      <div class="select-menu-filters">
        <div class="select-menu-text-filter">
          <input type="text" aria-label="Filter branches/tags" id="context-commitish-filter-field" class="js-filterable-field js-navigation-enable" placeholder="Filter branches/tags">
        </div>
        <div class="select-menu-tabs">
          <ul>
            <li class="select-menu-tab">
              <a href="#" data-tab-filter="branches" data-filter-placeholder="Filter branches/tags" class="js-select-menu-tab" role="tab">Branches</a>
            </li>
            <li class="select-menu-tab">
              <a href="#" data-tab-filter="tags" data-filter-placeholder="Find a tag…" class="js-select-menu-tab" role="tab">Tags</a>
            </li>
          </ul>
        </div>
      </div>

      <div class="select-menu-list select-menu-tab-bucket js-select-menu-tab-bucket" data-tab-filter="branches" role="menu">

        <div data-filterable-for="context-commitish-filter-field" data-filterable-type="substring">


            <a class="select-menu-item js-navigation-item js-navigation-open "
               href="/pymc-devs/pymc3/blob/advi/docs/js/mathjaxhelper.js"
               data-name="advi"
               data-skip-pjax="true"
               rel="nofollow">
              <span class="select-menu-item-icon octicon octicon-check"></span>
              <span class="select-menu-item-text css-truncate-target" title="advi">
                advi
              </span>
            </a>
            <a class="select-menu-item js-navigation-item js-navigation-open "
               href="/pymc-devs/pymc3/blob/categoricalfoolings/docs/js/mathjaxhelper.js"
               data-name="categoricalfoolings"
               data-skip-pjax="true"
               rel="nofollow">
              <span class="select-menu-item-icon octicon octicon-check"></span>
              <span class="select-menu-item-text css-truncate-target" title="categoricalfoolings">
                categoricalfoolings
              </span>
            </a>
            <a class="select-menu-item js-navigation-item js-navigation-open "
               href="/pymc-devs/pymc3/blob/conditional_pdf/docs/js/mathjaxhelper.js"
               data-name="conditional_pdf"
               data-skip-pjax="true"
               rel="nofollow">
              <span class="select-menu-item-icon octicon octicon-check"></span>
              <span class="select-menu-item-text css-truncate-target" title="conditional_pdf">
                conditional_pdf
              </span>
            </a>
            <a class="select-menu-item js-navigation-item js-navigation-open "
               href="/pymc-devs/pymc3/blob/defaults/docs/js/mathjaxhelper.js"
               data-name="defaults"
               data-skip-pjax="true"
               rel="nofollow">
              <span class="select-menu-item-icon octicon octicon-check"></span>
              <span class="select-menu-item-text css-truncate-target" title="defaults">
                defaults
              </span>
            </a>
            <a class="select-menu-item js-navigation-item js-navigation-open "
               href="/pymc-devs/pymc3/blob/discrete_tests/docs/js/mathjaxhelper.js"
               data-name="discrete_tests"
               data-skip-pjax="true"
               rel="nofollow">
              <span class="select-menu-item-icon octicon octicon-check"></span>
              <span class="select-menu-item-text css-truncate-target" title="discrete_tests">
                discrete_tests
              </span>
            </a>
            <a class="select-menu-item js-navigation-item js-navigation-open "
               href="/pymc-devs/pymc3/blob/fast_clean/docs/js/mathjaxhelper.js"
               data-name="fast_clean"
               data-skip-pjax="true"
               rel="nofollow">
              <span class="select-menu-item-icon octicon octicon-check"></span>
              <span class="select-menu-item-text css-truncate-target" title="fast_clean">
                fast_clean
              </span>
            </a>
            <a class="select-menu-item js-navigation-item js-navigation-open "
               href="/pymc-devs/pymc3/blob/fast/docs/js/mathjaxhelper.js"
               data-name="fast"
               data-skip-pjax="true"
               rel="nofollow">
              <span class="select-menu-item-icon octicon octicon-check"></span>
              <span class="select-menu-item-text css-truncate-target" title="fast">
                fast
              </span>
            </a>
            <a class="select-menu-item js-navigation-item js-navigation-open "
               href="/pymc-devs/pymc3/blob/fastrec/docs/js/mathjaxhelper.js"
               data-name="fastrec"
               data-skip-pjax="true"
               rel="nofollow">
              <span class="select-menu-item-icon octicon octicon-check"></span>
              <span class="select-menu-item-text css-truncate-target" title="fastrec">
                fastrec
              </span>
            </a>
            <a class="select-menu-item js-navigation-item js-navigation-open "
               href="/pymc-devs/pymc3/blob/fix_beset/docs/js/mathjaxhelper.js"
               data-name="fix_beset"
               data-skip-pjax="true"
               rel="nofollow">
              <span class="select-menu-item-icon octicon octicon-check"></span>
              <span class="select-menu-item-text css-truncate-target" title="fix_beset">
                fix_beset
              </span>
            </a>
            <a class="select-menu-item js-navigation-item js-navigation-open "
               href="/pymc-devs/pymc3/blob/fix_bounds/docs/js/mathjaxhelper.js"
               data-name="fix_bounds"
               data-skip-pjax="true"
               rel="nofollow">
              <span class="select-menu-item-icon octicon octicon-check"></span>
              <span class="select-menu-item-text css-truncate-target" title="fix_bounds">
                fix_bounds
              </span>
            </a>
            <a class="select-menu-item js-navigation-item js-navigation-open "
               href="/pymc-devs/pymc3/blob/gh-pages/docs/js/mathjaxhelper.js"
               data-name="gh-pages"
               data-skip-pjax="true"
               rel="nofollow">
              <span class="select-menu-item-icon octicon octicon-check"></span>
              <span class="select-menu-item-text css-truncate-target" title="gh-pages">
                gh-pages
              </span>
            </a>
            <a class="select-menu-item js-navigation-item js-navigation-open "
               href="/pymc-devs/pymc3/blob/gibbs/docs/js/mathjaxhelper.js"
               data-name="gibbs"
               data-skip-pjax="true"
               rel="nofollow">
              <span class="select-menu-item-icon octicon octicon-check"></span>
              <span class="select-menu-item-text css-truncate-target" title="gibbs">
                gibbs
              </span>
            </a>
            <a class="select-menu-item js-navigation-item js-navigation-open "
               href="/pymc-devs/pymc3/blob/gp/docs/js/mathjaxhelper.js"
               data-name="gp"
               data-skip-pjax="true"
               rel="nofollow">
              <span class="select-menu-item-icon octicon octicon-check"></span>
              <span class="select-menu-item-text css-truncate-target" title="gp">
                gp
              </span>
            </a>
            <a class="select-menu-item js-navigation-item js-navigation-open "
               href="/pymc-devs/pymc3/blob/km/rubgy-fix/docs/js/mathjaxhelper.js"
               data-name="km/rubgy-fix"
               data-skip-pjax="true"
               rel="nofollow">
              <span class="select-menu-item-icon octicon octicon-check"></span>
              <span class="select-menu-item-text css-truncate-target" title="km/rubgy-fix">
                km/rubgy-fix
              </span>
            </a>
            <a class="select-menu-item js-navigation-item js-navigation-open "
               href="/pymc-devs/pymc3/blob/lbfgs/docs/js/mathjaxhelper.js"
               data-name="lbfgs"
               data-skip-pjax="true"
               rel="nofollow">
              <span class="select-menu-item-icon octicon octicon-check"></span>
              <span class="select-menu-item-text css-truncate-target" title="lbfgs">
                lbfgs
              </span>
            </a>
            <a class="select-menu-item js-navigation-item js-navigation-open selected"
               href="/pymc-devs/pymc3/blob/master/docs/js/mathjaxhelper.js"
               data-name="master"
               data-skip-pjax="true"
               rel="nofollow">
              <span class="select-menu-item-icon octicon octicon-check"></span>
              <span class="select-menu-item-text css-truncate-target" title="master">
                master
              </span>
            </a>
            <a class="select-menu-item js-navigation-item js-navigation-open "
               href="/pymc-devs/pymc3/blob/nuts/docs/js/mathjaxhelper.js"
               data-name="nuts"
               data-skip-pjax="true"
               rel="nofollow">
              <span class="select-menu-item-icon octicon octicon-check"></span>
              <span class="select-menu-item-text css-truncate-target" title="nuts">
                nuts
              </span>
            </a>
            <a class="select-menu-item js-navigation-item js-navigation-open "
               href="/pymc-devs/pymc3/blob/parallel/docs/js/mathjaxhelper.js"
               data-name="parallel"
               data-skip-pjax="true"
               rel="nofollow">
              <span class="select-menu-item-icon octicon octicon-check"></span>
              <span class="select-menu-item-text css-truncate-target" title="parallel">
                parallel
              </span>
            </a>
            <a class="select-menu-item js-navigation-item js-navigation-open "
               href="/pymc-devs/pymc3/blob/prior_plot/docs/js/mathjaxhelper.js"
               data-name="prior_plot"
               data-skip-pjax="true"
               rel="nofollow">
              <span class="select-menu-item-icon octicon octicon-check"></span>
              <span class="select-menu-item-text css-truncate-target" title="prior_plot">
                prior_plot
              </span>
            </a>
            <a class="select-menu-item js-navigation-item js-navigation-open "
               href="/pymc-devs/pymc3/blob/profile/docs/js/mathjaxhelper.js"
               data-name="profile"
               data-skip-pjax="true"
               rel="nofollow">
              <span class="select-menu-item-icon octicon octicon-check"></span>
              <span class="select-menu-item-text css-truncate-target" title="profile">
                profile
              </span>
            </a>
            <a class="select-menu-item js-navigation-item js-navigation-open "
               href="/pymc-devs/pymc3/blob/random/docs/js/mathjaxhelper.js"
               data-name="random"
               data-skip-pjax="true"
               rel="nofollow">
              <span class="select-menu-item-icon octicon octicon-check"></span>
              <span class="select-menu-item-text css-truncate-target" title="random">
                random
              </span>
            </a>
            <a class="select-menu-item js-navigation-item js-navigation-open "
               href="/pymc-devs/pymc3/blob/readme/docs/js/mathjaxhelper.js"
               data-name="readme"
               data-skip-pjax="true"
               rel="nofollow">
              <span class="select-menu-item-icon octicon octicon-check"></span>
              <span class="select-menu-item-text css-truncate-target" title="readme">
                readme
              </span>
            </a>
            <a class="select-menu-item js-navigation-item js-navigation-open "
               href="/pymc-devs/pymc3/blob/rename_as_op/docs/js/mathjaxhelper.js"
               data-name="rename_as_op"
               data-skip-pjax="true"
               rel="nofollow">
              <span class="select-menu-item-icon octicon octicon-check"></span>
              <span class="select-menu-item-text css-truncate-target" title="rename_as_op">
                rename_as_op
              </span>
            </a>
            <a class="select-menu-item js-navigation-item js-navigation-open "
               href="/pymc-devs/pymc3/blob/rsv_fix/docs/js/mathjaxhelper.js"
               data-name="rsv_fix"
               data-skip-pjax="true"
               rel="nofollow">
              <span class="select-menu-item-icon octicon octicon-check"></span>
              <span class="select-menu-item-text css-truncate-target" title="rsv_fix">
                rsv_fix
              </span>
            </a>
            <a class="select-menu-item js-navigation-item js-navigation-open "
               href="/pymc-devs/pymc3/blob/sharedfix/docs/js/mathjaxhelper.js"
               data-name="sharedfix"
               data-skip-pjax="true"
               rel="nofollow">
              <span class="select-menu-item-icon octicon octicon-check"></span>
              <span class="select-menu-item-text css-truncate-target" title="sharedfix">
                sharedfix
              </span>
            </a>
            <a class="select-menu-item js-navigation-item js-navigation-open "
               href="/pymc-devs/pymc3/blob/transform_classes/docs/js/mathjaxhelper.js"
               data-name="transform_classes"
               data-skip-pjax="true"
               rel="nofollow">
              <span class="select-menu-item-icon octicon octicon-check"></span>
              <span class="select-menu-item-text css-truncate-target" title="transform_classes">
                transform_classes
              </span>
            </a>
            <a class="select-menu-item js-navigation-item js-navigation-open "
               href="/pymc-devs/pymc3/blob/uqchapter/docs/js/mathjaxhelper.js"
               data-name="uqchapter"
               data-skip-pjax="true"
               rel="nofollow">
              <span class="select-menu-item-icon octicon octicon-check"></span>
              <span class="select-menu-item-text css-truncate-target" title="uqchapter">
                uqchapter
              </span>
            </a>
            <a class="select-menu-item js-navigation-item js-navigation-open "
               href="/pymc-devs/pymc3/blob/value_attr/docs/js/mathjaxhelper.js"
               data-name="value_attr"
               data-skip-pjax="true"
               rel="nofollow">
              <span class="select-menu-item-icon octicon octicon-check"></span>
              <span class="select-menu-item-text css-truncate-target" title="value_attr">
                value_attr
              </span>
            </a>
            <a class="select-menu-item js-navigation-item js-navigation-open "
               href="/pymc-devs/pymc3/blob/wishart/docs/js/mathjaxhelper.js"
               data-name="wishart"
               data-skip-pjax="true"
               rel="nofollow">
              <span class="select-menu-item-icon octicon octicon-check"></span>
              <span class="select-menu-item-text css-truncate-target" title="wishart">
                wishart
              </span>
            </a>
        </div>

          <div class="select-menu-no-results">Nothing to show</div>
      </div>

      <div class="select-menu-list select-menu-tab-bucket js-select-menu-tab-bucket" data-tab-filter="tags">
        <div data-filterable-for="context-commitish-filter-field" data-filterable-type="substring">


            <div class="select-menu-item js-navigation-item ">
              <span class="select-menu-item-icon octicon octicon-check"></span>
              <a href="/pymc-devs/pymc3/tree/v3.0beta/docs/js/mathjaxhelper.js"
                 data-name="v3.0beta"
                 data-skip-pjax="true"
                 rel="nofollow"
                 class="js-navigation-open select-menu-item-text css-truncate-target"
                 title="v3.0beta">v3.0beta</a>
            </div>
            <div class="select-menu-item js-navigation-item ">
              <span class="select-menu-item-icon octicon octicon-check"></span>
              <a href="/pymc-devs/pymc3/tree/v3.0alpha/docs/js/mathjaxhelper.js"
                 data-name="v3.0alpha"
                 data-skip-pjax="true"
                 rel="nofollow"
                 class="js-navigation-open select-menu-item-text css-truncate-target"
                 title="v3.0alpha">v3.0alpha</a>
            </div>
        </div>

        <div class="select-menu-no-results">Nothing to show</div>
      </div>

    </div>
  </div>
</div>

    <div class="btn-group right">
      <a href="/pymc-devs/pymc3/find/master"
            class="js-show-file-finder btn btn-sm empty-icon tooltipped tooltipped-nw"
            data-pjax
            data-hotkey="t"
            aria-label="Quickly jump between files">
        <span class="octicon octicon-list-unordered"></span>
      </a>
      <button aria-label="Copy file path to clipboard" class="js-zeroclipboard btn btn-sm zeroclipboard-button tooltipped tooltipped-s" data-copied-hint="Copied!" type="button"><span class="octicon octicon-clippy"></span></button>
    </div>

    <div class="breadcrumb js-zeroclipboard-target">
      <span class="repo-root js-repo-root"><span itemscope="" itemtype="http://data-vocabulary.org/Breadcrumb"><a href="/pymc-devs/pymc3" class="" data-branch="master" data-pjax="true" itemscope="url"><span itemprop="title">pymc3</span></a></span></span><span class="separator">/</span><span itemscope="" itemtype="http://data-vocabulary.org/Breadcrumb"><a href="/pymc-devs/pymc3/tree/master/docs" class="" data-branch="master" data-pjax="true" itemscope="url"><span itemprop="title">docs</span></a></span><span class="separator">/</span><span itemscope="" itemtype="http://data-vocabulary.org/Breadcrumb"><a href="/pymc-devs/pymc3/tree/master/docs/js" class="" data-branch="master" data-pjax="true" itemscope="url"><span itemprop="title">js</span></a></span><span class="separator">/</span><strong class="final-path">mathjaxhelper.js</strong>
    </div>
  </div>


  <div class="commit-tease">
      <span class="right">
        <a class="commit-tease-sha" href="/pymc-devs/pymc3/commit/07af6fde045264e0aea9b51c23f6ea9fd8bff3b5" data-pjax>
          07af6fd
        </a>
        <time datetime="2015-02-25T14:03:19Z" is="relative-time">Feb 25, 2015</time>
      </span>
      <div>
        <img alt="@twiecki" class="avatar" height="20" src="https://avatars3.githubusercontent.com/u/674200?v=3&amp;s=40" width="20" />
        <a href="/twiecki" class="user-mention" rel="contributor">twiecki</a>
          <a href="/pymc-devs/pymc3/commit/07af6fde045264e0aea9b51c23f6ea9fd8bff3b5" class="message" data-pjax="true" title="Fix mathjax issues. Add hierarchical GLM example.">Fix mathjax issues. Add hierarchical GLM example.</a>
      </div>

    <div class="commit-tease-contributors">
      <a class="muted-link contributors-toggle" href="#blob_contributors_box" rel="facebox">
        <strong>1</strong>
         contributor
      </a>
      
    </div>

    <div id="blob_contributors_box" style="display:none">
      <h2 class="facebox-header" data-facebox-id="facebox-header">Users who have contributed to this file</h2>
      <ul class="facebox-user-list" data-facebox-id="facebox-description">
          <li class="facebox-user-list-item">
            <img alt="@twiecki" height="24" src="https://avatars1.githubusercontent.com/u/674200?v=3&amp;s=48" width="24" />
            <a href="/twiecki">twiecki</a>
          </li>
      </ul>
    </div>
  </div>

<div class="file">
  <div class="file-header">
  <div class="file-actions">

    <div class="btn-group">
      <a href="/pymc-devs/pymc3/raw/master/docs/js/mathjaxhelper.js" class="btn btn-sm " id="raw-url">Raw</a>
        <a href="/pymc-devs/pymc3/blame/master/docs/js/mathjaxhelper.js" class="btn btn-sm js-update-url-with-hash">Blame</a>
      <a href="/pymc-devs/pymc3/commits/master/docs/js/mathjaxhelper.js" class="btn btn-sm " rel="nofollow">History</a>
    </div>


        <button type="button" class="octicon-btn disabled tooltipped tooltipped-nw"
          aria-label="You must be signed in to make or propose changes">
          <span class="octicon octicon-pencil"></span>
        </button>
        <button type="button" class="octicon-btn octicon-btn-danger disabled tooltipped tooltipped-nw"
          aria-label="You must be signed in to make or propose changes">
          <span class="octicon octicon-trashcan"></span>
        </button>
  </div>

  <div class="file-info">
      10 lines (10 sloc)
      <span class="file-info-divider"></span>
    138 Bytes
  </div>
</div>

  

  <div class="blob-wrapper data type-javascript">
      <table class="highlight tab-size js-file-line-container" data-tab-size="8">
      <tr>
        <td id="L1" class="blob-num js-line-number" data-line-number="1"></td>
        <td id="LC1" class="blob-code blob-code-inner js-file-line"><span class="pl-c">/*</span></td>
      </tr>
      <tr>
        <td id="L2" class="blob-num js-line-number" data-line-number="2"></td>
        <td id="LC2" class="blob-code blob-code-inner js-file-line"><span class="pl-c">#if false</span></td>
      </tr>
      <tr>
        <td id="L3" class="blob-num js-line-number" data-line-number="3"></td>
        <td id="LC3" class="blob-code blob-code-inner js-file-line"><span class="pl-c">Prevent Unity to try compiling this js</span></td>
      </tr>
      <tr>
        <td id="L4" class="blob-num js-line-number" data-line-number="4"></td>
        <td id="LC4" class="blob-code blob-code-inner js-file-line"><span class="pl-c">*/</span></td>
      </tr>
      <tr>
        <td id="L5" class="blob-num js-line-number" data-line-number="5"></td>
        <td id="LC5" class="blob-code blob-code-inner js-file-line">MathJax.Hub.Config({</td>
      </tr>
      <tr>
        <td id="L6" class="blob-num js-line-number" data-line-number="6"></td>
        <td id="LC6" class="blob-code blob-code-inner js-file-line">	<span class="pl-s"><span class="pl-pds">&quot;</span>tex2jax<span class="pl-pds">&quot;</span></span><span class="pl-k">:</span> { inlineMath<span class="pl-k">:</span> [ [ <span class="pl-s"><span class="pl-pds">&#39;</span>$<span class="pl-pds">&#39;</span></span>, <span class="pl-s"><span class="pl-pds">&#39;</span>$<span class="pl-pds">&#39;</span></span> ] ] }</td>
      </tr>
      <tr>
        <td id="L7" class="blob-num js-line-number" data-line-number="7"></td>
        <td id="LC7" class="blob-code blob-code-inner js-file-line">	});</td>
      </tr>
      <tr>
        <td id="L8" class="blob-num js-line-number" data-line-number="8"></td>
        <td id="LC8" class="blob-code blob-code-inner js-file-line"><span class="pl-c">/*</span></td>
      </tr>
      <tr>
        <td id="L9" class="blob-num js-line-number" data-line-number="9"></td>
        <td id="LC9" class="blob-code blob-code-inner js-file-line"><span class="pl-c">#endif</span></td>
      </tr>
      <tr>
        <td id="L10" class="blob-num js-line-number" data-line-number="10"></td>
        <td id="LC10" class="blob-code blob-code-inner js-file-line"><span class="pl-c">*/</span></td>
      </tr>
</table>

  </div>

</div>

<a href="#jump-to-line" rel="facebox[.linejump]" data-hotkey="l" style="display:none">Jump to Line</a>
<div id="jump-to-line" style="display:none">
  <!-- </textarea> --><!-- '"` --><form accept-charset="UTF-8" action="" class="js-jump-to-line-form" method="get"><div style="margin:0;padding:0;display:inline"><input name="utf8" type="hidden" value="&#x2713;" /></div>
    <input class="linejump-input js-jump-to-line-field" type="text" placeholder="Jump to line&hellip;" aria-label="Jump to line" autofocus>
    <button type="submit" class="btn">Go</button>
</form></div>

        </div>
      </div>
      <div class="modal-backdrop"></div>
    </div>
  </div>


    </div>

      <div class="container">
  <div class="site-footer" role="contentinfo">
    <ul class="site-footer-links right">
        <li><a href="https://status.github.com/" data-ga-click="Footer, go to status, text:status">Status</a></li>
      <li><a href="https://developer.github.com" data-ga-click="Footer, go to api, text:api">API</a></li>
      <li><a href="https://training.github.com" data-ga-click="Footer, go to training, text:training">Training</a></li>
      <li><a href="https://shop.github.com" data-ga-click="Footer, go to shop, text:shop">Shop</a></li>
        <li><a href="https://github.com/blog" data-ga-click="Footer, go to blog, text:blog">Blog</a></li>
        <li><a href="https://github.com/about" data-ga-click="Footer, go to about, text:about">About</a></li>
        <li><a href="https://github.com/pricing" data-ga-click="Footer, go to pricing, text:pricing">Pricing</a></li>

    </ul>

    <a href="https://github.com" aria-label="Homepage">
      <span class="mega-octicon octicon-mark-github" title="GitHub"></span>
</a>
    <ul class="site-footer-links">
      <li>&copy; 2015 <span title="0.04153s from github-fe134-cp1-prd.iad.github.net">GitHub</span>, Inc.</li>
        <li><a href="https://github.com/site/terms" data-ga-click="Footer, go to terms, text:terms">Terms</a></li>
        <li><a href="https://github.com/site/privacy" data-ga-click="Footer, go to privacy, text:privacy">Privacy</a></li>
        <li><a href="https://github.com/security" data-ga-click="Footer, go to security, text:security">Security</a></li>
        <li><a href="https://github.com/contact" data-ga-click="Footer, go to contact, text:contact">Contact</a></li>
        <li><a href="https://help.github.com" data-ga-click="Footer, go to help, text:help">Help</a></li>
    </ul>
  </div>
</div>



    
    
    

    <div id="ajax-error-message" class="flash flash-error">
      <span class="octicon octicon-alert"></span>
      <button type="button" class="flash-close js-flash-close js-ajax-error-dismiss" aria-label="Dismiss error">
        <span class="octicon octicon-x"></span>
      </button>
      Something went wrong with that request. Please try again.
    </div>


      <script crossorigin="anonymous" src="https://assets-cdn.github.com/assets/frameworks-2e7fc3d264a208e1383de85b815379beccff56c1f977714515d4cac7820eef3e.js"></script>
      <script async="async" crossorigin="anonymous" src="https://assets-cdn.github.com/assets/github-ad3afa2166b01280a8ade8889a9a7dea8ec9428d62c892b216456b35e9574dcc.js"></script>
      
      
    <div class="js-stale-session-flash stale-session-flash flash flash-warn flash-banner hidden">
      <span class="octicon octicon-alert"></span>
      <span class="signed-in-tab-flash">You signed in with another tab or window. <a href="">Reload</a> to refresh your session.</span>
      <span class="signed-out-tab-flash">You signed out in another tab or window. <a href="">Reload</a> to refresh your session.</span>
    </div>
  </body>
</html>

