import{_ as k,C as p,c as t,o as n,j as i,a,az as l,G as h,w as r}from"./chunks/framework.BFLv0oST.js";const f=JSON.parse('{"title":"Conjugacy of integral matrices","description":"","frontmatter":{},"headers":[],"relativePath":"manual/misc/conjugacy.md","filePath":"manual/misc/conjugacy.md","lastUpdated":null}'),d={name:"manual/misc/conjugacy.md"},o={class:"jldocstring custom-block"},E={class:"MathJax",jax:"SVG",style:{direction:"ltr",position:"relative"}},g={style:{overflow:"visible","min-height":"1px","min-width":"1px","vertical-align":"0"},xmlns:"http://www.w3.org/2000/svg",width:"1.593ex",height:"1.532ex",role:"img",focusable:"false",viewBox:"0 -677 704 677","aria-hidden":"true"},Q={class:"MathJax",jax:"SVG",style:{direction:"ltr",position:"relative"}},y={style:{overflow:"visible","min-height":"1px","min-width":"1px","vertical-align":"-0.186ex"},xmlns:"http://www.w3.org/2000/svg",width:"9.617ex",height:"1.805ex",role:"img",focusable:"false",viewBox:"0 -716 4250.6 798","aria-hidden":"true"},m={class:"MathJax",jax:"SVG",style:{direction:"ltr",position:"relative"}},C={style:{overflow:"visible","min-height":"1px","min-width":"1px","vertical-align":"0"},xmlns:"http://www.w3.org/2000/svg",width:"1.593ex",height:"1.532ex",role:"img",focusable:"false",viewBox:"0 -677 704 677","aria-hidden":"true"};function F(c,s,u,T,x,w){const e=p("Badge");return n(),t("div",null,[s[15]||(s[15]=i("h1",{id:"Conjugacy-of-integral-matrices",tabindex:"-1"},[a("Conjugacy of integral matrices "),i("a",{class:"header-anchor",href:"#Conjugacy-of-integral-matrices","aria-label":'Permalink to "Conjugacy of integral matrices {#Conjugacy-of-integral-matrices}"'},"​")],-1)),i("details",o,[i("summary",null,[s[0]||(s[0]=i("a",{id:"is_GLZ_conjugate-Tuple{ZZMatrix, ZZMatrix}",href:"#is_GLZ_conjugate-Tuple{ZZMatrix, ZZMatrix}"},[i("span",{class:"jlbinding"},"is_GLZ_conjugate")],-1)),s[1]||(s[1]=a()),h(e,{type:"info",class:"jlObjectType jlMethod",text:"Method"})]),s[13]||(s[13]=l("",1)),i("p",null,[s[8]||(s[8]=a("Given two integral or rational matrices, determine whether there exists an invertible integral matrix ")),i("mjx-container",E,[(n(),t("svg",g,s[2]||(s[2]=[i("g",{stroke:"currentColor",fill:"currentColor","stroke-width":"0",transform:"scale(1,-1)"},[i("g",{"data-mml-node":"math"},[i("g",{"data-mml-node":"mi"},[i("path",{"data-c":"1D447",d:"M40 437Q21 437 21 445Q21 450 37 501T71 602L88 651Q93 669 101 677H569H659Q691 677 697 676T704 667Q704 661 687 553T668 444Q668 437 649 437Q640 437 637 437T631 442L629 445Q629 451 635 490T641 551Q641 586 628 604T573 629Q568 630 515 631Q469 631 457 630T439 622Q438 621 368 343T298 60Q298 48 386 46Q418 46 427 45T436 36Q436 31 433 22Q429 4 424 1L422 0Q419 0 415 0Q410 0 363 1T228 2Q99 2 64 0H49Q43 6 43 9T45 27Q49 40 55 46H83H94Q174 46 189 55Q190 56 191 56Q196 59 201 76T241 233Q258 301 269 344Q339 619 339 625Q339 630 310 630H279Q212 630 191 624Q146 614 121 583T67 467Q60 445 57 441T43 437H40Z",style:{"stroke-width":"3"}})])])],-1)]))),s[3]||(s[3]=i("mjx-assistive-mml",{unselectable:"on",display:"inline",style:{top:"0px",left:"0px",clip:"rect(1px, 1px, 1px, 1px)","-webkit-touch-callout":"none","-webkit-user-select":"none","-khtml-user-select":"none","-moz-user-select":"none","-ms-user-select":"none","user-select":"none",position:"absolute",padding:"1px 0px 0px 0px",border:"0px",display:"block",width:"auto",overflow:"hidden"}},[i("math",{xmlns:"http://www.w3.org/1998/Math/MathML"},[i("mi",null,"T")])],-1))]),s[9]||(s[9]=a(" with ")),i("mjx-container",Q,[(n(),t("svg",y,s[4]||(s[4]=[l("",1)]))),s[5]||(s[5]=i("mjx-assistive-mml",{unselectable:"on",display:"inline",style:{top:"0px",left:"0px",clip:"rect(1px, 1px, 1px, 1px)","-webkit-touch-callout":"none","-webkit-user-select":"none","-khtml-user-select":"none","-moz-user-select":"none","-ms-user-select":"none","user-select":"none",position:"absolute",padding:"1px 0px 0px 0px",border:"0px",display:"block",width:"auto",overflow:"hidden"}},[i("math",{xmlns:"http://www.w3.org/1998/Math/MathML"},[i("mi",null,"T"),i("mi",null,"A"),i("mo",null,"="),i("mi",null,"B"),i("mi",null,"T")])],-1))]),s[10]||(s[10]=a(". If true, the second argument is such a matrix ")),i("mjx-container",m,[(n(),t("svg",C,s[6]||(s[6]=[i("g",{stroke:"currentColor",fill:"currentColor","stroke-width":"0",transform:"scale(1,-1)"},[i("g",{"data-mml-node":"math"},[i("g",{"data-mml-node":"mi"},[i("path",{"data-c":"1D447",d:"M40 437Q21 437 21 445Q21 450 37 501T71 602L88 651Q93 669 101 677H569H659Q691 677 697 676T704 667Q704 661 687 553T668 444Q668 437 649 437Q640 437 637 437T631 442L629 445Q629 451 635 490T641 551Q641 586 628 604T573 629Q568 630 515 631Q469 631 457 630T439 622Q438 621 368 343T298 60Q298 48 386 46Q418 46 427 45T436 36Q436 31 433 22Q429 4 424 1L422 0Q419 0 415 0Q410 0 363 1T228 2Q99 2 64 0H49Q43 6 43 9T45 27Q49 40 55 46H83H94Q174 46 189 55Q190 56 191 56Q196 59 201 76T241 233Q258 301 269 344Q339 619 339 625Q339 630 310 630H279Q212 630 191 624Q146 614 121 583T67 467Q60 445 57 441T43 437H40Z",style:{"stroke-width":"3"}})])])],-1)]))),s[7]||(s[7]=i("mjx-assistive-mml",{unselectable:"on",display:"inline",style:{top:"0px",left:"0px",clip:"rect(1px, 1px, 1px, 1px)","-webkit-touch-callout":"none","-webkit-user-select":"none","-khtml-user-select":"none","-moz-user-select":"none","-ms-user-select":"none","user-select":"none",position:"absolute",padding:"1px 0px 0px 0px",border:"0px",display:"block",width:"auto",overflow:"hidden"}},[i("math",{xmlns:"http://www.w3.org/1998/Math/MathML"},[i("mi",null,"T")])],-1))]),s[11]||(s[11]=a(". Otherwise, the second argument is unspecified."))]),s[14]||(s[14]=l("",1)),h(e,{type:"info",class:"source-link",text:"source"},{default:r(()=>s[12]||(s[12]=[i("a",{href:"https://github.com/thofma/Hecke.jl",target:"_blank",rel:"noreferrer"},"source",-1)])),_:1})])])}const b=k(d,[["render",F]]);export{f as __pageData,b as default};
