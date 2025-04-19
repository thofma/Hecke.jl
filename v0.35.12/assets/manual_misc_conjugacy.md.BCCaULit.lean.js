import{_ as h,C as k,c as t,o as n,j as s,a,az as l,G as p}from"./chunks/framework.CcMML7AC.js";const B=JSON.parse('{"title":"Conjugacy of integral matrices","description":"","frontmatter":{},"headers":[],"relativePath":"manual/misc/conjugacy.md","filePath":"manual/misc/conjugacy.md","lastUpdated":null}'),r={name:"manual/misc/conjugacy.md"},d={class:"jldocstring custom-block",open:""},E={class:"MathJax",jax:"SVG",style:{direction:"ltr",position:"relative"}},o={style:{overflow:"visible","min-height":"1px","min-width":"1px","vertical-align":"0"},xmlns:"http://www.w3.org/2000/svg",width:"1.593ex",height:"1.532ex",role:"img",focusable:"false",viewBox:"0 -677 704 677","aria-hidden":"true"},g={class:"MathJax",jax:"SVG",style:{direction:"ltr",position:"relative"}},Q={style:{overflow:"visible","min-height":"1px","min-width":"1px","vertical-align":"-0.186ex"},xmlns:"http://www.w3.org/2000/svg",width:"9.617ex",height:"1.805ex",role:"img",focusable:"false",viewBox:"0 -716 4250.6 798","aria-hidden":"true"},y={class:"MathJax",jax:"SVG",style:{direction:"ltr",position:"relative"}},m={style:{overflow:"visible","min-height":"1px","min-width":"1px","vertical-align":"0"},xmlns:"http://www.w3.org/2000/svg",width:"1.593ex",height:"1.532ex",role:"img",focusable:"false",viewBox:"0 -677 704 677","aria-hidden":"true"};function C(F,i,c,T,u,x){const e=k("Badge");return n(),t("div",null,[i[14]||(i[14]=s("h1",{id:"Conjugacy-of-integral-matrices",tabindex:"-1"},[a("Conjugacy of integral matrices "),s("a",{class:"header-anchor",href:"#Conjugacy-of-integral-matrices","aria-label":'Permalink to "Conjugacy of integral matrices {#Conjugacy-of-integral-matrices}"'},"​")],-1)),s("details",d,[s("summary",null,[i[0]||(i[0]=s("a",{id:"is_GLZ_conjugate-Tuple{ZZMatrix, ZZMatrix}",href:"#is_GLZ_conjugate-Tuple{ZZMatrix, ZZMatrix}"},[s("span",{class:"jlbinding"},"is_GLZ_conjugate")],-1)),i[1]||(i[1]=a()),p(e,{type:"info",class:"jlObjectType jlMethod",text:"Method"})]),i[12]||(i[12]=l("",1)),s("p",null,[i[8]||(i[8]=a("Given two integral or rational matrices, determine whether there exists an invertible integral matrix ")),s("mjx-container",E,[(n(),t("svg",o,i[2]||(i[2]=[s("g",{stroke:"currentColor",fill:"currentColor","stroke-width":"0",transform:"scale(1,-1)"},[s("g",{"data-mml-node":"math"},[s("g",{"data-mml-node":"mi"},[s("path",{"data-c":"1D447",d:"M40 437Q21 437 21 445Q21 450 37 501T71 602L88 651Q93 669 101 677H569H659Q691 677 697 676T704 667Q704 661 687 553T668 444Q668 437 649 437Q640 437 637 437T631 442L629 445Q629 451 635 490T641 551Q641 586 628 604T573 629Q568 630 515 631Q469 631 457 630T439 622Q438 621 368 343T298 60Q298 48 386 46Q418 46 427 45T436 36Q436 31 433 22Q429 4 424 1L422 0Q419 0 415 0Q410 0 363 1T228 2Q99 2 64 0H49Q43 6 43 9T45 27Q49 40 55 46H83H94Q174 46 189 55Q190 56 191 56Q196 59 201 76T241 233Q258 301 269 344Q339 619 339 625Q339 630 310 630H279Q212 630 191 624Q146 614 121 583T67 467Q60 445 57 441T43 437H40Z",style:{"stroke-width":"3"}})])])],-1)]))),i[3]||(i[3]=s("mjx-assistive-mml",{unselectable:"on",display:"inline",style:{top:"0px",left:"0px",clip:"rect(1px, 1px, 1px, 1px)","-webkit-touch-callout":"none","-webkit-user-select":"none","-khtml-user-select":"none","-moz-user-select":"none","-ms-user-select":"none","user-select":"none",position:"absolute",padding:"1px 0px 0px 0px",border:"0px",display:"block",width:"auto",overflow:"hidden"}},[s("math",{xmlns:"http://www.w3.org/1998/Math/MathML"},[s("mi",null,"T")])],-1))]),i[9]||(i[9]=a(" with ")),s("mjx-container",g,[(n(),t("svg",Q,i[4]||(i[4]=[l("",1)]))),i[5]||(i[5]=s("mjx-assistive-mml",{unselectable:"on",display:"inline",style:{top:"0px",left:"0px",clip:"rect(1px, 1px, 1px, 1px)","-webkit-touch-callout":"none","-webkit-user-select":"none","-khtml-user-select":"none","-moz-user-select":"none","-ms-user-select":"none","user-select":"none",position:"absolute",padding:"1px 0px 0px 0px",border:"0px",display:"block",width:"auto",overflow:"hidden"}},[s("math",{xmlns:"http://www.w3.org/1998/Math/MathML"},[s("mi",null,"T"),s("mi",null,"A"),s("mo",null,"="),s("mi",null,"B"),s("mi",null,"T")])],-1))]),i[10]||(i[10]=a(". If true, the second argument is such a matrix ")),s("mjx-container",y,[(n(),t("svg",m,i[6]||(i[6]=[s("g",{stroke:"currentColor",fill:"currentColor","stroke-width":"0",transform:"scale(1,-1)"},[s("g",{"data-mml-node":"math"},[s("g",{"data-mml-node":"mi"},[s("path",{"data-c":"1D447",d:"M40 437Q21 437 21 445Q21 450 37 501T71 602L88 651Q93 669 101 677H569H659Q691 677 697 676T704 667Q704 661 687 553T668 444Q668 437 649 437Q640 437 637 437T631 442L629 445Q629 451 635 490T641 551Q641 586 628 604T573 629Q568 630 515 631Q469 631 457 630T439 622Q438 621 368 343T298 60Q298 48 386 46Q418 46 427 45T436 36Q436 31 433 22Q429 4 424 1L422 0Q419 0 415 0Q410 0 363 1T228 2Q99 2 64 0H49Q43 6 43 9T45 27Q49 40 55 46H83H94Q174 46 189 55Q190 56 191 56Q196 59 201 76T241 233Q258 301 269 344Q339 619 339 625Q339 630 310 630H279Q212 630 191 624Q146 614 121 583T67 467Q60 445 57 441T43 437H40Z",style:{"stroke-width":"3"}})])])],-1)]))),i[7]||(i[7]=s("mjx-assistive-mml",{unselectable:"on",display:"inline",style:{top:"0px",left:"0px",clip:"rect(1px, 1px, 1px, 1px)","-webkit-touch-callout":"none","-webkit-user-select":"none","-khtml-user-select":"none","-moz-user-select":"none","-ms-user-select":"none","user-select":"none",position:"absolute",padding:"1px 0px 0px 0px",border:"0px",display:"block",width:"auto",overflow:"hidden"}},[s("math",{xmlns:"http://www.w3.org/1998/Math/MathML"},[s("mi",null,"T")])],-1))]),i[11]||(i[11]=a(". Otherwise, the second argument is unspecified."))]),i[13]||(i[13]=l("",2))])])}const f=h(r,[["render",C]]);export{B as __pageData,f as default};
