import{_ as s,c as a,o as e,j as Q,a as T,az as l}from"./chunks/framework.CE5HjQlj.js";const M=JSON.parse('{"title":"Introduction","description":"","frontmatter":{},"headers":[],"relativePath":"manual/elliptic_curves/intro.md","filePath":"manual/elliptic_curves/intro.md","lastUpdated":null}'),n={name:"manual/elliptic_curves/intro.md"},o={class:"MathJax",jax:"SVG",style:{direction:"ltr",position:"relative"}},m={style:{overflow:"visible","min-height":"1px","min-width":"1px","vertical-align":"0"},xmlns:"http://www.w3.org/2000/svg",width:"1.729ex",height:"1.538ex",role:"img",focusable:"false",viewBox:"0 -680 764 680","aria-hidden":"true"},d={class:"MathJax",jax:"SVG",display:"true",style:{direction:"ltr",display:"block","text-align":"center",margin:"1em 0",position:"relative"}},r={style:{overflow:"visible","min-height":"1px","min-width":"1px","vertical-align":"-0.464ex"},xmlns:"http://www.w3.org/2000/svg",width:"39.233ex",height:"2.464ex",role:"img",focusable:"false",viewBox:"0 -883.9 17341.2 1088.9","aria-hidden":"true"},i={class:"MathJax",jax:"SVG",style:{direction:"ltr",position:"relative"}},p={style:{overflow:"visible","min-height":"1px","min-width":"1px","vertical-align":"-0.375ex"},xmlns:"http://www.w3.org/2000/svg",width:"16.736ex",height:"1.881ex",role:"img",focusable:"false",viewBox:"0 -666 7397.3 831.6","aria-hidden":"true"},h={class:"MathJax",jax:"SVG",display:"true",style:{direction:"ltr",display:"block","text-align":"center",margin:"1em 0",position:"relative"}},u={style:{overflow:"visible","min-height":"1px","min-width":"1px","vertical-align":"-0.464ex"},xmlns:"http://www.w3.org/2000/svg",width:"18.59ex",height:"2.464ex",role:"img",focusable:"false",viewBox:"0 -883.9 8216.7 1088.9","aria-hidden":"true"};function g(H,t,c,w,x,V){return e(),a("div",null,[t[15]||(t[15]=Q("h1",{id:"introduction",tabindex:"-1"},[T("Introduction "),Q("a",{class:"header-anchor",href:"#introduction","aria-label":'Permalink to "Introduction"'},"​")],-1)),t[16]||(t[16]=Q("p",null,"This chapter deals with functionality for elliptic curves, which is available over arbitrary fields, with specific features available for curves over the rationals and number fields, and finite fields.",-1)),Q("p",null,[t[2]||(t[2]=T("An elliptic curve ")),Q("mjx-container",o,[(e(),a("svg",m,t[0]||(t[0]=[Q("g",{stroke:"currentColor",fill:"currentColor","stroke-width":"0",transform:"scale(1,-1)"},[Q("g",{"data-mml-node":"math"},[Q("g",{"data-mml-node":"mi"},[Q("path",{"data-c":"1D438",d:"M492 213Q472 213 472 226Q472 230 477 250T482 285Q482 316 461 323T364 330H312Q311 328 277 192T243 52Q243 48 254 48T334 46Q428 46 458 48T518 61Q567 77 599 117T670 248Q680 270 683 272Q690 274 698 274Q718 274 718 261Q613 7 608 2Q605 0 322 0H133Q31 0 31 11Q31 13 34 25Q38 41 42 43T65 46Q92 46 125 49Q139 52 144 61Q146 66 215 342T285 622Q285 629 281 629Q273 632 228 634H197Q191 640 191 642T193 659Q197 676 203 680H757Q764 676 764 669Q764 664 751 557T737 447Q735 440 717 440H705Q698 445 698 453L701 476Q704 500 704 528Q704 558 697 578T678 609T643 625T596 632T532 634H485Q397 633 392 631Q388 629 386 622Q385 619 355 499T324 377Q347 376 372 376H398Q464 376 489 391T534 472Q538 488 540 490T557 493Q562 493 565 493T570 492T572 491T574 487T577 483L544 351Q511 218 508 216Q505 213 492 213Z",style:{"stroke-width":"3"}})])])],-1)]))),t[1]||(t[1]=Q("mjx-assistive-mml",{unselectable:"on",display:"inline",style:{top:"0px",left:"0px",clip:"rect(1px, 1px, 1px, 1px)","-webkit-touch-callout":"none","-webkit-user-select":"none","-khtml-user-select":"none","-moz-user-select":"none","-ms-user-select":"none","user-select":"none",position:"absolute",padding:"1px 0px 0px 0px",border:"0px",display:"block",width:"auto",overflow:"hidden"}},[Q("math",{xmlns:"http://www.w3.org/1998/Math/MathML"},[Q("mi",null,"E")])],-1))]),t[3]||(t[3]=T(" is the projective closure of the curve given by the ")),t[4]||(t[4]=Q("em",null,"Weierstrass equation",-1))]),Q("mjx-container",d,[(e(),a("svg",r,t[5]||(t[5]=[l("",1)]))),t[6]||(t[6]=Q("mjx-assistive-mml",{unselectable:"on",display:"block",style:{top:"0px",left:"0px",clip:"rect(1px, 1px, 1px, 1px)","-webkit-touch-callout":"none","-webkit-user-select":"none","-khtml-user-select":"none","-moz-user-select":"none","-ms-user-select":"none","user-select":"none",position:"absolute",padding:"1px 0px 0px 0px",border:"0px",display:"block",overflow:"hidden",width:"100%"}},[Q("math",{xmlns:"http://www.w3.org/1998/Math/MathML",display:"block"},[Q("msup",null,[Q("mi",null,"y"),Q("mn",null,"2")]),Q("mo",null,"+"),Q("msub",null,[Q("mi",null,"a"),Q("mn",null,"1")]),Q("mi",null,"x"),Q("mi",null,"y"),Q("mo",null,"+"),Q("msub",null,[Q("mi",null,"a"),Q("mn",null,"3")]),Q("mi",null,"y"),Q("mo",null,"="),Q("msup",null,[Q("mi",null,"x"),Q("mn",null,"3")]),Q("mo",null,"+"),Q("msub",null,[Q("mi",null,"a"),Q("mn",null,"2")]),Q("msup",null,[Q("mi",null,"x"),Q("mn",null,"2")]),Q("mo",null,"+"),Q("msub",null,[Q("mi",null,"a"),Q("mn",null,"4")]),Q("mi",null,"x"),Q("mo",null,"+"),Q("msub",null,[Q("mi",null,"a"),Q("mn",null,"6")])])],-1))]),Q("p",null,[t[9]||(t[9]=T("specified by the list of coefficients ")),t[10]||(t[10]=Q("code",null,"[a1, a2, a3, a4, a6]",-1)),t[11]||(t[11]=T(". If ")),Q("mjx-container",i,[(e(),a("svg",p,t[7]||(t[7]=[l("",1)]))),t[8]||(t[8]=Q("mjx-assistive-mml",{unselectable:"on",display:"inline",style:{top:"0px",left:"0px",clip:"rect(1px, 1px, 1px, 1px)","-webkit-touch-callout":"none","-webkit-user-select":"none","-khtml-user-select":"none","-moz-user-select":"none","-ms-user-select":"none","user-select":"none",position:"absolute",padding:"1px 0px 0px 0px",border:"0px",display:"block",width:"auto",overflow:"hidden"}},[Q("math",{xmlns:"http://www.w3.org/1998/Math/MathML"},[Q("msub",null,[Q("mi",null,"a"),Q("mn",null,"1")]),Q("mo",null,"="),Q("msub",null,[Q("mi",null,"a"),Q("mn",null,"2")]),Q("mo",null,"="),Q("msub",null,[Q("mi",null,"a"),Q("mn",null,"3")]),Q("mo",null,"="),Q("mn",null,"0")])],-1))]),t[12]||(t[12]=T(", this simplifies to"))]),Q("mjx-container",h,[(e(),a("svg",u,t[13]||(t[13]=[l("",1)]))),t[14]||(t[14]=Q("mjx-assistive-mml",{unselectable:"on",display:"block",style:{top:"0px",left:"0px",clip:"rect(1px, 1px, 1px, 1px)","-webkit-touch-callout":"none","-webkit-user-select":"none","-khtml-user-select":"none","-moz-user-select":"none","-ms-user-select":"none","user-select":"none",position:"absolute",padding:"1px 0px 0px 0px",border:"0px",display:"block",overflow:"hidden",width:"100%"}},[Q("math",{xmlns:"http://www.w3.org/1998/Math/MathML",display:"block"},[Q("msup",null,[Q("mi",null,"y"),Q("mn",null,"2")]),Q("mo",null,"="),Q("msup",null,[Q("mi",null,"x"),Q("mn",null,"3")]),Q("mo",null,"+"),Q("msub",null,[Q("mi",null,"a"),Q("mn",null,"4")]),Q("mi",null,"x"),Q("mo",null,"+"),Q("msub",null,[Q("mi",null,"a"),Q("mn",null,"6")])])],-1))]),t[17]||(t[17]=Q("p",null,[T("which we refer to as a "),Q("em",null,"short Weierstrass equation"),T(" and which is specified by the two element list "),Q("code",null,"[a4, a6]"),T(".")],-1))])}const y=s(n,[["render",g]]);export{M as __pageData,y as default};
