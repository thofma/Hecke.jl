import{_ as s,c as l,l as e,a as t,o,a6 as i}from"./chunks/framework.6Ym_72DL.js";const B=JSON.parse('{"title":"","description":"","frontmatter":{},"headers":[],"relativePath":"function_fields/internal.md","filePath":"function_fields/internal.md","lastUpdated":null}'),n={name:"function_fields/internal.md"},a=e("p",null,"Function fields, in Hecke, come in several different types:",-1),r=e("code",null,"RationalFunctionField",-1),d={class:"MathJax",jax:"SVG",style:{direction:"ltr",position:"relative"}},T={style:{overflow:"visible","min-height":"1px","min-width":"1px","vertical-align":"-0.566ex"},xmlns:"http://www.w3.org/2000/svg",width:"4.233ex",height:"2.262ex",role:"img",focusable:"false",viewBox:"0 -750 1871 1000","aria-hidden":"true"},Q=i("",1),c=[Q],h=e("mjx-assistive-mml",{unselectable:"on",display:"inline",style:{top:"0px",left:"0px",clip:"rect(1px, 1px, 1px, 1px)","-webkit-touch-callout":"none","-webkit-user-select":"none","-khtml-user-select":"none","-moz-user-select":"none","-ms-user-select":"none","user-select":"none",position:"absolute",padding:"1px 0px 0px 0px",border:"0px",display:"block",width:"auto",overflow:"hidden"}},[e("math",{xmlns:"http://www.w3.org/1998/Math/MathML"},[e("mi",null,"k"),e("mo",{stretchy:"false"},"("),e("mi",null,"x"),e("mo",{stretchy:"false"},")")])],-1),p={class:"MathJax",jax:"SVG",style:{direction:"ltr",position:"relative"}},m={style:{overflow:"visible","min-height":"1px","min-width":"1px","vertical-align":"-0.025ex"},xmlns:"http://www.w3.org/2000/svg",width:"1.179ex",height:"1.595ex",role:"img",focusable:"false",viewBox:"0 -694 521 705","aria-hidden":"true"},u=e("g",{stroke:"currentColor",fill:"currentColor","stroke-width":"0",transform:"scale(1,-1)"},[e("g",{"data-mml-node":"math"},[e("g",{"data-mml-node":"mi"},[e("path",{"data-c":"1D458",d:"M121 647Q121 657 125 670T137 683Q138 683 209 688T282 694Q294 694 294 686Q294 679 244 477Q194 279 194 272Q213 282 223 291Q247 309 292 354T362 415Q402 442 438 442Q468 442 485 423T503 369Q503 344 496 327T477 302T456 291T438 288Q418 288 406 299T394 328Q394 353 410 369T442 390L458 393Q446 405 434 405H430Q398 402 367 380T294 316T228 255Q230 254 243 252T267 246T293 238T320 224T342 206T359 180T365 147Q365 130 360 106T354 66Q354 26 381 26Q429 26 459 145Q461 153 479 153H483Q499 153 499 144Q499 139 496 130Q455 -11 378 -11Q333 -11 305 15T277 90Q277 108 280 121T283 145Q283 167 269 183T234 206T200 217T182 220H180Q168 178 159 139T145 81T136 44T129 20T122 7T111 -2Q98 -11 83 -11Q66 -11 57 -1T48 16Q48 26 85 176T158 471L195 616Q196 629 188 632T149 637H144Q134 637 131 637T124 640T121 647Z",style:{"stroke-width":"3"}})])])],-1),x=[u],_=e("mjx-assistive-mml",{unselectable:"on",display:"inline",style:{top:"0px",left:"0px",clip:"rect(1px, 1px, 1px, 1px)","-webkit-touch-callout":"none","-webkit-user-select":"none","-khtml-user-select":"none","-moz-user-select":"none","-ms-user-select":"none","user-select":"none",position:"absolute",padding:"1px 0px 0px 0px",border:"0px",display:"block",width:"auto",overflow:"hidden"}},[e("math",{xmlns:"http://www.w3.org/1998/Math/MathML"},[e("mi",null,"k")])],-1),f=e("li",null,[e("p",null,[e("code",null,"FunctionField"),t(": a finite extension of a rational function field given by a polynomial.")])],-1),w=e("p",null,[t("Function fields with the type "),e("code",null,"FunctionField"),t(" are referred to as simple fields in the rest of this document. They are also referred to as being absolute.")],-1),g=e("h2",{id:"Absolute-Simple-Fields",tabindex:"-1"},[t("Absolute Simple Fields "),e("a",{class:"header-anchor",href:"#Absolute-Simple-Fields","aria-label":'Permalink to "Absolute Simple Fields {#Absolute-Simple-Fields}"'},"​")],-1),b=e("code",null,"FunctionField",-1),y={class:"MathJax",jax:"SVG",style:{direction:"ltr",position:"relative"}},k={style:{overflow:"visible","min-height":"1px","min-width":"1px","vertical-align":"-0.025ex"},xmlns:"http://www.w3.org/2000/svg",width:"1.179ex",height:"1.595ex",role:"img",focusable:"false",viewBox:"0 -694 521 705","aria-hidden":"true"},v=e("g",{stroke:"currentColor",fill:"currentColor","stroke-width":"0",transform:"scale(1,-1)"},[e("g",{"data-mml-node":"math"},[e("g",{"data-mml-node":"mi"},[e("path",{"data-c":"1D458",d:"M121 647Q121 657 125 670T137 683Q138 683 209 688T282 694Q294 694 294 686Q294 679 244 477Q194 279 194 272Q213 282 223 291Q247 309 292 354T362 415Q402 442 438 442Q468 442 485 423T503 369Q503 344 496 327T477 302T456 291T438 288Q418 288 406 299T394 328Q394 353 410 369T442 390L458 393Q446 405 434 405H430Q398 402 367 380T294 316T228 255Q230 254 243 252T267 246T293 238T320 224T342 206T359 180T365 147Q365 130 360 106T354 66Q354 26 381 26Q429 26 459 145Q461 153 479 153H483Q499 153 499 144Q499 139 496 130Q455 -11 378 -11Q333 -11 305 15T277 90Q277 108 280 121T283 145Q283 167 269 183T234 206T200 217T182 220H180Q168 178 159 139T145 81T136 44T129 20T122 7T111 -2Q98 -11 83 -11Q66 -11 57 -1T48 16Q48 26 85 176T158 471L195 616Q196 629 188 632T149 637H144Q134 637 131 637T124 640T121 647Z",style:{"stroke-width":"3"}})])])],-1),H=[v],M=e("mjx-assistive-mml",{unselectable:"on",display:"inline",style:{top:"0px",left:"0px",clip:"rect(1px, 1px, 1px, 1px)","-webkit-touch-callout":"none","-webkit-user-select":"none","-khtml-user-select":"none","-moz-user-select":"none","-ms-user-select":"none","user-select":"none",position:"absolute",padding:"1px 0px 0px 0px",border:"0px",display:"block",width:"auto",overflow:"hidden"}},[e("math",{xmlns:"http://www.w3.org/1998/Math/MathML"},[e("mi",null,"k")])],-1);function A(F,L,S,j,C,V){return o(),l("div",null,[a,e("ul",null,[e("li",null,[e("p",null,[r,t(": a field of the form "),e("mjx-container",d,[(o(),l("svg",T,c)),h]),t(" for a field "),e("mjx-container",p,[(o(),l("svg",m,x)),_]),t(".")])]),f]),w,g,e("p",null,[t("Internally function fields of type "),b,t(" are essentially represented as a unvariate quotient with the arithmetic provided by the AbstractAlgebra and Nemo packages. As they are defined generically for all AbstractAlgebra, Nemo and Hecke fields "),e("mjx-container",y,[(o(),l("svg",k,H)),M]),t(" the function field type is implemented in AbstractAlgebra.")])])}const D=s(n,[["render",A]]);export{B as __pageData,D as default};
