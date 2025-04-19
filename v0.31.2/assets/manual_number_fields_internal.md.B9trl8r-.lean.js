import{_ as n,c as t,l as e,a as l,a6 as s,o as i}from"./chunks/framework.BUCQO1mN.js";const V=JSON.parse('{"title":"Internals","description":"","frontmatter":{},"headers":[],"relativePath":"manual/number_fields/internal.md","filePath":"manual/number_fields/internal.md","lastUpdated":null}'),a={name:"manual/number_fields/internal.md"},o=e("h1",{id:"Internals",tabindex:"-1"},[l("Internals "),e("a",{class:"header-anchor",href:"#Internals","aria-label":'Permalink to "Internals {#Internals}"'},"​")],-1),d=e("h2",{id:"Types-of-number-fields",tabindex:"-1"},[l("Types of number fields "),e("a",{class:"header-anchor",href:"#Types-of-number-fields","aria-label":'Permalink to "Types of number fields {#Types-of-number-fields}"'},"​")],-1),r=e("p",null,"Number fields, in Hecke, come in several different types:",-1),m=e("code",null,"AbsSimpleNumField",-1),c={class:"MathJax",jax:"SVG",style:{direction:"ltr",position:"relative"}},p={style:{overflow:"visible","min-height":"1px","min-width":"1px","vertical-align":"-0.437ex"},xmlns:"http://www.w3.org/2000/svg",width:"1.955ex",height:"2.011ex",role:"img",focusable:"false",viewBox:"0 -696 864 889","aria-hidden":"true"},h=s("",1),u=[h],_=e("mjx-assistive-mml",{unselectable:"on",display:"inline",style:{top:"0px",left:"0px",clip:"rect(1px, 1px, 1px, 1px)","-webkit-touch-callout":"none","-webkit-user-select":"none","-khtml-user-select":"none","-moz-user-select":"none","-ms-user-select":"none","user-select":"none",position:"absolute",padding:"1px 0px 0px 0px",border:"0px",display:"block",width:"auto",overflow:"hidden"}},[e("math",{xmlns:"http://www.w3.org/1998/Math/MathML"},[e("mrow",{"data-mjx-texclass":"ORD"},[e("mi",{mathvariant:"bold"},"Q")])])],-1),f=e("code",null,"AbsNonSimpleNumField",-1),T={class:"MathJax",jax:"SVG",style:{direction:"ltr",position:"relative"}},x={style:{overflow:"visible","min-height":"1px","min-width":"1px","vertical-align":"-0.437ex"},xmlns:"http://www.w3.org/2000/svg",width:"1.955ex",height:"2.011ex",role:"img",focusable:"false",viewBox:"0 -696 864 889","aria-hidden":"true"},Q=s("",1),b=[Q],w=e("mjx-assistive-mml",{unselectable:"on",display:"inline",style:{top:"0px",left:"0px",clip:"rect(1px, 1px, 1px, 1px)","-webkit-touch-callout":"none","-webkit-user-select":"none","-khtml-user-select":"none","-moz-user-select":"none","-ms-user-select":"none","user-select":"none",position:"absolute",padding:"1px 0px 0px 0px",border:"0px",display:"block",width:"auto",overflow:"hidden"}},[e("math",{xmlns:"http://www.w3.org/1998/Math/MathML"},[e("mrow",{"data-mjx-texclass":"ORD"},[e("mi",{mathvariant:"bold"},"Q")])])],-1),g=e("li",null,[e("p",null,[e("code",null,"RelSimpleNumField"),l(": a finite simple extension of a number field. This is actually parametried by the (element) type of the coefficient field. The complete type of an extension of an absolute field ("),e("code",null,"AbsSimpleNumField"),l(") is "),e("code",null,"RelSimpleNumField{AbsSimpleNumFieldElem}"),l(". The next extension thus will be "),e("code",null,"RelSimpleNumField{RelSimpleNumFieldElem{AbsSimpleNumFieldElem}}"),l(".")])],-1),y=e("li",null,[e("p",null,[e("code",null,"RelNonSimpleNumField"),l(": extensions of number fields given by several polynomials. This too will be referred to as a non-simple field.")])],-1),v=s("",4);function N(S,A,k,F,I,R){return i(),t("div",null,[o,d,r,e("ul",null,[e("li",null,[e("p",null,[m,l(": a finite simple extension of the rational numbers "),e("mjx-container",c,[(i(),t("svg",p,u)),_])])]),e("li",null,[e("p",null,[f,l(": a finite extension of "),e("mjx-container",T,[(i(),t("svg",x,b)),w]),l(" given by several polynomials. We will refer to this as a non-simple field - even though mathematically we can find a primitive elements.")])]),g,y]),v])}const j=n(a,[["render",N]]);export{V as __pageData,j as default};
