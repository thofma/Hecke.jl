import{_ as k,C as r,c as p,o as h,az as l,j as i,G as t,a,w as e}from"./chunks/framework.1KlXKLck.js";const M=JSON.parse('{"title":"Multi-sets and sub-set iterators","description":"","frontmatter":{},"headers":[],"relativePath":"manual/misc/mset.md","filePath":"manual/misc/mset.md","lastUpdated":null}'),d={name:"manual/misc/mset.md"},g={class:"jldocstring custom-block",open:""},E={class:"jldocstring custom-block",open:""},o={class:"MathJax",jax:"SVG",style:{direction:"ltr",position:"relative"}},F={style:{overflow:"visible","min-height":"1px","min-width":"1px","vertical-align":"0"},xmlns:"http://www.w3.org/2000/svg",width:"1.131ex",height:"1.507ex",role:"img",focusable:"false",viewBox:"0 -666 500 666","aria-hidden":"true"},y={class:"MathJax",jax:"SVG",style:{direction:"ltr",position:"relative"}},c={style:{overflow:"visible","min-height":"1px","min-width":"1px","vertical-align":"-0.05ex"},xmlns:"http://www.w3.org/2000/svg",width:"1.131ex",height:"1.557ex",role:"img",focusable:"false",viewBox:"0 -666 500 688","aria-hidden":"true"},C={class:"jldocstring custom-block",open:""},u={class:"jldocstring custom-block",open:""},m={class:"jldocstring custom-block",open:""},B={class:"jldocstring custom-block",open:""},b={class:"jldocstring custom-block",open:""},A={class:"jldocstring custom-block",open:""};function T(f,s,D,v,S,j){const n=r("Badge");return h(),p("div",null,[s[53]||(s[53]=l("",4)),i("details",g,[i("summary",null,[s[0]||(s[0]=i("a",{id:"MSet",href:"#MSet"},[i("span",{class:"jlbinding"},"MSet")],-1)),s[1]||(s[1]=a()),t(n,{type:"info",class:"jlObjectType jlType",text:"Type"})]),s[3]||(s[3]=l("",5)),t(n,{type:"info",class:"source-link",text:"source"},{default:e(()=>s[2]||(s[2]=[i("a",{href:"https://github.com/thofma/Hecke.jl",target:"_blank",rel:"noreferrer"},"source",-1)])),_:1})]),s[54]||(s[54]=i("p",null,"We can create multi-sets from any finite iterator, dictionary or pair of lists with the appropriate conditions.",-1)),i("details",E,[i("summary",null,[s[4]||(s[4]=i("a",{id:"multiset",href:"#multiset"},[i("span",{class:"jlbinding"},"multiset")],-1)),s[5]||(s[5]=a()),t(n,{type:"info",class:"jlObjectType jlFunction",text:"Function"})]),s[8]||(s[8]=l("",6)),t(n,{type:"info",class:"source-link",text:"source"},{default:e(()=>s[6]||(s[6]=[i("a",{href:"https://github.com/thofma/Hecke.jl",target:"_blank",rel:"noreferrer"},"source",-1)])),_:1}),s[9]||(s[9]=l("",4)),t(n,{type:"info",class:"source-link",text:"source"},{default:e(()=>s[7]||(s[7]=[i("a",{href:"https://github.com/thofma/Hecke.jl",target:"_blank",rel:"noreferrer"},"source",-1)])),_:1})]),s[55]||(s[55]=l("",3)),i("p",null,[s[14]||(s[14]=l("",21)),i("mjx-container",o,[(h(),p("svg",F,s[10]||(s[10]=[i("g",{stroke:"currentColor",fill:"currentColor","stroke-width":"0",transform:"scale(1,-1)"},[i("g",{"data-mml-node":"math"},[i("g",{"data-mml-node":"mn"},[i("path",{"data-c":"31",d:"M213 578L200 573Q186 568 160 563T102 556H83V602H102Q149 604 189 617T245 641T273 663Q275 666 285 666Q294 666 302 660V361L303 61Q310 54 315 52T339 48T401 46H427V0H416Q395 3 257 3Q121 3 100 0H88V46H114Q136 46 152 46T177 47T193 50T201 52T207 57T213 61V578Z",style:{"stroke-width":"3"}})])])],-1)]))),s[11]||(s[11]=i("mjx-assistive-mml",{unselectable:"on",display:"inline",style:{top:"0px",left:"0px",clip:"rect(1px, 1px, 1px, 1px)","-webkit-touch-callout":"none","-webkit-user-select":"none","-khtml-user-select":"none","-moz-user-select":"none","-ms-user-select":"none","user-select":"none",position:"absolute",padding:"1px 0px 0px 0px",border:"0px",display:"block",width:"auto",overflow:"hidden"}},[i("math",{xmlns:"http://www.w3.org/1998/Math/MathML"},[i("mn",null,"1")])],-1))]),s[15]||(s[15]=a(". Much stronger, ")),s[16]||(s[16]=i("code",null,"delete!(M, x)",-1)),s[17]||(s[17]=a(" will remove ")),s[18]||(s[18]=i("em",null,"all",-1)),s[19]||(s[19]=a(" instances of ")),s[20]||(s[20]=i("code",null,"x",-1)),s[21]||(s[21]=a(" in ")),s[22]||(s[22]=i("code",null,"M",-1)),s[23]||(s[23]=a(" and so ")),s[24]||(s[24]=i("code",null,"multiplicity(M, x)",-1)),s[25]||(s[25]=a(" will be ")),i("mjx-container",y,[(h(),p("svg",c,s[12]||(s[12]=[i("g",{stroke:"currentColor",fill:"currentColor","stroke-width":"0",transform:"scale(1,-1)"},[i("g",{"data-mml-node":"math"},[i("g",{"data-mml-node":"mn"},[i("path",{"data-c":"30",d:"M96 585Q152 666 249 666Q297 666 345 640T423 548Q460 465 460 320Q460 165 417 83Q397 41 362 16T301 -15T250 -22Q224 -22 198 -16T137 16T82 83Q39 165 39 320Q39 494 96 585ZM321 597Q291 629 250 629Q208 629 178 597Q153 571 145 525T137 333Q137 175 145 125T181 46Q209 16 250 16Q290 16 318 46Q347 76 354 130T362 333Q362 478 354 524T321 597Z",style:{"stroke-width":"3"}})])])],-1)]))),s[13]||(s[13]=i("mjx-assistive-mml",{unselectable:"on",display:"inline",style:{top:"0px",left:"0px",clip:"rect(1px, 1px, 1px, 1px)","-webkit-touch-callout":"none","-webkit-user-select":"none","-khtml-user-select":"none","-moz-user-select":"none","-ms-user-select":"none","user-select":"none",position:"absolute",padding:"1px 0px 0px 0px",border:"0px",display:"block",width:"auto",overflow:"hidden"}},[i("math",{xmlns:"http://www.w3.org/1998/Math/MathML"},[i("mn",null,"0")])],-1))]),s[26]||(s[26]=a("."))]),s[56]||(s[56]=i("p",null,[a("While "),i("code",null,"unique"),a(" will return the keys of the underlying dictionary, one can access the values (i.e. the multiplicities of the elements in the multi-set) via the following functions:")],-1)),i("details",C,[i("summary",null,[s[27]||(s[27]=i("a",{id:"multiplicities-Tuple{MSet}",href:"#multiplicities-Tuple{MSet}"},[i("span",{class:"jlbinding"},"multiplicities")],-1)),s[28]||(s[28]=a()),t(n,{type:"info",class:"jlObjectType jlMethod",text:"Method"})]),s[30]||(s[30]=l("",4)),t(n,{type:"info",class:"source-link",text:"source"},{default:e(()=>s[29]||(s[29]=[i("a",{href:"https://github.com/thofma/Hecke.jl",target:"_blank",rel:"noreferrer"},"source",-1)])),_:1})]),i("details",u,[i("summary",null,[s[31]||(s[31]=i("a",{id:"multiplicity-Union{Tuple{T}, Tuple{MSet{T}, T}} where T",href:"#multiplicity-Union{Tuple{T}, Tuple{MSet{T}, T}} where T"},[i("span",{class:"jlbinding"},"multiplicity")],-1)),s[32]||(s[32]=a()),t(n,{type:"info",class:"jlObjectType jlMethod",text:"Method"})]),s[34]||(s[34]=l("",4)),t(n,{type:"info",class:"source-link",text:"source"},{default:e(()=>s[33]||(s[33]=[i("a",{href:"https://github.com/thofma/Hecke.jl",target:"_blank",rel:"noreferrer"},"source",-1)])),_:1})]),s[57]||(s[57]=i("p",null,[a("Finally, the sum and difference for "),i("code",null,"MSet"),a(" are also available. Difference is given by the complements of sets and the sum is given by disjoint union of sets.")],-1)),i("details",m,[i("summary",null,[s[35]||(s[35]=i("a",{id:"+-Tuple{MSet, MSet}",href:"#+-Tuple{MSet, MSet}"},[i("span",{class:"jlbinding"},"+")],-1)),s[36]||(s[36]=a()),t(n,{type:"info",class:"jlObjectType jlMethod",text:"Method"})]),s[38]||(s[38]=l("",4)),t(n,{type:"info",class:"source-link",text:"source"},{default:e(()=>s[37]||(s[37]=[i("a",{href:"https://github.com/thofma/Hecke.jl",target:"_blank",rel:"noreferrer"},"source",-1)])),_:1})]),i("details",B,[i("summary",null,[s[39]||(s[39]=i("a",{id:"--Tuple{MSet, Vararg{MSet}}",href:"#--Tuple{MSet, Vararg{MSet}}"},[i("span",{class:"jlbinding"},"-")],-1)),s[40]||(s[40]=a()),t(n,{type:"info",class:"jlObjectType jlMethod",text:"Method"})]),s[42]||(s[42]=l("",5)),t(n,{type:"info",class:"source-link",text:"source"},{default:e(()=>s[41]||(s[41]=[i("a",{href:"https://github.com/thofma/Hecke.jl",target:"_blank",rel:"noreferrer"},"source",-1)])),_:1})]),s[58]||(s[58]=i("h2",{id:"Subset-iterators-for-sets-and-multisets",tabindex:"-1"},[a("Subset iterators for sets and multisets "),i("a",{class:"header-anchor",href:"#Subset-iterators-for-sets-and-multisets","aria-label":'Permalink to "Subset iterators for sets and multisets {#Subset-iterators-for-sets-and-multisets}"'},"​")],-1)),i("details",b,[i("summary",null,[s[43]||(s[43]=i("a",{id:"subsets-Union{Tuple{MSet{T}}, Tuple{T}} where T",href:"#subsets-Union{Tuple{MSet{T}}, Tuple{T}} where T"},[i("span",{class:"jlbinding"},"subsets")],-1)),s[44]||(s[44]=a()),t(n,{type:"info",class:"jlObjectType jlMethod",text:"Method"})]),s[47]||(s[47]=l("",2)),t(n,{type:"info",class:"source-link",text:"source"},{default:e(()=>s[45]||(s[45]=[i("a",{href:"https://github.com/thofma/Hecke.jl",target:"_blank",rel:"noreferrer"},"source",-1)])),_:1}),s[48]||(s[48]=l("",2)),t(n,{type:"info",class:"source-link",text:"source"},{default:e(()=>s[46]||(s[46]=[i("a",{href:"https://github.com/thofma/Hecke.jl",target:"_blank",rel:"noreferrer"},"source",-1)])),_:1})]),s[59]||(s[59]=i("h3",{id:"Sub-sets-of-a-given-size",tabindex:"-1"},[a("Sub-sets of a given size "),i("a",{class:"header-anchor",href:"#Sub-sets-of-a-given-size","aria-label":'Permalink to "Sub-sets of a given size {#Sub-sets-of-a-given-size}"'},"​")],-1)),i("details",A,[i("summary",null,[s[49]||(s[49]=i("a",{id:"subsets-Union{Tuple{T}, Tuple{Set{T}, Int64}} where T",href:"#subsets-Union{Tuple{T}, Tuple{Set{T}, Int64}} where T"},[i("span",{class:"jlbinding"},"subsets")],-1)),s[50]||(s[50]=a()),t(n,{type:"info",class:"jlObjectType jlMethod",text:"Method"})]),s[52]||(s[52]=l("",2)),t(n,{type:"info",class:"source-link",text:"source"},{default:e(()=>s[51]||(s[51]=[i("a",{href:"https://github.com/thofma/Hecke.jl",target:"_blank",rel:"noreferrer"},"source",-1)])),_:1})])])}const _=k(d,[["render",T]]);export{M as __pageData,_ as default};
