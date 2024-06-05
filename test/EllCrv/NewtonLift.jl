R,x = polynomial_ring(QQ,:x)
fw = x^6 - 2*x^5 + 2*x^4 - 3*x^3 + 2*x^2 - 2*x + 1
fx = x^12 - 3*x^11 + x^10 + 7*x^9 - 8*x^8 - 4*x^7 + 13*x^6 - 4*x^5 - 8*x^4 + 7*x^3 + x^2 - 3*x + 1
F,z  = number_field(fx, :z)
Ftp = polynomial_ring(F,'t')[1]
Ft = fraction_field(Ftp)
t = gen(Ft)
w = z^11 - z^10 - 3*z^9 + 4*z^8 + 5*z^7 - 6*z^6 - 2*z^5 + 7*z^4 + z^3 - 4*z^2 + z + 2
zeta7 = 2*z^11 - 4*z^10 - 3*z^9 + 14*z^8 - 4*z^7 - 16*z^6 + 16*z^5 + 8*z^4 - 14*z^3 + 2*z^2 + 6*z - 2

@assert minpoly(w)==fw
@assert minpoly(zeta7) == x^6 + x^5 + x^4 + x^3 + x^2 + x + 1

OF = maximal_order(F)
p29 = ideal(OF, OF.([29,z+12]))
gens(p29) # fixes a bug
@assert is_prime(p29)
kF, OFtokF = residue_field(OF, p29)
FtokF = extend(OFtokF, F)

kFtp,_ = polynomial_ring(kF,"t")
kFt = fraction_field(kFtp)

FttokFt = map_from_func(x->kFt(map_coefficients(FtokF,numerator(x);parent=kFtp), map_coefficients(FtokF, denominator(x), ;parent=kFtp)), Ft, kFt)


ainvs = Ft.([0,
 0,
 0,
 (-486*z^11 + 1620*z^10 - 513*z^9 - 3888*z^8 + 4077*z^7 + 2565*z^6 - 5616*z^5 + 1269*z^4 + 3591*z^3 - 1620*z^2 - 675*z + 567)*t^8 + (-6696*z^11 + 17712*z^10 + 432*z^9 - 44712*z^8 + 30024*z^7 + 36720*z^6 - 53352*z^5 - 2808*z^4 + 39960*z^3 - 10800*z^2 - 10368*z + 7344)*t^7 + (-2808*z^11 + 10044*z^10 - 17172*z^9 - 1080*z^8 + 52488*z^7 - 64044*z^6 - 29484*z^5 + 84024*z^4 - 35208*z^3 - 37044*z^2 + 32076*z + 5832)*t^6 + (-11016*z^11 + 48384*z^10 - 63288*z^9 - 65664*z^8 + 222696*z^7 - 81648*z^6 - 238248*z^5 + 201960*z^4 + 56376*z^3 - 164592*z^2 + 7560*z + 45360)*t^5 + (-12690*z^11 + 93150*z^10 - 118260*z^9 - 171990*z^8 + 411750*z^7 + 44280*z^6 - 487890*z^5 + 222750*z^4 + 287820*z^3 - 247590*z^2 - 90180*z + 76680)*t^4 + (-1296*z^11 + 37800*z^10 - 41256*z^9 - 86832*z^8 + 139320*z^7 + 98280*z^6 - 151200*z^5 + 20088*z^4 + 151632*z^3 - 23760*z^2 - 50112*z + 7776)*t^3 + (-13284*z^11 + 39204*z^10 + 19224*z^9 - 132732*z^8 + 37260*z^7 + 183384*z^6 - 110052*z^5 - 78516*z^4 + 152928*z^3 + 25272*z^2 - 41796*z + 9180)*t^2 + (-6048*z^11 + 2808*z^10 + 28944*z^9 - 30240*z^8 - 46656*z^7 + 59184*z^6 + 11664*z^5 - 63072*z^4 + 15336*z^3 + 28296*z^2 - 7776*z - 2592)*t + 297*z^11 - 1026*z^10 + 3456*z^8 - 2889*z^7 - 3699*z^6 + 5562*z^5 - 81*z^4 - 4590*z^3 + 1782*z^2 + 1242*z - 756,
 (-7722*z^11 + 22086*z^10 - 3240*z^9 - 50652*z^8 + 38502*z^7 + 40500*z^6 - 59562*z^5 - 4482*z^4 + 45576*z^3 - 8856*z^2 - 15012*z + 6804)*t^12 + (-98496*z^11 + 212544*z^10 + 90072*z^9 - 555336*z^8 + 109512*z^7 + 583200*z^6 - 423144*z^5 - 344088*z^4 + 430272*z^3 + 70632*z^2 - 174960*z + 44064)*t^11 + (223560*z^11 - 733536*z^10 - 90072*z^9 + 2659716*z^8 - 2026620*z^7 - 3154464*z^6 + 4465044*z^5 + 323352*z^4 - 3957336*z^3 + 1499148*z^2 + 1261980*z - 763992)*t^10 + (3447576*z^11 - 7511184*z^10 - 4469040*z^9 + 24927480*z^8 - 8393328*z^7 - 28239408*z^6 + 28654992*z^5 + 10934352*z^4 - 25684344*z^3 + 5006664*z^2 + 8851896*z - 3840912)*t^9 + (3403296*z^11 - 3695868*z^10 - 11826648*z^9 + 21801312*z^8 + 9769248*z^7 - 33295536*z^6 + 15361812*z^5 + 25153416*z^4 - 19040832*z^3 - 2238678*z^2 + 8672670*z - 812592)*t^8 + (-4041576*z^11 + 18718128*z^10 - 16985376*z^9 - 32168016*z^8 + 60015816*z^7 + 7663248*z^6 - 64441656*z^5 + 30965328*z^4 + 37784232*z^3 - 26276400*z^2 - 8659872*z + 11021184)*t^7 + (-18053280*z^11 + 49242816*z^10 - 3374784*z^9 - 119968128*z^8 + 88202520*z^7 + 97750800*z^6 - 151035192*z^5 - 9475704*z^4 + 111685392*z^3 - 32377968*z^2 - 36442224*z + 19078416)*t^6 + (-17546544*z^11 + 38331792*z^10 + 13155048*z^9 - 99952056*z^8 + 34218288*z^7 + 90345456*z^6 - 89199792*z^5 - 39875328*z^4 + 68240880*z^3 - 1063368*z^2 - 24871536*z + 5820336)*t^5 + (1819098*z^11 - 11564532*z^10 + 6563106*z^9 + 34937082*z^8 - 42080796*z^7 - 40589748*z^6 + 69748452*z^5 - 4833270*z^4 - 64619694*z^3 + 25145964*z^2 + 20500938*z - 14105664)*t^4 + (8464824*z^11 - 19295928*z^10 - 8678016*z^9 + 58692600*z^8 - 20930616*z^7 - 64744704*z^6 + 63535752*z^5 + 26203392*z^4 - 58450032*z^3 + 7671024*z^2 + 20609856*z - 8338032)*t^3 + (1602828*z^11 - 1830924*z^10 - 4247964*z^9 + 7142256*z^8 + 4926420*z^7 - 9102456*z^6 + 1647540*z^5 + 8908056*z^4 - 2494800*z^3 - 2839860*z^2 + 1512432*z + 366768)*t^2 + (-200232*z^11 + 598752*z^10 - 12960*z^9 - 1662768*z^8 + 1236384*z^7 + 1578528*z^6 - 2214864*z^5 - 97848*z^4 + 1799496*z^3 - 498960*z^2 - 505440*z + 283824)*t - 6534*z^11 + 10422*z^10 + 17712*z^9 - 45144*z^8 - 9180*z^7 + 67824*z^6 - 36072*z^5 - 45360*z^4 + 49248*z^3 + 3996*z^2 - 19440*z + 6480])

basisE = [
((-15*z^11 + 42*z^10 + 6*z^9 - 132*z^8 + 90*z^7 + 138*z^6 - 192*z^5 - 18*z^4 + 159*z^3 - 54*z^2 - 51*z + 30)*t^4 + (-24*z^11 + 24*z^9 + 156*z^8 - 264*z^7 - 264*z^6 + 456*z^5 - 120*z^4 - 432*z^3 + 204*z^2 + 96*z - 96)*t^3 + (-342*z^11 + 846*z^10 + 90*z^9 - 2214*z^8 + 1296*z^7 + 2088*z^6 - 2844*z^5 - 594*z^4 + 2304*z^3 - 666*z^2 - 882*z + 450)*t^2 + (240*z^11 - 672*z^10 - 36*z^9 + 1944*z^8 - 1368*z^7 - 1968*z^6 + 2832*z^5 + 264*z^4 - 2376*z^3 + 804*z^2 + 780*z - 504)*t + 21*z^11 - 48*z^10 - 18*z^9 + 138*z^8 - 48*z^7 - 159*z^6 + 159*z^5 + 72*z^4 - 156*z^3 + 24*z^2 + 60*z - 30,
 (1404*z^11 - 2484*z^10 - 2916*z^9 + 9396*z^8 - 216*z^7 - 12096*z^6 + 8856*z^5 + 6912*z^4 - 9288*z^3 + 540*z^2 + 3456*z - 1188)*t^5 + (-1296*z^11 + 3456*z^10 - 432*z^9 - 6912*z^8 + 4536*z^7 + 4536*z^6 - 6048*z^5 - 540*z^4 + 4320*z^3 + 108*z^2 - 864*z + 648)*t^4 + (-4644*z^11 + 12636*z^10 - 864*z^9 - 31320*z^8 + 22896*z^7 + 27540*z^6 - 42228*z^5 - 4536*z^4 + 32940*z^3 - 10476*z^2 - 12096*z + 6264)*t^3 + (864*z^11 - 3996*z^10 + 2376*z^9 + 11124*z^8 - 14580*z^7 - 10800*z^6 + 24516*z^5 - 2916*z^4 - 19548*z^3 + 10476*z^2 + 7020*z - 4860)*t^2),

((-15*z^11 + 42*z^10 + 6*z^9 - 132*z^8 + 90*z^7 + 138*z^6 - 192*z^5 - 18*z^4 + 159*z^3 - 54*z^2 - 51*z + 30)*t^4 + (-204*z^11 + 504*z^10 + 96*z^9 - 1428*z^8 + 816*z^7 + 1392*z^6 - 1848*z^5 - 336*z^4 + 1476*z^3 - 444*z^2 - 516*z + 264)*t^3 + (18*z^11 - 90*z^10 + 198*z^9 - 90*z^8 - 360*z^7 + 540*z^6 + 72*z^5 - 522*z^4 + 252*z^3 + 198*z^2 - 162*z - 54)*t^2 + (-192*z^11 + 408*z^10 + 252*z^9 - 1296*z^8 + 288*z^7 + 1596*z^6 - 1380*z^5 - 816*z^4 + 1404*z^3 - 132*z^2 - 552*z + 216)*t + 21*z^11 - 48*z^10 - 18*z^9 + 138*z^8 - 48*z^7 - 159*z^6 + 159*z^5 + 72*z^4 - 156*z^3 + 24*z^2 + 60*z - 30,
 (756*z^11 - 756*z^10 - 1944*z^9 + 1944*z^8 + 4212*z^7 - 2484*z^6 - 3888*z^5 + 5076*z^4 + 2268*z^3 - 4104*z^2 - 324*z + 1296)*t^4 + (-108*z^11 + 648*z^10 + 108*z^9 - 3024*z^8 + 1512*z^7 + 6156*z^6 - 5292*z^5 - 3564*z^4 + 6912*z^3 - 864*z^2 - 3780*z + 756)*t^3 + (-1080*z^11 + 5616*z^10 - 4644*z^9 - 10908*z^8 + 17064*z^7 + 7344*z^6 - 20304*z^5 + 6048*z^4 + 15768*z^3 - 6696*z^2 - 4212*z + 3672)*t^2 + (-2052*z^11 + 4860*z^10 + 972*z^9 - 12636*z^8 + 6588*z^7 + 10584*z^6 - 13716*z^5 - 2052*z^4 + 9936*z^3 - 2376*z^2 - 2484*z + 1620)*t),

((-15*z^11 + 42*z^10 + 6*z^9 - 132*z^8 + 90*z^7 + 138*z^6 - 192*z^5 - 18*z^4 + 159*z^3 - 54*z^2 - 51*z + 30)*t^4 + (-204*z^11 + 504*z^10 + 96*z^9 - 1428*z^8 + 816*z^7 + 1392*z^6 - 1848*z^5 - 336*z^4 + 1476*z^3 - 444*z^2 - 516*z + 264)*t^3 + (-90*z^11 + 162*z^10 + 126*z^9 - 486*z^8 + 72*z^7 + 432*z^6 - 396*z^5 - 198*z^4 + 216*z^3 - 18*z^2 - 54*z - 18)*t^2 + (60*z^11 - 168*z^10 + 36*z^9 + 360*z^8 - 288*z^7 - 312*z^6 + 528*z^5 + 48*z^4 - 468*z^3 + 156*z^2 + 168*z - 144)*t + 21*z^11 - 48*z^10 - 18*z^9 + 138*z^8 - 48*z^7 - 159*z^6 + 159*z^5 + 72*z^4 - 156*z^3 + 24*z^2 + 60*z - 30,
-( (108*z^11 + 324*z^10 - 432*z^9 - 1728*z^8 + 2376*z^7 + 3564*z^6 - 5076*z^5 - 324*z^4 + 5940*z^3 - 2160*z^2 - 2160*z + 1512)*t^4 + (-1188*z^11 + 2376*z^10 + 2484*z^9 - 9072*z^8 + 648*z^7 + 12744*z^6 - 9072*z^5 - 6696*z^4 + 10908*z^3 - 540*z^2 - 3672*z + 1728)*t^3 + (108*z^11 - 1836*z^10 + 3348*z^9 + 1620*z^8 - 8208*z^7 + 1728*z^6 + 6912*z^5 - 5292*z^4 - 3672*z^3 + 3672*z^2 + 1296*z - 1404)*t^2 + (1404*z^11 - 3888*z^10 + 432*z^9 + 8964*z^8 - 6480*z^7 - 7452*z^6 + 10908*z^5 + 1080*z^4 - 8640*z^3 + 2052*z^2 + 2808*z - 1620)*t)),

((-1203//13*z^11 + 2310//13*z^10 + 3426//13*z^9 - 11472//13*z^8 + 1854//13*z^7 + 15906//13*z^6 - 13332//13*z^5 - 6282//13*z^4 + 13191//13*z^3 - 2214//13*z^2 - 3867//13*z + 1650//13)*t^4 + (-1068//13*z^11 - 144//13*z^10 + 9384//13*z^9 - 14928//13*z^8 - 336*z^7 + 25692//13*z^6 - 18300//13*z^5 - 11280//13*z^4 + 18072//13*z^3 - 5448//13*z^2 - 3720//13*z + 1992//13)*t^3 + (-3438//13*z^11 + 4626//13*z^10 + 13590//13*z^9 - 32346//13*z^8 - 900//13*z^7 + 3600*z^6 - 36216//13*z^5 - 20754//13*z^4 + 34452//13*z^3 - 7074//13*z^2 - 9342//13*z + 3438//13)*t^2 + (276*z^11 - 11112//13*z^10 + 5688//13*z^9 + 18360//13*z^8 - 20952//13*z^7 - 8304//13*z^6 + 24072//13*z^5 - 2472//13*z^4 - 16236//13*z^3 + 4800//13*z^2 + 7404//13*z - 4104//13)*t + 1569//13*z^11 - 4152//13*z^10 + 990//13*z^9 + 8022//13*z^8 - 6816//13*z^7 - 4155//13*z^6 + 9411//13*z^5 - 432//13*z^4 - 5340//13*z^3 + 1932//13*z^2 + 2004//13*z - 1038//13,
 (-126252//169*z^11 + 417204//169*z^10 - 530820//169*z^9 - 142452//169*z^8 + 1356480//169*z^7 - 1698516//169*z^6 - 264492//169*z^5 + 1866456//169*z^4 - 1440828//169*z^3 - 338148//169*z^2 + 811404//169*z - 290952//169)*t^6 + (-442044//169*z^11 + 2289816//169*z^10 - 3569076//169*z^9 - 1241568//169*z^8 + 9427104//169*z^7 - 7877628//169*z^6 - 4142988//169*z^5 + 10748268//169*z^4 - 4569048//169*z^3 - 3132432//169*z^2 + 3313332//169*z - 860436//169)*t^5 + (-1162728//169*z^11 + 4893804//169*z^10 - 6446088//169*z^9 - 3506004//169*z^8 + 17809632//169*z^7 - 14511636//169*z^6 - 7975908//169*z^5 + 19951920//169*z^4 - 9233136//169*z^3 - 5412960//169*z^2 + 6511428//169*z - 1915920//169)*t^4 + (-1590084//169*z^11 + 509976//13*z^10 - 7644888//169*z^9 - 6990084//169*z^8 + 23298948//169*z^7 - 13693428//169*z^6 - 13823352//169*z^5 + 23171292//169*z^4 - 6554736//169*z^3 - 582120//13*z^2 + 6376860//169*z - 1425492//169)*t^3 + (-1060452//169*z^11 + 4108752//169*z^10 - 4691196//169*z^9 - 4092768//169*z^8 + 14577948//169*z^7 - 10120680//169*z^6 - 8150004//169*z^5 + 15838416//169*z^4 - 6106428//169*z^3 - 4998996//169*z^2 + 5089068//169*z - 98928//13)*t^2 + (-11772//13*z^11 + 1029456//169*z^10 - 1868508//169*z^9 - 455976//169*z^8 + 5238756//169*z^7 - 4816584//169*z^6 - 2130084//169*z^5 + 6745356//169*z^4 - 3221748//169*z^3 - 1902096//169*z^2 + 2438964//169*z - 739584//169)*t - 19116//169*z^11 + 140184//169*z^10 - 16740//13*z^9 - 184248//169*z^8 + 812268//169*z^7 - 542484//169*z^6 - 486216//169*z^5 + 1022652//169*z^4 - 358560//169*z^3 - 342792//169*z^2 + 29160//13*z - 120852//169)
]



E=elliptic_curve(Ft, ainvs)
basisE = [E(collect(b)) for b in basisE]

Ek = base_change(FttokFt, E)
basisk = [Ek(FttokFt.([b[1],b[2]])) for b in basisE]


@test all(basisE[i] == newton_lift(E,basisk[i],OFtokF;max_iterations=7) for i in 1:4)
# test a non-integral section
@test 2*basisE[1] == newton_lift(E,2*basisk[1],OFtokF;max_iterations=7)
