function _write_fields(list::Vector{Tuple{AnticNumberField, ZZRingElem}}, filename::String)
  f=open(filename, "a")
  for L in list
    x=([coeff(L[1].pol, i) for i=0:degree(L[1].pol)], L[2])
    Base.write(f, "$x\n")
  end
  close(f)
end

function __to_univariate(Qx, f)
  z = zero(Qx)
  x = gen(Qx)
  for (c, m) in zip(coefficients(f), monomials(f))
    z = z + FlintQQ(c) * x^total_degree(m)
  end
  return z
end

function _write_fields(list::Vector{Tuple{AnticNumberField, NfRelNS{nf_elem}, ZZRingElem}}, filename::String)
  f=open(filename, "a")
  for L in list
    Qx = parent(L[1].pol)
    unis = [ __to_univariate(Qx, L[2].pol[i]) for i in 1:length(L[2].pol)]
    y = [[coeff(g, i) for i=0:degree(g)] for g in unis]
    x=([coeff(L[1].pol, i) for i=0:degree(L[1].pol)], y, L[3])
    Base.write(f, "$x\n")
  end
  close(f)
end

function _read_fields(filename::String)
  f=open(filename, "r")
  Qx,x=PolynomialRing(FlintQQ,"x")
  pols = []
  for s in eachline(f)
    a=Main.eval(Meta.parse(s))
    if length(a) == 3
      push!(pols,(Qx(a[1]), [ Qx(b) for b in a[2]], a[3]))
    else
      @assert length(a) == 2
      push!(pols,(Qx(a[1]), a[end]))
    end
  end
  close(f)
  return identity.(pols)
end

global small_solvable_groups =
[ (1, 1), (2, 1), (3, 1), (4, 1), (4, 2), (5, 1), (6, 1), (6, 2), (7, 1), (8,
1), (8, 2), (8, 3), (8, 4), (8, 5), (9, 1), (9, 2), (10, 1), (10, 2), (11, 1),
(12, 1), (12, 2), (12, 3), (12, 4), (12, 5), (13, 1), (14, 1), (14, 2), (15, 1),
(16, 1), (16, 2), (16, 3), (16, 4), (16, 5), (16, 6), (16, 7), (16, 8), (16, 9),
(16, 10), (16, 11), (16, 12), (16, 13), (16, 14), (17, 1), (18, 1), (18, 2),
(18, 3), (18, 4), (18, 5), (19, 1), (20, 1), (20, 2), (20, 3), (20, 4), (20, 5),
(21, 1), (21, 2), (22, 1), (22, 2), (23, 1), (24, 1), (24, 2), (24, 3), (24, 4),
(24, 5), (24, 6), (24, 7), (24, 8), (24, 9), (24, 10), (24, 11), (24, 12), (24,
13), (24, 14), (24, 15), (25, 1), (25, 2), (26, 1), (26, 2), (27, 1), (27, 2),
(27, 3), (27, 4), (27, 5), (28, 1), (28, 2), (28, 3), (28, 4), (29, 1), (30, 1),
(30, 2), (30, 3), (30, 4), (31, 1), (32, 1), (32, 2), (32, 3), (32, 4), (32, 5),
(32, 6), (32, 7), (32, 8), (32, 9), (32, 10), (32, 11), (32, 12), (32, 13), (32,
14), (32, 15), (32, 16), (32, 17), (32, 18), (32, 19), (32, 20), (32, 21), (32,
22), (32, 23), (32, 24), (32, 25), (32, 26), (32, 27), (32, 28), (32, 29), (32,
30), (32, 31), (32, 32), (32, 33), (32, 34), (32, 35), (32, 36), (32, 37), (32,
38), (32, 39), (32, 40), (32, 41), (32, 42), (32, 43), (32, 44), (32, 45), (32,
46), (32, 47), (32, 48), (32, 49), (32, 50), (32, 51), (33, 1), (34, 1), (34,
2), (35, 1), (36, 1), (36, 2), (36, 3), (36, 4), (36, 5), (36, 6), (36, 7), (36,
8), (36, 9), (36, 10), (36, 11), (36, 12), (36, 13), (36, 14), (37, 1), (38, 1),
(38, 2), (39, 1), (39, 2), (40, 1), (40, 2), (40, 3), (40, 4), (40, 5), (40, 6),
(40, 7), (40, 8), (40, 9), (40, 10), (40, 11), (40, 12), (40, 13), (40, 14),
(41, 1), (42, 1), (42, 2), (42, 3), (42, 4), (42, 5), (42, 6), (43, 1), (44, 1),
(44, 2), (44, 3), (44, 4), (45, 1), (45, 2), (46, 1), (46, 2), (47, 1), (48, 1),
(48, 2), (48, 3), (48, 4), (48, 5), (48, 6), (48, 7), (48, 8), (48, 9), (48,
10), (48, 11), (48, 12), (48, 13), (48, 14), (48, 15), (48, 16), (48, 17), (48,
18), (48, 19), (48, 20), (48, 21), (48, 22), (48, 23), (48, 24), (48, 25), (48,
26), (48, 27), (48, 28), (48, 29), (48, 30), (48, 31), (48, 32), (48, 33), (48,
34), (48, 35), (48, 36), (48, 37), (48, 38), (48, 39), (48, 40), (48, 41), (48,
42), (48, 43), (48, 44), (48, 45), (48, 46), (48, 47), (48, 48), (48, 49), (48,
50), (48, 51), (48, 52), (49, 1), (49, 2), (50, 1), (50, 2), (50, 3), (50, 4),
(50, 5), (51, 1), (52, 1), (52, 2), (52, 3), (52, 4), (52, 5), (53, 1), (54, 1),
(54, 2), (54, 3), (54, 4), (54, 5), (54, 6), (54, 7), (54, 8), (54, 9), (54,
10), (54, 11), (54, 12), (54, 13), (54, 14), (54, 15), (55, 1), (55, 2), (56,
1), (56, 2), (56, 3), (56, 4), (56, 5), (56, 6), (56, 7), (56, 8), (56, 9), (56,
10), (56, 11), (56, 12), (56, 13), (57, 1), (57, 2), (58, 1), (58, 2), (59, 1),
(60, 1), (60, 2), (60, 3), (60, 4), (60, 6), (60, 7), (60, 8), (60, 9), (60,
10), (60, 11), (60, 12), (60, 13), (61, 1), (62, 1), (62, 2), (63, 1), (63, 2),
(63, 3), (63, 4), (64, 1), (64, 2), (64, 3), (64, 4), (64, 5), (64, 6), (64, 7),
(64, 8), (64, 9), (64, 10), (64, 11), (64, 12), (64, 13), (64, 14), (64, 15),
(64, 16), (64, 17), (64, 18), (64, 19), (64, 20), (64, 21), (64, 22), (64, 23),
(64, 24), (64, 25), (64, 26), (64, 27), (64, 28), (64, 29), (64, 30), (64, 31),
(64, 32), (64, 33), (64, 34), (64, 35), (64, 36), (64, 37), (64, 38), (64, 39),
(64, 40), (64, 41), (64, 42), (64, 43), (64, 44), (64, 45), (64, 46), (64, 47),
(64, 48), (64, 49), (64, 50), (64, 51), (64, 52), (64, 53), (64, 54), (64, 55),
(64, 56), (64, 57), (64, 58), (64, 59), (64, 60), (64, 61), (64, 62), (64, 63),
(64, 64), (64, 65), (64, 66), (64, 67), (64, 68), (64, 69), (64, 70), (64, 71),
(64, 72), (64, 73), (64, 74), (64, 75), (64, 76), (64, 77), (64, 78), (64, 79),
(64, 80), (64, 81), (64, 82), (64, 83), (64, 84), (64, 85), (64, 86), (64, 87),
(64, 88), (64, 89), (64, 90), (64, 91), (64, 92), (64, 93), (64, 94), (64, 95),
(64, 96), (64, 97), (64, 98), (64, 99), (64, 100), (64, 101), (64, 102), (64,
103), (64, 104), (64, 105), (64, 106), (64, 107), (64, 108), (64, 109), (64,
110), (64, 111), (64, 112), (64, 113), (64, 114), (64, 115), (64, 116), (64,
117), (64, 118), (64, 119), (64, 120), (64, 121), (64, 122), (64, 123), (64,
124), (64, 125), (64, 126), (64, 127), (64, 128), (64, 129), (64, 130), (64,
131), (64, 132), (64, 133), (64, 134), (64, 135), (64, 136), (64, 137), (64,
138), (64, 139), (64, 140), (64, 141), (64, 142), (64, 143), (64, 144), (64,
145), (64, 146), (64, 147), (64, 148), (64, 149), (64, 150), (64, 151), (64,
152), (64, 153), (64, 154), (64, 155), (64, 156), (64, 157), (64, 158), (64,
159), (64, 160), (64, 161), (64, 162), (64, 163), (64, 164), (64, 165), (64,
166), (64, 167), (64, 168), (64, 169), (64, 170), (64, 171), (64, 172), (64,
173), (64, 174), (64, 175), (64, 176), (64, 177), (64, 178), (64, 179), (64,
180), (64, 181), (64, 182), (64, 183), (64, 184), (64, 185), (64, 186), (64,
187), (64, 188), (64, 189), (64, 190), (64, 191), (64, 192), (64, 193), (64,
194), (64, 195), (64, 196), (64, 197), (64, 198), (64, 199), (64, 200), (64,
201), (64, 202), (64, 203), (64, 204), (64, 205), (64, 206), (64, 207), (64,
208), (64, 209), (64, 210), (64, 211), (64, 212), (64, 213), (64, 214), (64,
215), (64, 216), (64, 217), (64, 218), (64, 219), (64, 220), (64, 221), (64,
222), (64, 223), (64, 224), (64, 225), (64, 226), (64, 227), (64, 228), (64,
229), (64, 230), (64, 231), (64, 232), (64, 233), (64, 234), (64, 235), (64,
236), (64, 237), (64, 238), (64, 239), (64, 240), (64, 241), (64, 242), (64,
243), (64, 244), (64, 245), (64, 246), (64, 247), (64, 248), (64, 249), (64,
250), (64, 251), (64, 252), (64, 253), (64, 254), (64, 255), (64, 256), (64,
257), (64, 258), (64, 259), (64, 260), (64, 261), (64, 262), (64, 263), (64,
264), (64, 265), (64, 266), (64, 267), (65, 1), (66, 1), (66, 2), (66, 3), (66,
4), (67, 1), (68, 1), (68, 2), (68, 3), (68, 4), (68, 5), (69, 1), (70, 1), (70,
2), (70, 3), (70, 4), (71, 1), (72, 1), (72, 2), (72, 3), (72, 4), (72, 5), (72,
6), (72, 7), (72, 8), (72, 9), (72, 10), (72, 11), (72, 12), (72, 13), (72, 14),
(72, 15), (72, 16), (72, 17), (72, 18), (72, 19), (72, 20), (72, 21), (72, 22),
(72, 23), (72, 24), (72, 25), (72, 26), (72, 27), (72, 28), (72, 29), (72, 30),
(72, 31), (72, 32), (72, 33), (72, 34), (72, 35), (72, 36), (72, 37), (72, 38),
(72, 39), (72, 40), (72, 41), (72, 42), (72, 43), (72, 44), (72, 45), (72, 46),
(72, 47), (72, 48), (72, 49), (72, 50), (73, 1), (74, 1), (74, 2), (75, 1), (75,
2), (75, 3), (76, 1), (76, 2), (76, 3), (76, 4), (77, 1), (78, 1), (78, 2), (78,
3), (78, 4), (78, 5), (78, 6), (79, 1), (80, 1), (80, 2), (80, 3), (80, 4), (80,
5), (80, 6), (80, 7), (80, 8), (80, 9), (80, 10), (80, 11), (80, 12), (80, 13),
(80, 14), (80, 15), (80, 16), (80, 17), (80, 18), (80, 19), (80, 20), (80, 21),
(80, 22), (80, 23), (80, 24), (80, 25), (80, 26), (80, 27), (80, 28), (80, 29),
(80, 30), (80, 31), (80, 32), (80, 33), (80, 34), (80, 35), (80, 36), (80, 37),
(80, 38), (80, 39), (80, 40), (80, 41), (80, 42), (80, 43), (80, 44), (80, 45),
(80, 46), (80, 47), (80, 48), (80, 49), (80, 50), (80, 51), (80, 52), (81, 1),
(81, 2), (81, 3), (81, 4), (81, 5), (81, 6), (81, 7), (81, 8), (81, 9), (81,
10), (81, 11), (81, 12), (81, 13), (81, 14), (81, 15), (82, 1), (82, 2), (83,
1), (84, 1), (84, 2), (84, 3), (84, 4), (84, 5), (84, 6), (84, 7), (84, 8), (84,
9), (84, 10), (84, 11), (84, 12), (84, 13), (84, 14), (84, 15), (85, 1), (86,
1), (86, 2), (87, 1), (88, 1), (88, 2), (88, 3), (88, 4), (88, 5), (88, 6), (88,
7), (88, 8), (88, 9), (88, 10), (88, 11), (88, 12), (89, 1), (90, 1), (90, 2),
(90, 3), (90, 4), (90, 5), (90, 6), (90, 7), (90, 8), (90, 9), (90, 10), (91,
1), (92, 1), (92, 2), (92, 3), (92, 4), (93, 1), (93, 2), (94, 1), (94, 2), (95,
1), (96, 1), (96, 2), (96, 3), (96, 4), (96, 5), (96, 6), (96, 7), (96, 8), (96,
9), (96, 10), (96, 11), (96, 12), (96, 13), (96, 14), (96, 15), (96, 16), (96,
17), (96, 18), (96, 19), (96, 20), (96, 21), (96, 22), (96, 23), (96, 24), (96,
25), (96, 26), (96, 27), (96, 28), (96, 29), (96, 30), (96, 31), (96, 32), (96,
33), (96, 34), (96, 35), (96, 36), (96, 37), (96, 38), (96, 39), (96, 40), (96,
41), (96, 42), (96, 43), (96, 44), (96, 45), (96, 46), (96, 47), (96, 48), (96,
49), (96, 50), (96, 51), (96, 52), (96, 53), (96, 54), (96, 55), (96, 56), (96,
57), (96, 58), (96, 59), (96, 60), (96, 61), (96, 62), (96, 63), (96, 64), (96,
65), (96, 66), (96, 67), (96, 68), (96, 69), (96, 70), (96, 71), (96, 72), (96,
73), (96, 74), (96, 75), (96, 76), (96, 77), (96, 78), (96, 79), (96, 80), (96,
81), (96, 82), (96, 83), (96, 84), (96, 85), (96, 86), (96, 87), (96, 88), (96,
89), (96, 90), (96, 91), (96, 92), (96, 93), (96, 94), (96, 95), (96, 96), (96,
97), (96, 98), (96, 99), (96, 100), (96, 101), (96, 102), (96, 103), (96, 104),
(96, 105), (96, 106), (96, 107), (96, 108), (96, 109), (96, 110), (96, 111),
(96, 112), (96, 113), (96, 114), (96, 115), (96, 116), (96, 117), (96, 118),
(96, 119), (96, 120), (96, 121), (96, 122), (96, 123), (96, 124), (96, 125),
(96, 126), (96, 127), (96, 128), (96, 129), (96, 130), (96, 131), (96, 132),
(96, 133), (96, 134), (96, 135), (96, 136), (96, 137), (96, 138), (96, 139),
(96, 140), (96, 141), (96, 142), (96, 143), (96, 144), (96, 145), (96, 146),
(96, 147), (96, 148), (96, 149), (96, 150), (96, 151), (96, 152), (96, 153),
(96, 154), (96, 155), (96, 156), (96, 157), (96, 158), (96, 159), (96, 160),
(96, 161), (96, 162), (96, 163), (96, 164), (96, 165), (96, 166), (96, 167),
(96, 168), (96, 169), (96, 170), (96, 171), (96, 172), (96, 173), (96, 174),
(96, 175), (96, 176), (96, 177), (96, 178), (96, 179), (96, 180), (96, 181),
(96, 182), (96, 183), (96, 184), (96, 185), (96, 186), (96, 187), (96, 188),
(96, 189), (96, 190), (96, 191), (96, 192), (96, 193), (96, 194), (96, 195),
(96, 196), (96, 197), (96, 198), (96, 199), (96, 200), (96, 201), (96, 202),
(96, 203), (96, 204), (96, 205), (96, 206), (96, 207), (96, 208), (96, 209),
(96, 210), (96, 211), (96, 212), (96, 213), (96, 214), (96, 215), (96, 216),
(96, 217), (96, 218), (96, 219), (96, 220), (96, 221), (96, 222), (96, 223),
(96, 224), (96, 225), (96, 226), (96, 227), (96, 228), (96, 229), (96, 230),
(96, 231), (97, 1), (98, 1), (98, 2), (98, 3), (98, 4), (98, 5), (99, 1), (99,
2), (100, 1), (100, 2), (100, 3), (100, 4), (100, 5), (100, 6), (100, 7), (100,
8), (100, 9), (100, 10), (100, 11), (100, 12), (100, 13), (100, 14), (100, 15),
(100, 16) ]
