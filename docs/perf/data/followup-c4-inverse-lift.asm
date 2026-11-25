symbol=_ZN16jpeg2000_decoder9transform8wavelets12inverse_lift17h4bfc198acecbc9e9E
846e0: stp x20, x19, [sp, #-0x10]!
846e4: cbz x2, #0x8470c
846e8: cmp x4, #1
846ec: mov x8, #-0x40000000
846f0: mov x9, #-0x80000000
846f4: mov w10, #0x40000000
846f8: mov w11, #-0x80000000
846fc: csel x8, x9, x8, eq
84700: csel x9, x11, x10, eq
84704: subs x10, x2, #1
84708: b.ne #0x8471c
8470c: mov w8, #0xf
84710: strb w8, [x0]
84714: ldp x20, x19, [sp], #0x10
84718: ret 
8471c: scvtf d0, x5
84720: add x11, x5, #0x40, lsl #12
84724: cbz w3, #0x84764
84728: ldp x12, x13, [x1]
8472c: cmp x4, #1
84730: b.hi #0x848e8
84734: cmp x12, x8
84738: b.lt #0x848e8
8473c: cmp x12, x9
84740: b.gt #0x848e8
84744: cmp x13, x8
84748: b.lt #0x848e8
8474c: cmp x13, x9
84750: b.gt #0x848e8
84754: cmp x4, #1
84758: b.ne #0x84974
8475c: add x16, x12, x13
84760: b #0x84768
84764: ldr x16, [x1]
84768: mov x12, #1
8476c: mov x13, x1
84770: mov w14, #1
84774: movk x12, #8, lsl #32
84778: mov w15, #2
8477c: mov x17, #0x40e0000000000000
84780: str x16, [x13], #8
84784: mov x16, #0x400000000
84788: mov x18, #0x3ef0000000000000
8478c: mov x6, #0x8000
84790: b #0x847ac
84794: ldr x7, [x13]
84798: add x14, x14, #1
8479c: subs x10, x10, #1
847a0: add x15, x15, #1
847a4: str x7, [x13], #8
847a8: b.eq #0x8470c
847ac: sub w7, w15, #1
847b0: tst x7, #1
847b4: cset w7, eq
847b8: eor w7, w3, w7
847bc: tbnz w7, #0, #0x84794
847c0: sub x7, x15, #2
847c4: cmp x15, x2
847c8: add x14, x14, #1
847cc: csel x7, x15, x7, lo
847d0: cmp x4, #1
847d4: ldr x19, [x1, x7, lsl #3]
847d8: ldp x20, x7, [x13, #-8]
847dc: b.hi #0x84824
847e0: cmp x7, x8
847e4: b.lt #0x84824
847e8: cmp x7, x9
847ec: b.gt #0x84824
847f0: cmp x20, x8
847f4: b.lt #0x84824
847f8: cmp x20, x9
847fc: b.gt #0x84824
84800: cmp x19, x8
84804: b.lt #0x84824
84808: cmp x19, x9
8480c: b.gt #0x84824
84810: cmp x4, #1
84814: add x19, x19, x20
84818: b.ne #0x848dc
8481c: add x7, x7, x19, asr #1
84820: b #0x8479c
84824: adds x19, x20, x19
84828: b.vs #0x848f0
8482c: cbz x4, #0x84844
84830: cmp x4, #1
84834: b.ne #0x8485c
84838: adds x7, x7, x19, asr #1
8483c: b.vc #0x8479c
84840: b #0x848f0
84844: adds x19, x19, #2
84848: b.vs #0x848f0
8484c: asr x19, x19, #2
84850: subs x7, x7, x19
84854: b.vc #0x8479c
84858: b #0x848f0
8485c: add x20, x19, x16
84860: cmp x20, x12
84864: b.hs #0x848b4
84868: cmp x11, #0x80, lsl #12
8486c: b.hi #0x84898
84870: scvtf d1, x19
84874: fmov d2, x17
84878: fmul d1, d0, d1
8487c: fadd d1, d1, d2
84880: fmov d2, x18
84884: fmul d1, d1, d2
84888: fcvtms x19, d1
8488c: subs x7, x7, x19
84890: b.vc #0x8479c
84894: b #0x848f0
84898: cmp x19, w19, sxtw
8489c: b.ne #0x848b4
848a0: madd x19, x19, x5, x6
848a4: asr x19, x19, #0x10
848a8: subs x7, x7, x19
848ac: b.vc #0x8479c
848b0: b #0x848f0
848b4: mul x20, x19, x5
848b8: smulh x19, x19, x5
848bc: cmp x19, x20, asr #63
848c0: b.ne #0x848f0
848c4: adds x19, x20, #8, lsl #12
848c8: b.vs #0x848f0
848cc: asr x19, x19, #0x10
848d0: subs x7, x7, x19
848d4: b.vc #0x8479c
848d8: b #0x848f0
848dc: add x19, x19, #2
848e0: sub x7, x7, x19, asr #2
848e4: b #0x8479c
848e8: adds x13, x13, x13
848ec: b.vc #0x84904
848f0: mov w8, #0x2300
848f4: str xzr, [x0, #8]
848f8: strh w8, [x0]
848fc: ldp x20, x19, [sp], #0x10
84900: ret 
84904: cbz x4, #0x8491c
84908: cmp x4, #1
8490c: b.ne #0x8492c
84910: adds x16, x12, x13, asr #1
84914: b.vc #0x84768
84918: b #0x848f0
8491c: adds x13, x13, #2
84920: b.vs #0x848f0
84924: asr x13, x13, #2
84928: b #0x849b4
8492c: mov x14, #0x400000000
84930: mov x15, #1
84934: add x14, x13, x14
84938: movk x15, #8, lsl #32
8493c: cmp x14, x15
84940: b.hs #0x84998
84944: cmp x11, #0x80, lsl #12
84948: b.hi #0x84984
8494c: scvtf d1, x13
84950: mov x13, #0x40e0000000000000
84954: fmov d2, x13
84958: mov x13, #0x3ef0000000000000
8495c: fmul d1, d0, d1
84960: fadd d1, d1, d2
84964: fmov d2, x13
84968: fmul d1, d1, d2
8496c: fcvtms x13, d1
84970: b #0x849b4
84974: lsl x13, x13, #1
84978: add x13, x13, #2
8497c: sub x16, x12, x13, asr #2
84980: b #0x84768
84984: cmp x13, w13, sxtw
84988: b.ne #0x84998
8498c: mov x14, #0x8000
84990: madd x13, x13, x5, x14
84994: b #0x849b0
84998: mul x14, x13, x5
8499c: smulh x13, x13, x5
849a0: cmp x13, x14, asr #63
849a4: b.ne #0x848f0
849a8: adds x13, x14, #8, lsl #12
849ac: b.vs #0x848f0
849b0: asr x13, x13, #0x10
849b4: subs x16, x12, x13
849b8: b.vc #0x84768
849bc: b #0x848f0
