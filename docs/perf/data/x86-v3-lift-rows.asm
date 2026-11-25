000000000007bad0 <jpeg2000_decoder::transform::rowwise::lift_rows>:
   7c030:	c4 81 7e 6f 4c d6 e0 	vmovdqu -0x20(%r14,%r10,8),%ymm1
   7c037:	c4 81 7e 6f 14 d6    	vmovdqu (%r14,%r10,8),%ymm2
   7c03d:	c4 a1 7e 6f 5c d6 e0 	vmovdqu -0x20(%rsi,%r10,8),%ymm3
   7c044:	c4 a1 7e 6f 24 d6    	vmovdqu (%rsi,%r10,8),%ymm4
   7c04a:	c4 81 65 d4 5c d0 e0 	vpaddq -0x20(%r8,%r10,8),%ymm3,%ymm3
   7c051:	c4 81 5d d4 24 d0    	vpaddq (%r8,%r10,8),%ymm4,%ymm4
   7c057:	c5 e5 d4 d8          	vpaddq %ymm0,%ymm3,%ymm3
   7c05b:	c5 dd d4 e0          	vpaddq %ymm0,%ymm4,%ymm4
   7c05f:	c5 d5 72 e3 02       	vpsrad $0x2,%ymm3,%ymm5
   7c064:	c5 e5 73 d3 02       	vpsrlq $0x2,%ymm3,%ymm3
   7c069:	c4 e3 65 02 dd aa    	vpblendd $0xaa,%ymm5,%ymm3,%ymm3
   7c06f:	c5 f5 fb cb          	vpsubq %ymm3,%ymm1,%ymm1
   7c073:	c5 e5 72 e4 02       	vpsrad $0x2,%ymm4,%ymm3
   7c078:	c5 dd 73 d4 02       	vpsrlq $0x2,%ymm4,%ymm4
   7c07d:	c4 e3 5d 02 db aa    	vpblendd $0xaa,%ymm3,%ymm4,%ymm3
   7c083:	c5 ed fb d3          	vpsubq %ymm3,%ymm2,%ymm2
   7c087:	c4 81 7e 7f 4c d6 e0 	vmovdqu %ymm1,-0x20(%r14,%r10,8)
   7c08e:	c4 81 7e 7f 14 d6    	vmovdqu %ymm2,(%r14,%r10,8)
   7c094:	49 83 c2 08          	add    $0x8,%r10
   7c098:	4c 39 d0             	cmp    %r10,%rax
   7c09b:	75 93                	jne    7c030 <jpeg2000_decoder::transform::rowwise::lift_rows+0x560>
