这是错的：

a: {
      permute: Perm (Fin 8) := (1=>a1,2=>a1,3=>a1,4=>a1,5=>a1,6=>a1,7=>a1,8=>a1)
      orient : Vector (Fin 3) 8 := (b1,b2,b3,b4,b5,b6,b7,b8)
}
b: {
      permute: Perm (Fin 8) := (a1=>c1,a2=>c2,a3=>c3,a4=>c4,a5=>c5,a6=>c6,a7=>c7,a8=>c8)
      orient : Vector (Fin 3) 8 := (d1,d2,d3,d4,d5,d6,d7,d8)
}
c: {
      permute: Perm (Fin 8) := (c1=>e1,c2=>e2,c3=>e3,c4=>e4,c5=>e5,c6=>e6,c7=>e7,c8=>e8)
      orient : Vector (Fin 3) 8 := (f1,f2,f3,f4,f5,f6,f7,f8)
}
bc:{
      permute: (a1=>c1,a2=>c2,a3=>c3,a4=>c4,a5=>c5,a6=>c6,a7=>c7,a8=>c8) * (c1=>e1,c2=>e2,c3=>e3,c4=>e4,c5=>e5,c6=>e6,c7=>e7,c8=>e8)
            = (a1=>e1,a2=>e2,a3=>e3,a4=>e4,a5=>e5,a6=>e6,a7=>e7,a8=>e8)
      orient : (a1=>c1,a2=>c2,a3=>c3,a4=>c4,a5=>c5,a6=>c6,a7=>c7,a8=>c8)^(-1)·(f1,f2,f3,f4,f5,f6,f7,f8)
            + (d1,d2,d3,d4,d5,d6,d7,d8) (mod 3)
      }
ab:{
      permute: (1=>a1,2=>a1,3=>a1,4=>a1,5=>a1,6=>a1,7=>a1,8=>a1) * (a1=>c1,a2=>c2,a3=>c3,a4=>c4,a5=>c5,a6=>c6,a7=>c7,a8=>c8)
            = (1=>c1,2=>c1,3=>c1,4=>c1,5=>c1,6=>c1,7=>c1,8=>c1)
      orient : (1=>a1,2=>a1,3=>a1,4=>a1,5=>a1,6=>a1,7=>a1,8=>a1)^(-1)·(d1,d2,d3,d4,d5,d6,d7,d8)
            + (b1,b2,b3,b4,b5,b6,b7,b8) (mod 3)
      }
(ab)c:{
      permute: (1=>c1,2=>c1,3=>c1,4=>c1,5=>c1,6=>c1,7=>c1,8=>c1)
            * (c1=>e1,c2=>e2,c3=>e3,c4=>e4,c5=>e5,c6=>e6,c7=>e7,c8=>e8)
            = (1=>e1,2=>e1,3=>e1,4=>e1,5=>e1,6=>e1,7=>e1,8=>e1)
      orient : (1=>c1,2=>c1,3=>c1,4=>c1,5=>c1,6=>c1,7=>c1,8=>c1)^(-1)·
            (f1,f2,f3,f4,f5,f6,f7,f8)
            + (1=>a1,2=>a1,3=>a1,4=>a1,5=>a1,6=>a1,7=>a1,8=>a1)^(-1)·(d1,d2,d3,d4,d5,d6,d7,d8)
            + (b1,b2,b3,b4,b5,b6,b7,b8) (mod 3)

      = (1=>c1,2=>c1,3=>c1,4=>c1,5=>c1,6=>c1,7=>c1,8=>c1)^(-1)·(f1,f2,f3,f4,f5,f6,f7,f8)
      + (1=>a1,2=>a1,3=>a1,4=>a1,5=>a1,6=>a1,7=>a1,8=>a1)^(-1)·(d1,d2,d3,d4,d5,d6,d7,d8)
      + (b1,b2,b3,b4,b5,b6,b7,b8)

      = (c1=>1,c1=>2,c1=>3,c1=>4,c1=>5,c1=>6,c1=>7,c1=>8)·(f1,f2,f3,f4,f5,f6,f7,f8)
      + (1=>a1,2=>a1,3=>a1,4=>a1,5=>a1,6=>a1,7=>a1,8=>a1)^(-1)·(d1,d2,d3,d4,d5,d6,d7,d8)
      + (b1,b2,b3,b4,b5,b6,b7,b8)

      }
a(bc):{
      permute: (1=>a1,2=>a1,3=>a1,4=>a1,5=>a1,6=>a1,7=>a1,8=>a1)
      * (a1=>e1,a2=>e2,a3=>e3,a4=>e4,a5=>e5,a6=>e6,a7=>e7,a8=>e8)
      = (1=>e1,2=>e1,3=>e1,4=>e1,5=>e1,6=>e1,7=>e1,8=>e1)
      orient : (1=>a1,2=>a1,3=>a1,4=>a1,5=>a1,6=>a1,7=>a1,8=>a1)^(-1)·
      ((a1=>c1,a2=>c2,a3=>c3,a4=>c4,a5=>c5,a6=>c6,a7=>c7,a8=>c8)^(-1)·(f1,f2,f3,f4,f5,f6,f7,f8) + (d1,d2,d3,d4,d5,d6,d7,d8))
      + (b1,b2,b3,b4,b5,b6,b7,b8) (mod 3)

      这步是错的：

      = (1=>a1,2=>a1,3=>a1,4=>a1,5=>a1,6=>a1,7=>a1,8=>a1)^(-1)·((a1=>c1,a2=>c2,a3=>c3,a4=>c4,a5=>c5,a6=>c6,a7=>c7,a8=>c8)^(-1)·(f1,f2,f3,f4,f5,f6,f7,f8))
      + (1=>a1,2=>a1,3=>a1,4=>a1,5=>a1,6=>a1,7=>a1,8=>a1)^(-1)·(d1,d2,d3,d4,d5,d6,d7,d8)
      + (b1,b2,b3,b4,b5,b6,b7,b8)

      = (a1=>1,a1=>2,a1=>3,a1=>4,a1=>5,a1=>6,a1=>7,a1=>8)·((c1=>a1,c2=>a2,c3=>a3,c4=>a4,c5=>a5,c6=>a6,c7=>a7,c8=>a8)·(f1,f2,f3,f4,f5,f6,f7,f8))
      + (1=>a1,2=>a1,3=>a1,4=>a1,5=>a1,6=>a1,7=>a1,8=>a1)^(-1)·(d1,d2,d3,d4,d5,d6,d7,d8)
      + (b1,b2,b3,b4,b5,b6,b7,b8)

      = (c1=>1,c1=>2,c1=>3,c1=>4,c1=>5,c1=>6,c1=>7,c1=>8)·(f1,f2,f3,f4,f5,f6,f7,f8))
      + (1=>a1,2=>a1,3=>a1,4=>a1,5=>a1,6=>a1,7=>a1,8=>a1)^(-1)·(d1,d2,d3,d4,d5,d6,d7,d8)
      + (b1,b2,b3,b4,b5,b6,b7,b8)
      }



orient := (a1.orient ∘ a2.permute.invFun) + a2.orient -- ∘是右边的函数作用到左边的对象

For example :
a is F, b is R, c is B

a: {
      permute: Perm (Fin 8) := (1=>a1,2=>a1,3=>a1,4=>a1,5=>a1,6=>a1,7=>a1,8=>a1)
      orient : Vector (Fin 3) 8 := (b1,b2,b3,b4,b5,b6,b7,b8)
}
b: {
      permute: Perm (Fin 8) := (a1=>c1,a2=>c2,a3=>c3,a4=>c4,a5=>c5,a6=>c6,a7=>c7,a8=>c8)
      orient : Vector (Fin 3) 8 := (d1,d2,d3,d4,d5,d6,d7,d8)
}
c: {
      permute: Perm (Fin 8) := (c1=>e1,c2=>e2,c3=>e3,c4=>e4,c5=>e5,c6=>e6,c7=>e7,c8=>e8)
      orient : Vector (Fin 3) 8 := (f1,f2,f3,f4,f5,f6,f7,f8)
}



(a.orient ∘ b.permute.symm + b.orient) ∘ c.permute.symm =
a.orient ∘ (b.permute.symm ∘ c.permute.symm)+ b.orient ∘ c.permute.symm

证明：
1. (b.permute.symm ∘ c.permute.symm) = (c1=>e1,c2=>e2,c3=>e3,c4=>e4,c5=>e5,c6=>e6,c7=>e7,c8=>e8)^(-1)·[(a1=>c1,a2=>c2,a3=>c3,a4=>c4,a5=>c5,a6=>c6,a7=>c7,a8=>c8)^(-1)]
  = (e1=>c1,e2=>c2,e3=>c3,e4=>c4,e5=>c5,e6=>c6,e7=>c7,e8=>c8)·(c1=>a1,c2=>a2,c3=>a3,c4=>a4,c5=>a5,c6=>a6,c7=>a7,c8=>a8)
  = (e1=>a1,e2=>a2,e3=>a3,e4=>a4,e5=>a5,e6=>a6,e7=>a7,e8=>a8)
2. 右边 = (e1=>a1,e2=>a2,e3=>a3,e4=>a4,e5=>a5,e6=>a6,e7=>a7,e8=>a8)·(b1,b2,b3,b4,b5,b6,b7,b8)
      + (c1=>e1,c2=>e2,c3=>e3,c4=>e4,c5=>e5,c6=>e6,c7=>e7,c8=>e8)^(-1)·(d1,d2,d3,d4,d5,d6,d7,d8)
3. 左边 = (c1=>e1,c2=>e2,c3=>e3,c4=>e4,c5=>e5,c6=>e6,c7=>e7,c8=>e8)^(-1)
·[(a1=>c1,a2=>c2,a3=>c3,a4=>c4,a5=>c5,a6=>c6,a7=>c7,a8=>c8)^(-1)·(b1,b2,b3,b4,b5,b6,b7,b8) + (d1,d2,d3,d4,d5,d6,d7,d8)]
4.








a: {
      permute: Perm (Fin 8) := (1=>a1,2=>a1,3=>a1,4=>a1,5=>a1,6=>a1,7=>a1,8=>a1)
      orient : Vector (Fin 3) 8 := (b1,b2,b3,b4,b5,b6,b7,b8)
}
b: {
      permute: Perm (Fin 8) := (a1=>c1,a2=>c2,a3=>c3,a4=>c4,a5=>c5,a6=>c6,a7=>c7,a8=>c8)
      orient : Vector (Fin 3) 8 := (d1,d2,d3,d4,d5,d6,d7,d8)
}
c: {
      permute: Perm (Fin 8) := (c1=>e1,c2=>e2,c3=>e3,c4=>e4,c5=>e5,c6=>e6,c7=>e7,c8=>e8)
      orient : Vector (Fin 3) 8 := (f1,f2,f3,f4,f5,f6,f7,f8)
}
bc:{
      permute: (a1=>c1,a2=>c2,a3=>c3,a4=>c4,a5=>c5,a6=>c6,a7=>c7,a8=>c8) * (c1=>e1,c2=>e2,c3=>e3,c4=>e4,c5=>e5,c6=>e6,c7=>e7,c8=>e8)
            = (a1=>e1,a2=>e2,a3=>e3,a4=>e4,a5=>e5,a6=>e6,a7=>e7,a8=>e8)
      orient : (a1=>c1,a2=>c2,a3=>c3,a4=>c4,a5=>c5,a6=>c6,a7=>c7,a8=>c8)^(-1)·(f1,f2,f3,f4,f5,f6,f7,f8)
            + (d1,d2,d3,d4,d5,d6,d7,d8) (mod 3)
      }
ab:{
      permute: (1=>a1,2=>a1,3=>a1,4=>a1,5=>a1,6=>a1,7=>a1,8=>a1) * (a1=>c1,a2=>c2,a3=>c3,a4=>c4,a5=>c5,a6=>c6,a7=>c7,a8=>c8)
            = (1=>c1,2=>c1,3=>c1,4=>c1,5=>c1,6=>c1,7=>c1,8=>c1)
      orient : (1=>a1,2=>a1,3=>a1,4=>a1,5=>a1,6=>a1,7=>a1,8=>a1)^(-1)·(d1,d2,d3,d4,d5,d6,d7,d8)
            + (b1,b2,b3,b4,b5,b6,b7,b8) (mod 3)
      }
a(bc):{
      permute: (1=>a1,2=>a1,3=>a1,4=>a1,5=>a1,6=>a1,7=>a1,8=>a1)
      * (a1=>e1,a2=>e2,a3=>e3,a4=>e4,a5=>e5,a6=>e6,a7=>e7,a8=>e8)
      = (1=>e1,2=>e1,3=>e1,4=>e1,5=>e1,6=>e1,7=>e1,8=>e1)
      orient : (1=>a1,2=>a1,3=>a1,4=>a1,5=>a1,6=>a1,7=>a1,8=>a1)^(-1)·
      ((a1=>c1,a2=>c2,a3=>c3,a4=>c4,a5=>c5,a6=>c6,a7=>c7,a8=>c8)^(-1)·(f1,f2,f3,f4,f5,f6,f7,f8) + (d1,d2,d3,d4,d5,d6,d7,d8))
      + (b1,b2,b3,b4,b5,b6,b7,b8) (mod 3)
      = (1=>a1,2=>a1,3=>a1,4=>a1,5=>a1,6=>a1,7=>a1,8=>a1)^(-1)·((a1=>c1,a2=>c2,a3=>c3,a4=>c4,a5=>c5,a6=>c6,a7=>c7,a8=>c8)^(-1)·(f1,f2,f3,f4,f5,f6,f7,f8))
      + (1=>a1,2=>a1,3=>a1,4=>a1,5=>a1,6=>a1,7=>a1,8=>a1)^(-1)·(d1,d2,d3,d4,d5,d6,d7,d8)
      + (b1,b2,b3,b4,b5,b6,b7,b8)
      = (a1=>1,a1=>2,a1=>3,a1=>4,a1=>5,a1=>6,a1=>7,a1=>8)·((c1=>a1,c2=>a2,c3=>a3,c4=>a4,c5=>a5,c6=>a6,c7=>a7,c8=>a8)·(f1,f2,f3,f4,f5,f6,f7,f8))
      + (1=>a1,2=>a1,3=>a1,4=>a1,5=>a1,6=>a1,7=>a1,8=>a1)^(-1)·(d1,d2,d3,d4,d5,d6,d7,d8)
      + (b1,b2,b3,b4,b5,b6,b7,b8)
      = (c1=>1,c1=>2,c1=>3,c1=>4,c1=>5,c1=>6,c1=>7,c1=>8)·(f1,f2,f3,f4,f5,f6,f7,f8))
      + (1=>a1,2=>a1,3=>a1,4=>a1,5=>a1,6=>a1,7=>a1,8=>a1)^(-1)·(d1,d2,d3,d4,d5,d6,d7,d8)
      + (b1,b2,b3,b4,b5,b6,b7,b8)
      }
(ab)c:{
      permute: (1=>c1,2=>c1,3=>c1,4=>c1,5=>c1,6=>c1,7=>c1,8=>c1)
            * (c1=>e1,c2=>e2,c3=>e3,c4=>e4,c5=>e5,c6=>e6,c7=>e7,c8=>e8)
            = (1=>e1,2=>e1,3=>e1,4=>e1,5=>e1,6=>e1,7=>e1,8=>e1)
      orient : (1=>c1,2=>c1,3=>c1,4=>c1,5=>c1,6=>c1,7=>c1,8=>c1)^(-1)·
            (f1,f2,f3,f4,f5,f6,f7,f8)
            + (1=>a1,2=>a1,3=>a1,4=>a1,5=>a1,6=>a1,7=>a1,8=>a1)^(-1)·(d1,d2,d3,d4,d5,d6,d7,d8)
            + (b1,b2,b3,b4,b5,b6,b7,b8) (mod 3)
      = (1=>c1,2=>c1,3=>c1,4=>c1,5=>c1,6=>c1,7=>c1,8=>c1)^(-1)·(f1,f2,f3,f4,f5,f6,f7,f8)
      + (1=>a1,2=>a1,3=>a1,4=>a1,5=>a1,6=>a1,7=>a1,8=>a1)^(-1)·(d1,d2,d3,d4,d5,d6,d7,d8)
      + (b1,b2,b3,b4,b5,b6,b7,b8)
      = (c1=>1,c1=>2,c1=>3,c1=>4,c1=>5,c1=>6,c1=>7,c1=>8)·(f1,f2,f3,f4,f5,f6,f7,f8)
      + (1=>a1,2=>a1,3=>a1,4=>a1,5=>a1,6=>a1,7=>a1,8=>a1)^(-1)·(d1,d2,d3,d4,d5,d6,d7,d8)
      + (b1,b2,b3,b4,b5,b6,b7,b8)
      }








For example :
a is F, b is R, c is B
a: {
permute: Perm (Fin 8) := (1=>2,2=>6,3,4,5=>1,6=>5,7,8)
orient : Vector (Fin 3) 8 := (2,1,0,0,1,2,0,0)
}
b: {
permute: Perm (Fin 8) := (1,2=>3,3=>7,4,5,6=>2,7=>6,8)
orient : Vector (Fin 3) 8 := (0,2,1,0,0,1,2,0)
}
c: {
permute: Perm (Fin 8) := (1,2,3=>4,4=>8,5,6,7=>3,8=>7)
orient : Vector (Fin 3) 8 := (0,0,2,1,0,0,1,2)
}

bc:{
permute: (1,2=>3,3=>7,4,5,6=>2,7=>6,8) * (1,2,3=>4,4=>8,5,6,7=>3,8=>7)
      = (1,2=>4,3,4=>8,5,6=>2,7=>6,8=>7)
orient : (1,2=>3,3=>7,4,5,6=>2,7=>6,8)^(-1)·(0,0,2,1,0,0,1,2)
      + (0,2,1,0,0,1,2,0)
      = (0,2,1,1,0,0,0,2) +
            (0,2,1,0,0,1,2,0)
      = (0,1,2,1,0,1,2,2) （mod 3）
}
ab:{
permute: (1=>2,2=>6,3,4,5=>1,6=>5,7,8) * (1,2=>3,3=>7,4,5,6=>2,7=>6,8)
      = (1=>3,2,3=>7,4,5=>1,6=>5,7=>6,8)
orient : (1=>2,2=>6,3,4,5=>1,6=>5,7,8)^(-1)·(0,2,1,0,0,1,2,0)
      + (2,1,0,0,1,2,0,0)
      = (2,1,1,0,0,0,2,0) +
            (2,1,0,0,1,2,0,0)
      = (1,2,1,0,1,2,2,0) (mod 3)
}
a(bc):{
permute: (1=>2,2=>6,3,4,5=>1,6=>5,7,8) * (1,2=>4,3,4=>8,5,6=>2,7=>6,8=>7)
      = (1=>4,2,3,4=>8,5=>1,6=>5,7=>6,8=>7)
orient : (1=>2,2=>6,3,4,5=>1,6=>5,7,8)^(-1)·(0,1,2,1,0,1,2,2) +
            (2,1,0,0,1,2,0,0)
      = (1,1,2,1,0,0,2,2) +
        (2,1,0,0,1,2,0,0)
      = (0,2,2,1,1,2,2,2) (mod 3)
}
(ab)c:{
permute: (1=>3,2,3=>7,4,5=>1,6=>5,7=>6,8) * (1,2,3=>4,4=>8,5,6,7=>3,8=>7)
      = (1=>4,2,3,4=>8,5=>1,6=>5,7=>6,8=>7)
orient : (1=>3,2,3=>7,4,5=>1,6=>5,7=>6,8)^(-1)·(0,0,2,1,0,0,1,2) +
            (1,2,1,0,1,2,2,0)
      = (2,0,1,1,0,0,0,2) +
        (1,2,1,0,1,2,2,0)
      = (0,2,2,1,1,2,2,2)
}
we can see a(bc) is equal to (ab)c












1.如果PieceState的orient定义为：某个第i位置，标记点为该坐标下的逆时针旋转n次，那分量就是+n
2. F :{
      permute: Perm (Fin 8) := (1=>2,2=>6,3,4,5=>1,6=>5,7,8)
      orient: (1,2,0,0,2,1,0,0)
}
3. R :{
      permute: Perm (Fin 8) := (1,2=>3,3=>7,4,5,6=>2,7=>6,8)
      orient: (0,1,2,0,0,2,1,0)
}
4. 试一下FR乘法定义是否符合我们的方向数定义:{
      permute := (1,2=>3,3=>7,4,5,6=>2,7=>6,8) * (1=>2,2=>6,3,4,5=>1,6=>5,7,8)
      = (1=>3,2,3=>7,4,5=>1,6=>5,7=>6,8)
      orient: ((1,2,0,0,2,1,0,0) ∘ (1,2=>3,3=>7,4,5,6=>2,7=>6,8).invFun) i + (0,1,2,0,0,2,1,0) i
            = (1+0,0+1,0+2,0+0,2+0,2+2,1+1,0+0)
            = (1,1,2,0,2,1,2,0)-- 第三个就错了
}
5. 那应该如何定义呢？定义可以取不同的点为0方向，还可以取顺时针或逆时针为+n。这两个自由度来定义。
      无论怎么定义，结合律按照这种运算肯定是满足的，问题就在于如何在这两个自由度上定义方向数。
{
      1.尝试：先分析一下之前的结构：
            1. F :{
                  permute: Perm (Fin 8) := (1=>2,2=>6,3,4,5=>1,6=>5,7,8)
                  orient: (a1,a2,a3,a4,a5,a6,a7,a8)
            }
            2. R :{
                  permute: Perm (Fin 8) := (1,2=>3,3=>7,4,5,6=>2,7=>6,8)
                  orient: (b1,b2,b3,b4,b5,b6,b7,b8)
            }
            3. 试一下FR乘法定义:{
                  permute := (1,2=>3,3=>7,4,5,6=>2,7=>6,8) * (1=>2,2=>6,3,4,5=>1,6=>5,7,8)
                  = (1=>3,2,3=>7,4,5=>1,6=>5,7=>6,8)
                  orient: ((a1,a2,a3,a4,a5,a6,a7,a8) ∘ (1,2=>3,3=>7,4,5,6=>2,7=>6,8).invFun) i + (b1,b2,b3,b4,b5,b6,b7,b8) i
                        = (a1+b1,a3+b2,a7+b3,a4+b4,a5+b5,a2+b6,a6+b7,a8+b8)
            }
            4.现在的问题是，找到合适的定义，是的FR的运算结果orient也符合定义。
}



w(gh) := w(g) + σ(g)^(-1)·w(h)
σ(g) = (第1=>2,2=>3,3=>1)
σ(g)^(-1) = (第2=>1,3=>2,1=>3)
手写意义：第1项= w(g)的第1项 + σ(g)^(-1)·w(h)的第1项 = w(g)的第1项 + w(h)的第“2”项
代码写法：第1项= a1.orient的第1项 + a2.orient的第“2”项 = a1.orient的第1项 + a2.orient ∘ a1.permute i