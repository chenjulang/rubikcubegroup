证明最后阶段：
1.涉及定理：
    1.(精读)closure_three_cycles_eq_alternating: closure { σ : Perm α | IsThreeCycle σ } = alternatingGroup α
    2.mem_alternatingGroup: f ∈ alternatingGroup α ↔ sign f = 1
    3.需要一个类似这样的定理，但不止2个元素的：theorem mem_closure_pair {x y z : C} :
        z ∈ closure ({x, y} : Set C) ↔ ∃ m n : ℤ, x ^ m * y ^ n = z
    4.sign (h : IsThreeCycle σ) : sign σ = 1
    5.mem_alternatingGroup {f : Perm α} : f ∈ alternatingGroup α ↔ sign f = 1
    6.mem_ker (f : G →* M) {x : G} : x ∈ f.ker ↔ f x = 1
    7.(任何排列可表示成2循环的复合)def truncSwapFactors [Fintype α] (f : Perm α) :
        Trunc { l : List (Perm α) // l.prod = f ∧ ∀ g ∈ l, IsSwap g }
    8*.(任意2个2循环的乘积结果是一个3循环)IsSwap.mul_mem_closure_three_cycles {σ τ : Perm α} (hσ : IsSwap σ) (hτ : IsSwap τ) :
        σ * τ ∈ closure { σ : Perm α | IsThreeCycle σ }
    9*.swap_mul_swap_same_mem_closure_three_cycles {a b c : α} (ab : a ≠ b) (ac : a ≠ c) :
        swap a b * swap a c ∈ closure { σ : Perm α | IsThreeCycle σ }
    10*.(精读)(获取一个3循环的方式之一：)isThreeCycle_swap_mul_swap_same {a b c : α} (ab : a ≠ b) (ac : a ≠ c) (bc : b ≠ c) :
        IsThreeCycle (swap a b * swap a c)
    11.(找出一个排列变换中原参数不等于结果值的这些原参数；换句话说，改变值的那些原参数，不变的不需要)support (f : Perm α) : Finset α :=
      univ.filter fun x => f x ≠ x
    12.(获取一个3循环的方式之二：)：_root_.card_support_eq_three_iff : σ.support.card = 3 ↔ σ.IsThreeCycle
    13.prod_list_swap_mem_alternatingGroup_iff_even_length





魔方第二基本定理：注意***，这里的正方向标记将使用TW算法的标记法。
对于∀g∈ H (也就是广义的魔方群，可以拆散魔方) ，g在这里代表任意的一个魔方状态
则=>:，以下两命题可以互推(↔)
{
    g ∈ G (魔方群，可以通过6个基本操作生成的)
}
↔
{   以下3个命题都成立
    1.sgn(σ(g)) = sgn(ρ(g))  --(题外话：使用这个用来证明一个魔方不能单纯变化是：只交换一对角块位置，而棱块位置不变；
                            -- 也不能单纯变化是：只交换一对棱块位置，而角块位置不变)
    2.∑(12在上 i=1) wi(g) = 0 (mod 2) -- 应用起来，可以解释魔方单纯这样变化是不可能的：只翻转一个棱块的方向；
    3.∑(8在上 i=1) vi(g) = 0 (mod 3) -- 也不能单纯变化是：只翻转一个角块的方向，120 or 240都不行
}
证明：
已知集合{U,D,F,B,L,R}，记为Actions={U,D,F,B,L,R}
左推右：比较简单，
{
    1.符号相等：
        1.任意g∈G,可以表示成g=X1X2...Xk, 这里X1到Xk都是集合{U,D,F,B,L,R}之一。
        2.首先验证集合中单独6个元素满足sgn(σ(Xn)) = sgn(ρ(Xn))，这里略过（底层是因为因为4轮换？）。
        3,sgn是同态映射，也就是具有“保持运算”的性质，所以任意复合的结果，sgn都不变。
        4.sgn(σ(g)) = ∏(上k，下i=1)sgn(σ(Xi)) 由于g的定义，σ的同态性，sgn的同态性。
            = ∏(上k，下i=1)sgn(ρ(Xi)) 由于集合中6个元素都满足sgn(σ(Xn)) = sgn(ρ(Xn))
            = sgn(ρ(g)) 由于sgn的同态性，ρ的同态性，g的定义。
        例如:
        已知：sgn(σ(F)) = sgn(ρ(F)), sgn(σ(R)) = sgn(ρ(R))
            则sgn(σ(R)σ(F)) = sgn(σ(R)) + sgn(σ(F))  是由于sgn的同态性质
            = sgn(ρ(R)) + sgn(ρ(F)) 由于已知等式
            = sgn(ρ(R)ρ(F)) 是由于sgn的同态性质
    2.棱块向量的各分量的和为0(模2):
        做归纳法，对复合操作g所需的{U,D,F,B,L,R}中元素数量，记为l(g)作归纳：
        1.l(g)=1 成立，因为根据查w表可知。
        2.假设l(g)=k-1成立,也就是，假设g满足：可写成任意的n-1个复合，即：∀M_1∈Actions,∀M_2∈Actions,...,∀M_k-1∈Actions ,
        即g=M_1M_2...M_k-1，则有：
            ∑(上12，下i=1)wi(M_1M_2...M_k-1) = 0(mod 2)
        3.则l(g)=k，取g=X_1X_2...X_k，如何证明归纳成立？：
            1.由假设，分别取M_1，M_2,...,M_k-1分别取为X_1，X_2,...,X_k-1,
                可得到：∑(上12，下i=1)wi(X_1X_2...X_k-1) = 0(mod 2)
            2.命题1已知: w(xy) := w(x) + σ(x)^(-1)·w(y) ， 这里取x= X_1X_2...X_k-1 , y=Xk,
                得到：w(xy) = w(g) = w(X_1X_2...X_k-1) + σ(X_1X_2...X_k-1)^(-1)·w(Xk)
            3.将2中得到的等式左右取各分量的求和，仍然相等，
                得到：∑(上12，下i=1)wi(xy) = w(g) = ∑(上12，下i=1)wi(X_1X_2...X_k-1) + ∑(上12，下i=1)(σ(X_1X_2...X_k-1)^(-1)·w(Xk))_i
            4.小引理：因为X_1到X_k-1都满足σ(X_n)∈S12,σ是同态映射，即保持运算，因此σ(X_1)·σ(X_2)···σ(X_k-1) = σ(X_1X_2...X_k-1)
                因为等式左边都是S12群中的元素，封闭性知等式左边∈ S12,则=>:, 等式右边σ(X_1X_2...X_k-1)∈ S12
            5.观察3的等式右边加法的第二项：  ∑(上12，下i=1)(σ(X_1X_2...X_k-1)^(-1)·w(Xk))_i ，
                即：σ(X_1X_2...X_k-1)^(-1) 作用到 w(Xk) 以后 ， 取所有分量求和。
                因为 σ(X_1X_2...X_k-1)^(-1) 也是∈ S12, σ(X_1X_2...X_k-1)^(-1)作用到w(Xk)这个向量后，只是重新排列了各分量，求和是不变的，
                因此得到：∑(上12，下i=1)(σ(X_1X_2...X_k-1)^(-1)·w(Xk))_i = ∑(上12，下i=1)(w(Xk))_i
                以此为前提，因为Xk是Actions里面的单独一个元素，也就是归纳法l(g)=1的情况，因此∑(上12，下i=1)(w(Xk))_i = 0 (mod 2)
                总结得到：∑(上12，下i=1)(σ(X_1X_2...X_k-1)^(-1)·w(Xk))_i  = ∑(上12，下i=1)(w(Xk))_i = 0 (mod 2)
            6.我们将3得到的等式：w(g) = ∑(上12，下i=1)wi(X_1X_2...X_k-1) + ∑(上12，下i=1)(σ(X_1X_2...X_k-1)^(-1)·w(Xk))_i
                左右两边取模2，依然相等：
                w(g) = ∑(上12，下i=1)wi(X_1X_2...X_k-1) + ∑(上12，下i=1)(σ(X_1X_2...X_k-1)^(-1)·w(Xk))_i （mod 2）
                由1知道等式右边第1项：∑(上12，下i=1)wi(X_1X_2...X_k-1) = 0(mod 2)
                由5知道等式右边第2项: ∑(上12，下i=1)(σ(X_1X_2...X_k-1)^(-1)·w(Xk))_i = 0 (mod 2)
                因此w(g) = 0 (mod 2)
    3.角块向量的各分量的和为0(模3)。基本和2类似的步骤，这里略过。
}
右推左：
(总体思路：
  -- 分类讨论1得到小引理1：假设有状态g∈H,且∑(8在上 i=1) vi(g) = 0 (mod 3),则=>, g能通过有限次作用G中的元素（记为h），得到新的性质：v(gh)={0,0,...,0}。而且不改变棱块的方向数。
  -- 分类讨论2得到小引理2:假设有状态g∈H,且∑(12在上 i=1) wi(g) = 0 (mod 2) ， 则=>,g能通过有限次作用G中的元素（记为h），得到新的性质：w(gh)={0,0,...,0}。并且不改变角块的方向数。
  -- 通用小引理4.6：假设n>=3，对于任意集合M，假设M包含Sn中全体3循环，则=>， M >= An
  -- 小引理3***(最复杂的一个引理): 从已知的某些复合操作，能够覆盖所有的棱3循环（不改变方向数）；
      -- 而且，从已知的某些复合操作，能够覆盖所有的角3循环（不改变方向数）。
  -- 小引理11：由于小引理3，已覆盖所有3循环，再使用小引理4.6，因此可以得到 => 从已知的某些复合操作，能达到这个状态集合({A8},{A12},id,id)
  -- ValidCube的条件1，限制了当前状态x的范围，所以可以进行2种分类讨论：1.（奇X奇) 2.(偶X偶）
  -- 存在一个复合操作，作用一次到状态集合（奇X奇)上的某个元素后，新状态会属于新的状态集合(偶X偶）

  -- 以下就不是引理了，直接四行推理了：
  -- 因为对x的2种分类讨论都归化到了状态集合(偶X偶），即({A8},{A12},?,?)
  -- ValidCube的条件2, 然后使用小引理1，可以将({A8},{A12},?,?) 变成 ({A8},{A12},0,?)
  -- ValidCube的条件3, 然后使用小引理2，可以将({A8},{A12},0,?) 变成 ({A8},{A12},0,0)， 即({A8},{A12},id,id)
  -- 以上操作已经将状态x变成了这个状态集合里的某一个({A8},{A12},id,id)，因此直接使用小引理11，就可以直接证明x可以被复合得到。)
{
    魔方还原状态e ↔ g∈G,1.σ(g)=id,2.ρ(g)=id，3.w(g)={0,0,...,0}，4.v(g)={0,0,...,0}
    分情况讨论，这里分情况讨论并没有直接解决问题，而是分情况讨论的过程中会得到一些很有用的结论，
    换句话说，每一个分类讨论其实就是一个lemma:(1.只满足条件1+2+3；2.只满足条件1+2+4；3.只满足条件3+4)
    1.对于g∈H，对于棱块和角块位置不变,即σ(g)=id,ρ(g)=id，且w(g)={0,0,...,0}全零时的情况。
    换句话说，也就是全体位置都不变，棱块方向都不变时,换句话说只有可能是部分角块方向变了
        即已满足1,2,3，如果再给假设条件(3)的话，则=>: 满足g∈ G ，证明如下：
        0.修改目标命题：
            要证g∈ G,只需证新的目标命题：
            “此时的状态，都能变换回还原状态”
            给出变换的算法步骤，（或者弱一点，证明这样的变换存在即可）。
        （题外话：TW算法的步骤是，先变十字，然后是的v(g)全零，然后调整角块的位置保证3个轨道，然后调整棱块的位置保证2个轨道）
        1.小引理Lemma1：g1 = (R'D^2RB'U^2B)^2 ∈ G ,
            即R' D D R B' U U B R' D D R B' U U B
            g1的效果如下：
            则=>: g1可以保持UFR和DBL以外的块的方向和位置，只改变UFR和DBL的方向，
                    分别是UFR的方向数+2，DBL的方向数+1。
        2.以下会介绍一个完整的步骤，证明该状态g，可以通过Actions的复合得到（换句话说，就是能还原回初始魔方）：
            1.首先用小引理Lemma1中的g1还原F面的4个角块的方向数为0：
                1.(涉及F,g1)向UFR位置移入其他F面的块,比如UFL：这一步通过F操作即可，同样类似1的操作n次g1后，方向数+2n后必然符合mod3 = 0 。完成F面1个方向数还原。然后执行F'。
                2.(涉及F,g1)向UFR位置移入其他F面的块,比如DFL：这一步通过F^2操作即可，同样类似1的操作n次g1后，方向数+2n后必然符合mod3 = 0 。完成F面2个方向数还原。然后执行(F^2)⁻¹。
                3.(涉及F,g1)向UFR位置移入其他F面的块,比如DFR：这一步通过F'操作即可，同样类似1的操作n次g1后，方向数+2n后必然符合mod3 = 0 。完成F面3个方向数还原。然后执行F。
                (涉及F)注意，这里F面的第4个方向数,即UFR位置，还没处理，先留着。
        3.然后上一步的还没处理第4个方向数X就起作用了，因为下面要处理的是B面的4个方向数，通过g1和B的复合操作可以将B面的一个个方向数还原为0，具体步骤:
            1.(涉及B,g1)向DBL位置移入其他B面的块,比如UBL:这一步通过B操作即可，同样类似1的操作n次g1后，方向数+n后必然符合mod3 = 0 。因此B面第1个方向数还原。然后操作B'.
            2.(涉及B,g1)向DBL位置移入其他B面的块,比如UBR:这一步通过B^2操作即可，同样类似1的操作n次g1后，方向数+n后必然符合mod3 = 0 。因此B面第2个方向数还原。然后操作(B^2)⁻¹.
            3.(涉及B,g1)向DBL位置移入其他B面的块,比如DBR:这一步通过B'操作即可，同样类似1的操作n次g1后，方向数+n后必然符合mod3 = 0 。因此B面第3个方向数还原。然后操作B.
            4.小引理：假设角块的方向数求和后，模3为0,假设8个角块的方向数中，有7个方向数被以上步骤还原为0以后，则=>,第8个角块的方向数也还原成0 ，为什么呢？：
                由于前7个方向数还原操作后，7个方向数之和模3不会变，还是0，这是因为：
                还原操作涉及到的只有{F，B和g1},由于这3者之一，任意取一个记为X,都满足∑(8 i=1)v(X)_i=0 (mod 3)：
                    F和B通过查v表可知，
                    而g1则只需实际操作一次后，看到只修改了全体角块中2个角块的方向数，而且方向数一个+1，一个+2，所以也满足求和模3为0。
                换句话说，初始状态经过上述{F，B和g1}任意操作后，增加v(X)的各个分量，因为上述已知求和都是mod 3为0，增加这些分量以后再求和也是mod 3为0。
            5.观察现在还没还原的F面和B面中的角块的方向数，发现各剩下一个，分别在UFR和DBL位置，然后执行n次g1，则3号角块方向数+2n后必然符合mod3 = 0，详细步骤：
                (涉及g1)执行g1以后，其中3号方向数还原为0了，再根据小引理4，得到第8个角块也会还原为0。
        4.至此，已将8个角块的方向数全部还原为0，即v(g)={0,0,...,0}。而且w(g)还是全零。（是的，因为过程中操作g1,F,B不改变棱块的方向数。）
        5.1. 这里整个分类讨论1其实可以记成一个小引理：假设有状态g∈H,假设σ(g)=id,ρ(g)=id，且∑(8在上 i=1) vi(g) = 0 (mod 3) ， 则=>,
            g能通过有限次作用G中的元素，得到新的性质：v(g)={0,0,...,0}。
            5.1.2.lemma5: 其实引理可以再一般化一点：假设有状态g∈H,且∑(8在上 i=1) vi(g) = 0 (mod 3) ， 则=>,
            g能通过有限次作用G中的元素，得到新的性质：v(g)={0,0,...,0}。而且不改变棱块的方向数。
        5.因此假设中情况：σ(g)=id,ρ(g)=id，且w(g)={0,0,...,0}，
            再加上上述步骤，记为C1，C1的操作结果：v(g)={0,0,...,0} , 就得到了魔方群中的一个元素状态e，
            而上述步骤每个操作都是G中的元素，其复合C1也是元素，具有逆元C1^(-1)
            也就是g是e可以通过作用Actions集合的复合C1^(-1)得到。
            换句话说g可以表示成G中元素e·C1^(-1)，根据封闭性，还是在群G中，
            因此当前假设的情况g∈G成立。
    2.对于棱块和角块位置不变，即σ(g)=id,ρ(g)=id，且v(g)={0,0,...,0}全零时的情况。且满足(1),(2),(3)的话，
    换句话说，只有可能没有满足还原的条件是棱块的方向数w(g)。
    则=>: 满足g∈ G，
    证明如下：
        1.可以用到这个小引理Lemma2：g2 = LFR'F'L'U^2RURU^−1R^2U^2R， 则=>:
            g2可以保持其他块的方向和位置，只改变UF和UR的方向，分别是UF的方向+1，UR的方向的方向+1。
        2.也可能用到这个小引理lemma3: g_3= U R L' F L L F R L B B L L U' B B R R F F D D L L U' D'
            g_3可以保持其他块的方向和位置，只改变FU和FD的方向，分别是FU的方向+1，FD的方向的方向+1。
        2.1. 小引理lemma4：假设棱块的方向数求和后，模2为0,假设12个棱块的方向数中，有11个方向数能被G中若干元素作用后还原为0，则=>,第12个棱块的方向数也还原成0。
            为什么呢？：也是类似上面证明。
        2.当前状况要变成还原状态，过程类似于情况1中的证明：这里简单描述步骤：
            （题外话：TW算法中这一步简单很多。）
            (涉及g2,R，虽然用到R，但是R是“类交换子”中的一部分，换句话说，R一共执行了4次，相当于没有对角块方向数和位置，发生影响)
                先用g2和R逐个还原R面的4个方向数。至此已还原4个方向数。
                每次还原执行n次R，然后执行g2,然后复原使用（4-n）次R。
                顺序：UR,FR,RD,RB
            (涉及g2_R,B，虽然用到B，但是B是“类交换子”中的一部分，换句话说，B一共执行了4次，相当于没有对角块方向数和位置发生影响)
                还原B面的3个BU,BD,BL：然后g2的“R”变式，也就是用R面当成前面，直接操作g2,配合B,逐个还原B面的3个棱块。
                每次还原执行n次B，然后执行g2_R,然后复原使用（4-n）次R。
                顺序：UB,BD,LB
            (涉及g2_B,L,虽然用到L，但是L是“类交换子”中的一部分，换句话说，L一共执行了4次，相当于没有对角块方向数和位置发生影响)
                还原L面的1个LD：然后g2的“B”变式，也就是用B面当成前面，直接操作g2,配合L还原L面1个棱块。这一行前面的过程，L一共执行了2次。至此已还原8个方向数。
                (这一步故意留一个L面的LU没有还原方向数）
                每次还原执行n次L，然后执行g2_B,然后复原使用（4-n）次L。
                顺序：LD
            (涉及g2_L,F,虽然用到F，但是F是“类交换子”中的一部分，换句话说，F一共执行了4次，相当于没有对角块方向数和位置发生影响)
                还原F面的3个FL,FD:然后g1的“L”变式，也就是用L面当成前面，直接操作g1,配合F逐个还原这2个棱块。
                (这里故意留一个F面的FU没有还原方向数)
                每次还原执行n次F，然后执行g2_L,然后复原使用（4-n）次F。
                顺序：FL,FD
            现在的状态先分析一下，剩余的2个棱块UL,UF方向数只有下面的选择：分类讨论：
            根据小引理lemma4即2.1. ，也就是以上设计的所有公式涉及的{g1，g1变式,以及Actions中的元素}，都保持了一个性质：方向数求和模2为0。
                因此当前情况下σ(g)=id,ρ(g)=id，且v(g)={0,0,...,0}，也将得到性质w(g)={0,0,...,0}。v(g)还是全零。
            顺序：UL,UF一起还原。
            对2个棱块UL,UF方向数分类讨论：
            {
                1.0和1:由引理2.1的使用，这种情况不可能存在,不需要讨论。因为mod 2 ≠ 0 。
                2.0和0:不用操作，已还原方向数。
                3.1和0:由引理2.1的使用，这种情况不可能存在,不需要讨论。因为mod 2 ≠ 0。
                4.1和1:执行一次g1的“L”变式,这样就还原了所有棱块方向数。
            }
        3.至此已还原了棱块的方向数。并且过程中不改变角块的方向数。加上原有假设全体位置不变（在过程中也不受影响），因此已达到魔方还原状态e。
        3.0 这里其实可以记成一个小引理：假设有状态g∈H,假设σ(g)=id,ρ(g)=id，且∑(12在上 i=1) wi(g) = 0 (mod 2) ， 则=>,
            g能通过有限次作用G中的元素，得到新的性质：w(g)={0,0,...,0}。
            3.0.1.lemma6: 这里可以一般化引理：假设有状态g∈H,且∑(12在上 i=1) wi(g) = 0 (mod 2) ， 则=>,
            g能通过有限次作用G中的元素，得到新的性质：w(g)={0,0,...,0}。并且不改变角块的方向数。
        因此当前假设的情况g∈G成立。
    （目前来看，思路是：为了达到还原成e的新目标，而分情况讨论，每次讨论都故意缺一个充要条件的其中一条，
        其实是1/4的充要条件（σ(g)=id,ρ(g)=id，w(g)={0,0,...,0}，v(g)={0,0,...,0}）。
        可以发现上面两种情况无意中独立出来2条引理，是下面的关键。）
    3.现在考虑这种情况：σ(g)=id,ρ(g)=id，即棱块和角块位置不变，且满足(1),(2),(3)的话，也可以满足g∈ G。（换句话说，这里直接缺了e中的2条条件）：
        1.由上面5.1.引理知道，存在有限操作X1，g状态可以变成新的状态g_2,然后拥有性质v(g)={0,0,...,0}。
        2.由上面3.0 引理知道，存在有限操作X1，g_2状态可以变成新的状态g_3,然后拥有性质w(g)={0,0,...,0}.
        3.至此就集齐了e状态的4个充要条件。
        4.也就是说，当前假设的情况g∈G成立。
    4. 考虑棱块和角块方向不变时的情况g，即w(g)={0,0,...,0}，v(g)={0,0,...,0}，且满足(1),(2),(3)的话，即缺了e的前2个条件的情况。
        看能不能再独立出一条充要的引理。
        要证明状态g属于群G，当前证明目标变成新目标：
            g可以通过若干Actions复合操作变成还原状态e接口。
        也就是通过若干Actions复合后，能拥有性质σ(g)=id,ρ(g)=id。
        这种情况的状态的全体记为
    H':即w(g)={0,0,...,0}，v(g)={0,0,...,0}的H中的状态。也就是棱块和角块方向数不变时的情况。只可能改变位置。
        然后定义一个交集G',
    G' := H' ∩ G ， 换句话说，就是魔方群中方向数不变的元素集合
    我们下面将给出3个这样的G'中的元素,他们当然满足：
        1.不改变全体方向数，即w(g)={0,0,...,0}，v(g)={0,0,...,0}
    然后通过这3个操作的复合将任意一个G'中的方向分量全为0的状态A1，变换到原始状态e，也就是把位置也还原了,这就解决了我们的新目标。
    4.1.g3 = RU'RURURU'R'U'R^2 (即R U' R U R U R U' R' U' R R): 是一个棱块位置3循环，也就是σ(g3) =(1,2,4)。方向数都是0。
    4.2.第二个g4 = R' F' F' F' R' B B R' R' R' F' R' B B R' R'，是一个角块位置3循环, ρ(g4) =(2,4,3)
    4.2.错误的？第二个g4_2 = LF'LD^2L'FLD^2L^2 :是一个角块位置3循环, ρ(g4) =(4,5,6)
    4.3.第三个g5 = RUR'F'RUR'U'R'FR^2U'R'U'(即R U R' F' R U R' U' R' F R R U' R' U')
        :是2个2循环:2个棱块的2循环，2个角块的2循环σ(g5) =(1,2) ρ(g5) =(2,3)
    下面将描述方向不变，只有位置变化时，如何变成e的具体步骤，也就是还原位置的具体步骤：
    4.4 An :Sn置换群中，是偶的那些元素（即偶置换），这些组成的群。也称为“n元交错群”。
    元素个数是Sn的一半，即1/2，记为|Sn/An|=2 ???
    4.5 N:由G'中的全体元素，抽取2个位置变换拼成的的向量。向量里有两项内容（分别是12项向量，和8项向量），
        从定义知： N={(σ(g) , ρ(g)) |g∈G' } < SE×SV。（备忘：N定义中的g∈G', g不会改变全体块的方向数）
    4.6 小引理：假设n>=3，对于任意集合M，假设M包含Sn中全体3循环，则=>， M >= An
        证明：因为P.180的9.4.1（用到P.56的引理3.4.1），即Sn中全体3循环元素生成的群，就是An。
        因此M中只抽出Sn中的全体3循环，就能生成An了M集合肯定就>=An集合了。
        以此为前提，我们可以把A8 = <S8中的所有3循环> ， A12 = <S12中的所有3循环> ，
    4.7
            注意：这里用到的操作是g3,g4,g5,X1^(n)X2X1^(-n)（交换子中X1是{L2,R2,F,B,U,D}复合的）因为这样的集合保证了方向数不会改变,而且角块位置不变。
            0.1. 交换子公式小引理：X1X2X1^(-1)这类的操作，假设X1取的是Actions的复合，X2取的是棱块3循环集合的元素，这里特指{g3}，
                记g3影响到的棱块位置为第i,j,k，这个3循环记为(i,j,k)，则=>:
                X1X2X1^(-1)的操作，不改变全体角块方向数和位置。
                全体棱块方向数可能会变化的。
                因为已知任意状态g，通过X1操作后，会有所影响的棱块位置集合，记为E1 = {l1,l2,l3,...},
                X1操作效果是：{l1=>m1,l2=>m2,l3=>m3,...}
                则=>：
                {
                    1.如果E1中只存在一个初始位置为l1,通过X1操作后到达集合{i,j,k}中任意一个的，则=>:,
                        假设是{i,j,k}中的i
                        X1X2X1^(-1)的操作的结果会是一个不改变全体角块方向数和位置，这样的3棱块循环：
                        (i,j,k) → (l1,j,k) →(X2作用) → (k,l1,j), 也就是(k,l1,j)这样的新的3棱块循环，但全体棱块方向数可能改变。
                        {i,j,k}的其他情况类推可知：
                        假设是{i,j,k}中的j:(i,j,k) → (i,l1,k) →(X2作用) → (k,i,l1)这样的新的3棱块循环，但全体棱块方向数可能改变。
                        假设是{i,j,k}中的k:(i,j,k) → (i,j,l1) →(X2作用) → (l1,i,j)样的新的3棱块循环，但全体棱块方向数可能改变。
                    2.其他情况的定理目前先不探究：略。
                }
                    证明：分类讨论：
                    {
                        1.对于全体角块：{
                            1.对于方向数：
                                先执行X1,这一步肯定有可能修改方向数的，设影响到方向数的4个位置是第{P1,P2,P3,P4,...,Pn}，（先记这4个位置的执行这一行前的方向数分别是a1,a2,a3,a4,...an）
                                    设改变的详细是{P1:a1→b1,P2:a2→b2,P3:a3→b3,P4:a4→b4,...Pn:an→bn},把这个过程记为函数f1,方向数分别变成了。
                                然后执行X2时已知不改变全体角块的方向数，这一步结束后，对于P1,P2,P3,P4,...,Pn来说，都没改变方向数，还是b1,b2,b3,b4,...,bn。
                                然后执行X1^(-1)，对于P1,P2,P3,P4,...,Pn的方向数，相当于执行了一次f1^(-1),即f1的逆映射，
                                分别改变详细是：{P1:b1→a1,P2:b2→a2,P3:b3→ba,P4:b4→a4,...Pn:bn→an},因此又变回了a1,a2,a3,a4,...an方向数，因此不变。
                            2.对于位置：
                                先执行X1,这一步肯定改变位置的，设影响到的4个角块记为{V1,V2,...,Vn}。（执行这一行前这4个角块的位置分别记为第a1,第a2,...,第an）
                                    设改变的详细是{V1:第a1→第b1,V2:第a2→第b2,...,Vn:第an→第bn},把这个过程记为函数f2,位置分别变成了第b1,第b2,...,第bn。
                                然后执行X2,已知不改变全体角块的位置，这一步结束后，对于V1,V2,...,Vn来说，都没改变位置,还是第a1,第a2,...,第an。
                                然后执行X1^(-n)，对于V1,V2,...,Vn的位置，相当于执行了一次f2^(-1),即f2的逆映射，
                                分别改变详细是：{V1:第b1→第a1,V2:第b2→第a2,...,Vn:第bn→第an},因此又变回了第a1,第a2,...,第an的个位置，因此不变。
                        }
                        已知任意状态g，通过X1操作后，会有所“影响”（有动的都是）的棱块位置集合，记为E1 = {l1,l2,l3,...},X1操作效果是：{l1=>m1,l2=>m2,l3=>m3,...}
                        如果E1中只存在一个初始位置为l1,通过X1操作后到达集合{i,j,k}中的任意一个。
                        2.分类讨论：{
                            1.如果只有l1操作X1后到达了位置j：分类讨论棱块位置：--
                                {
                                    注意这里全体棱块 = {i,j,k} + {E1 - j} + {E1 + i + k}外的全体棱块
                                    换句话说= E1 + {i,k} + {E1 + i + k}外的全体棱块
                                    1.对于{E1 + i + k}外的全体棱块：这个集合中任意一个元素，作分析：
                                    由于X1操作改变了E1中的位置和方向，
                                    但X2没有对E1中任何位置和方向发生变化，
                                    所以X1^(-1)操作后E1中的位置和方向就还原了。
                                    2.对于X1操作前的位置{i,k}的这两个棱块:
                                        由于只有j被到达了，换句话说，{i,j,k}只有j收到了X1操作的影响,因此操作X1后{i,k}的方向和位置不变
                                        操作X2后，位置变化：{第i→第j,第k→第i}
                                        然后操作X1^(-1):
                                        分类讨论：{
                                            1.X1操作前的位置i：因为经过X2后移到了第j，会涉及方向和位置变化：
                                                由于X1的位置操作变化有：{第l1→ 第j}
                                                因此通过X1^(-1)操作后，当前分析的棱块位置会变到第l1。
                                            2.X1操作前的位置k：因为经过X2后移到了第i，不受X1^(-1)的变化影响，方向数和位置不变。
                                        }
                                        总结就是：{第i→第l1,第k→第i}
                                    3.对于X1操作前的位置E1这些棱块:分类讨论：
                                        {
                                            1.对于第l1位置的棱块：
                                                X1操作改变了方向和位置，位置到了第j位置，
                                                X2操作改变了方向和位置，位置到了第k位置，
                                                X1^(-1)操作后，由于X1的作用范围集合E1，和X2的作用范围集合{i,j,k}只有交集第j位置，
                                                    而目前分析的棱块到了第k位置，不会收到X1的作用影响，保持第k位置。
                                                总结这个棱块的变化：{第l1→第k}
                                            2.对于第j位置的棱块：
                                                X1操作改变了方向和位置，位置到了某个位置记为第j_2 ≠ 第j，方向数记为v_2,j_2在X1影响范围内,即j_2∈ E1
                                                    由于X1的作用范围集合E1，和X2的作用范围集合{i,j,k}只有交集第j位置，这个j_2 ∉ {i,j,k}
                                                X2操作中，由于j_2 ∉ {i,j,k},当前棱块的方向和位置不变，位置还是第j_2，方向数还是v_2。
                                                X1^(-1)操作中,方向数得到了还原，位置也因此得到还原。
                                                总结变化：{第j→第j}
                                            3.E1除了第l1位置,还有除了第j位置以外的棱块：
                                                X1操作改变了方向和位置，
                                                但X2不改变方向和位置，因为E1中只有l1到达了X2的作用区域中。
                                                因此X1^(-1)操作后目前分析的这些“E1除了第l1位置,还有除了第j位置以外的棱块”就恢复了原来的方向和位置。
                                        }

                                }
                                总结上面得到仅有的3个位置变换的：{第i→第l1,第k→第i}，{第l1→第k}，
                                    合并起来就是{第i→第l1,第k→第i，第l1→第k} ，写成3循环就是(i,l1,k) = (k,i,l1)，得证。
                            2.如果l1操作X1后到达了位置j：类似推理
                            3.如果l1操作X1后到达了位置k：类似推理
                        }
                    }
            0.2. 推论：直接使用0.1引理，但是再加一个假设：全体棱块方向数不变化,即要求X1不改变方向数
            （有一个方法很容易满足X1不改变方向数，只要组成它的元素都在这个集合中即可:{L2,R2,F,B,U,D}，当然也有其他集合可以.）
                则=>:
                使用0.1引理得到的“3循环，但全体棱块方向数可能改变”，就可以变成单纯的3循环。换句话说，就是保证了全体棱块方向数不变。
            1.小引理：任意H'中的元素X1，假设X1为任意满足这样的形式：((1),(i,j,k)),（这样的形式的确存在的，举例：g3，但是否能任意取i,j,k,还不确定），
            换句话说，就是棱块位置是某个3轮换，角块位置不变，棱块和角块方向数为0。
            则=>: X1状态能经过有限次G'中的操作，得到状态e  ∈ G。
            证明：
            这里的证明其实就是给出这个有限次G'中的操作，记为G1
            所以下面通常要涉及分类讨论(i,j,k)中3个分量的相对位置，具体步骤:
              首先把棱块还原成e：
                g3:R U' R U R U R U' R' U' R R
                σ(g3) =(1,2,4)
                目标：任意棱块3循环（棱块方向数为0，角块位置为id），可以用g3和g3变式和交换子模式还原成e。
                （硬要一个个列举的话，12个选3循环有220中不同的。）
                证明：
                1.对E1,E2,E3进行全体分类。
                注意*：以下都是讨论单纯的3循环，方向数不变。
                {
                1.1个面包含了3个棱块，这样的面有1个的情况：
                    {
                    1.3个棱块都在某个面：
                        1.逆时针顺序是E1,E2,E3:使用若干次g3或g3变式，将E1先恢复，其他自动也会恢复。因此得到e。 -- checked
                        2.逆时针顺序是E1,E3,E2:使用若干次g3或g3变式，将E1先恢复，其他自动也会恢复。因此得到e。
                    }
                上述以外的情况里，也就是“1个面包含了3个棱块，这样的面有0个的情况”：
                2.1个面包含了2个棱块，这样的面只有3个的情况：
                    {
                    E1,E2,E3只有这种相对位置：
                    -- todo : 交换子第一操作可以是：{U,D,F,B,L2,R2}
                    -- g3:R U' R U R U R U' R' U' R R
                    -- σ(g3) =(1,2,4)
                    1.E1,E2,E3的相对位置是类似{1,2,6}这样的，集合中取:交换子要用到中层变换。-- to check
                    }
                3.1个面包含了2个棱块，这样的面只有2个的情况：
                    { E1,E2,E3相对位置分类
                    1.类似{1,3,9}这样的:交换子
                    2.类似1,3,7:用到中层的交换子。
                    3.1,4,8:交换子。
                    4.1,4,12：交换子。
                    }
                4.1个面包含了2个棱块，这样的面只有1个的情况：
                    {
                        1.1,3,10:交换子。
                    }
                5.1个面包含了2个棱块，这样的面有0个的情况：
                    首先筛选剩下了这些可供E2,E3选择{BL,DL,BR,DR,BU,BD,DF} = {8,12,7,10,3,11,9}：
                    由于对称性，BL→BR,DL→DR,BU→DF,BD , 即{7,10,9,11}
                    E2从这4个归化的里面选：
                    {
                    1.1,7,12:2次交换子 -- to check
                    2.1,10,8:2次交换子
                    3.1,9,7:2次交换子。
                }
            2.小引理：任意H'中的元素X1，假设X1为任意满足这样的形式：((i,j,k),(1)),（这样的形式的确存在的，举例：g4，但是否能任意取i,j,k,还不确定），
            换句话说，就是角块位置是某个3轮换，棱块位置不变，棱块和角块方向数为0。
            则=>: X1状态能经过有限次G'中的操作，得到状态e  ∈ G。
            证明：
            然后把角块还原成e：
                g4: R' F' F' F' R' B B R' R' R' F' R' B B R' R'
                ρ(g4) =(2,4,3)
                目标：任意角块3循环（角块方向数为0，棱块位置为id），可以用g4和g4变式和交换子模式还原成e。
                （硬要一个个列举的话，8个选3循环有56种不同的。）
                证明：
                直接对V1,V2,V3进行全体分类:
                {
                1.1个面包含了3个角块，这样的面有1个的情况：
                {
                    1.3个角块在同一个面：
                    {
                        1.V1,V2,V3逆时针排列：执行若干次g4变式，将V1先恢复，则其他也跟着恢复。得到e。-- checked
                        2.V1,V2,V3顺时针排列：执行若干次g4变式，将V1先恢复，则其他也跟着恢复。得到e。
                    }
                }
                上述1除外的情况里，也就是“1个面包含了3个角块，这样的面有0个的情况”还有：
                2.1个面包含了2个角块，这样的面有3个的情况：
                {
                    1.2,1,7:交换子。-- checked 首先需要一个(4,2,1) = g4_B, 然后拼一个交换子B B g4_B B B
                    2.2,4,X:分类：
                    {
                        2,4,8: 3次交换子。
                        2,4,5: D' (2,4,8) D 即可。
                        2,4,7: D' (2,4,6) D 即可。
                        2,4,6: 3次交换子。-- checked
                            2，4，6举例：
                            先搞一个(2,6,3)交换子，记下来：D' L L g4 L L D
                            从复原状态开始，先使用(2,4,3)
                                然后使用(2,3,6) 2次，把3还原，
                            最终得到（2，4，6）: g4 (D' L L g4 L L D) (D' L L g4 L L D)
                            简化成了：R R D D L L D R R D' L L D R R D R R
                    }
                    {
                        2,3,5:交换子。
                        2,3,8:交换子。
                    }
                    4.2,7,X:
                    {
                        2,7,1:上面已存在。
                        2,7,4:上面已存在。
                        2,7,5:L L (2,4,7) L' L'即可。
                        2,7,8:L L (1,2,7) L' L'即可。
                    }
                    5.2,6,X:
                    {
                        2,6,4:上面已存在。
                        2,6,8:B B (2,6,7) B' B'即可。
                    }
                    6.2,5,X:
                    {
                        2,5,4:上面已存在。
                        2,5,3:上面已存在。
                        2,5,7:上面已存在。
                        2,5,8:B B (2,5,4) B' B'即可。
                    }
                    7.2,8,X:
                    {
                        2,8,1:上面已存在。
                        2,8,3:上面已存在。
                        2,8,4:上面已存在。
                        2,8,5:上面已存在。
                        2,8,6:上面已存在。
                        2,8,7:上面已存在。
                    }
                }
                3.1个面包含了2个角块，这样的面有2个的情况：
                {
                    1.2,1,X: 不存在，所以不用讨论。
                    2.2,4,X: 不存在
                    3.2,3,X: 不存在
                    4.2,7,X: 不存在
                    5.2,6,X: 不存在
                    6.2,5,X: 不存在
                    7.2,8,X: 不存在
                }
                4.1个面包含了2个角块，这样的面有1个的情况：
                {
                    不存在，所以不用讨论。
                }
                5.1个面包含了2个角块，这样的面有0个的情况：
                {
                    不存在，所以不用讨论。
                }
                }
        2.1 小引理推论***：如果从e出发，复合一些G中的交换子和g3变式和g4变式，则=>:
            能经过有限次G'中的操作，得到((i,j,k),(1))，其中第一个分量(i,j,k)满足：1<=i<=j<=k<=12。
            而且留意一下，全体棱块和角块的方向数不变，全体角块的位置也不变。
            换句话说，对于任意1<=i<=j<=k<=12，得到的这个变量(i,j,k)，也就是任意的S12中的任意3循环的状态，
            都能从((1,2,4),(1))经过有限次G'中操作，得到第一个分量能变成这个任意的3循环。
    5.总结：
    目标问题：g∈ H , 则=>: g∈G 吗？
    3个条件中第一个把H针对位置先分类，也就是针对(S8 X S12)分成了两个集合，分类讨论：
    对于状态g∈H
        1.有一个3.0小引理，由条件(2),即有求和棱块模2为0，因此g可以通过有限G中步骤，这里记为X1，得到新的性质：w(gX1) = {0,0,...,0}。
            而且不改变角块的方向数，因此保持了条件(3)。
        2.有一个5.1小引理，由条件(3),即求和角块模3为0，因此g·X1可以通过有限G中步骤，这里记为X2，得到新的性质：v(gX1X2) = {0,0,...,0}。
        3.我们先介绍一些通用的已知知识：(S8 X S12)有一个“子群”，记为G1：（A X B），（A X B）= （A1 X B1）∪ (A2 X B2) ,换句话说就是(奇X奇）∪（偶X偶）这个并集。
            其中A1是S8中全体奇的置换，A2是S8中全体偶的置换，
            B1是S12中全体奇的置换，B2是S12中全体偶的置换。
            很明显，这两个集合（A1 X B1），(A2 X B2) 是没有交集的。
            可以证明这个子群是封闭的。因为（奇X奇）+（偶X偶） = （奇X奇）
        3.1 同样用是否符合条件(1)来将H分成两个子集H1，H2的话。记符合条件(1)的为H1，不符合的为H2。其实这个H1就是G1， H1 = G1，因为H1和G1的定义是一样的。
            H1经过P映射就是（A X B）；
            H2经过P映射就是 (S8 X S12) - （A X B）；
        4.由条件(1),g有性质：棱和角的位置排列的符号数相等，换句话说就是（奇X奇） or （偶X偶）。
            所以：g属于3.1中的H1，g'是属于3中所说的(A X B)这个子群的。
            即g∈H1,g'∈(A X B)
            根据3的分析可知G1=H1是一个(S8 X S12)的子群，g∈H1,g经过X1，X2后变成了新状态gX1X2，这里记为g2。
        因此可以把当前目标g∈G，转化成新的目标：g2∈ G。(因为X1，X2都是G中元素)
        5. (S8 X S12)可以分成4个不相交子集的并集：奇X奇 ∪ 偶X偶 ∪ 奇X偶 ∪ 奇X偶。
            这4个子集的元素个数都相等，因为An（偶置换）是Sn的指数为2的子群。Sn除了An的剩下的当然都是奇置换。
        6.分析g2具有性质：w(g2) = {0,0,...,0}，v(g2) = {0,0,...,0}。而且对g2经过P映射后的g'(仍然是g',因为g到g2只改变了方向数)。
        7.右推左过程中，条件(1)让我们把g'的范围进一步缩小了，条件（1）换句话说，就是角块和棱块的排列的符号相等。
            换句话说，角块的排列和棱块的排列，同为奇，或者同为偶。因此g'∈ 奇X奇 ∪ 偶X偶 。
        8.我们这里把 (S8 X S12)分成两个子集，它们的元素个数相等。分别是
            1.（奇X奇 ∪ 偶X偶），记为J1；
            2.（奇X偶 ∪ 偶X奇），记为J2。
            由3.1分析可知，H1经过P映射得到J1，H2经过P映射得到J2
        9.G通过映射P得到集合G',由于我们已证明左推右，当然可以用。所以G中的元素都是满足条件(1)的性质：“角块的排列和棱块的排列，同为奇，或者同为偶”。
            因此G'属于8中定义的J1。
        10.由于2.1小引理推论，g_E124和g_E123可以生成所有的g_E???(方向数w,v都是全零，角块位置是id) 3循环，也就是(id)Xg_E???
        类似的某个引理(这里没详细证明)，g_V456可以生成所有的g_V???(方向数w,v都是全零，棱块位置是id) 3循环,也就是g_V???X(id)
        11.小引理：无前提假设,则=>,g_E???和g_V???可以与G中元素复合生成({A8},{A12},id,id)这样的任意元素。
        证明：由于({A8},{A12},id,id) = ({A8},(id),id,id) + ((id),{A12},id,id)  , 这里的写法不太严谨，换句话说，({A8},{A12},id,id)这个集合里面任意的一个元素，
            比如(a1,a2,id,id) = ((b1,b2,...,b8) ,(c1,c2,...,c12),id,id)
            则由g_E???复合运算得到元素C1：((b1,b2,...,b8) ,(id),id,id)
            g_V???复合运算得到元素D1：((id),(c1,c2,...,c12),id,id)
            将D1作用到魔方状态C1上，就得到了：((b1,b2,...,b8) ,(c1,c2,...,c12),id,id),也就是({A8},{A12},id,id)中的任意一个元素。
        12.小引理：g2是否一定能经过有限步G中操作，得到集合({A8},{A12},id,id)中的某一个元素
        对g2的前两个排列的奇偶性进行分类讨论，条件(1)把g2的范围缩小成了（奇X奇) or (偶X偶）:分类讨论：
        {
            1.g2的前两个排列的奇偶性是奇，奇：详细步骤：
                先执行一次g5,g5保持了棱和角方向数不变，保持id，id。
                然后将前两个排列的奇偶性都变换了，因此g2g5的前两个排列的奇偶性是偶，偶，因此转化成下面第2种情况。
            2.g2的前两个排列的奇偶性是偶，偶：由小引理11，G中元素可以复合得到({A8},{A12},id,id)，换句话说，由于g2∈ ({A8},{A12},id,id)，所以g2同样可以被G中元素可以复合得到。
        }
        至此，新目标g2∈ G证明完毕。
}
