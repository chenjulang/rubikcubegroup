列一下前置知识：
    1.Sn的数量是An的2倍。

魔方第二基本定理（↔）：
目标问题：g∈ H , 则=>: , g∈G 吗？
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
    类似的某个引理，g_V456可以生成所有的g_V???(方向数w,v都是全零，棱块位置是id) 3循环,也就是g_V???X(id)
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
        2.g2的前两个排列的奇偶性是偶，偶：由引理11，G中元素可以复合得到({A8},{A12},id,id)，换句话说，由于g2∈ ({A8},{A12},id,id)，所以g2同样可以被G中元素可以复合得到。
    }
    至此，新目标g2∈ G证明完毕。
}
