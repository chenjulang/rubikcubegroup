




用一个小笛卡尔积群，模拟一下SExSV这样的群如何被排列同奇偶，不同奇偶，分成2个子群。
比如S2xS3

列一下已知结论：
    1.Sn的数量是An的2倍。
    2.


目标问题：g∈G 吗？
3个条件中第一个把H针对位置先分类，也就是针对(S8 X S12)分成了两个集合，分类讨论：
对于状态g∈H
条件（1）把g∈ H分成了2类：分类讨论
{
    1.g满足：棱和角是同奇偶的排列，记为G1：
        {
            1.有一个5.1小引理，因为有求和棱块模2为0，因此可以通过有限步骤，这里记为X1，得到新的性质：w(g?) = {0,0,...,0}。
            2.有一个3.0小引理，因为有求和角块模3为0，因此可以通过有限步骤，这里记为X2，得到新的性质：v(g?) = {0,0,...,0}。
            3.我们考虑一个通用的情况：(S8 X S12)有一个子群：（A X B）= （A1 X B1）∪ (A2 X B2) ,
                其中A1是S8中全体奇的置换，A2是S8中全体偶的置换，
                B1是S12中全体奇的置换，B2是S12中全体偶的置换。
                很明显，这两个集合（A1 X B1），(A2 X B2) 是没有交集的。
                可以证明这个子群是封闭的。因为（奇X奇）+（偶X偶） = （奇X奇）
            4.对于当前分析的集合G1，根据3的分析可知G1是一个(S8 X S12)的子群，而且经过X1，X2后变成了新状态（这里面其实就用了条件(2)和条件(3)）
                ，这里记为g2。
                因此可以把当前目标g∈G，
            转化成新的目标：g2∈ G。
            5. 条件(1)把(S8 X S12)分成了2个等大小的子集。
            6.分析g2状态：w(g2) = {0,0,...,0}，v(g2) = {0,0,...,0},对g2经过P映射后，属于5中说的2个子集分类讨论：{
                1.g2在 （奇X奇 ∪ 偶X偶）中：

                2.g2在 （奇X偶 ∪ 奇X偶）中：
            }



        }
    2.g满足：棱和角是不同奇偶的排列，记为G2：
        {

        }
}
