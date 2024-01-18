正在阅读Adventures in group theory Rubiks cube,
    Merlins machine, and other mathematical toys (Joyner, David) --ok
看完第5章，--doing 1.一组魔方操作，最多重复操作1260次就可以还原，不多吧，操作为m = RU2D−1BD−1 。柯西定理有此话题更多的讨论。 --ok
还是得从书的第一页开始，不懂的举例子|然后要将关键定理用我们自己的理解记下来，不然会忘|跳过非魔方的部分--ok
|定理不一定要详细证明，但是名词一定要彻底理解，这样证明就只是一种技巧 ｜写记录的时候先写个总概括--ok

实在不懂的找gpt举例子：
关键定理自我理解记录：
1.P (f ) :是一个矩阵，其中 f 是一个排列，举例；
    写成f=（2，1，3）， P(f)就是
   [[0 1 0]
    [1 0 0]
    [0 0 1]], 也就是第1行第2列，第2行第1列，第3行第3列，根据f来的，都是1，其他为0
2.Sn : 有时代表任意排列组成的集合，元素数量当然就是n!个
3.与有关的魔方引理lemma 3.2.3：r^−1sr复合操作，能直接修改首位位置，修改效果是直接通过r映射。
    举例：
    i是uf位置,j是uf位置
    有一个操作s效果是3循环：s:= uf → ul → ur → uf ,
    另一个操作r := F^2
    则：
    r^−1sr的效果是r(i)位置 → r(j)位置
    因为r(uf)= df,所以：
    df → ul → ur → df
4.对于排列f，f的order定义:使得 f^N = 1 > 0 的最小整数 N 称为 f 的阶数order
5.对于排列f，f是even或odd的，意思是：swap(f ) 是even或odd，也就是f的逆序数之和
    逆序数具体定义：
    定义 3.1.1. 让 f : 跟n → 跟n 是一个排列组合，让
    和f (i) = #{j > i | f (i) > f (j)}, 1 ≤ i ≤ n − 1.
    swap（f ) = 和f (1) + . . . + 和f (n − 1)
6.算法：生成所有排列的方式竟然如此简单 3.4
7.超级翻转游戏：只翻转所有棱块，其他角块和中心块不影响
8.Sn ：任意排列(一个排列可以用一个向量来表示)组成的集合,也可以叫做“symmetric对称群”，
    因为满足P87的四个属性：封闭+结合律+单位排列+逆排列
9.tips:从群的乘法表出发分析，可以很容易的定义和判别是否阿贝尔群，关于对角线对称。
10.由某个集合S生成的置换群G，定义是:由某个有限的集合S，S集合里面元素是一个个排列，定义一个G集合，
    里面元素是任意S里面的元素复合运算得到的结果（当然也是一个个排列）
11.魔方群：是一个置换群G，也叫做由Sx中的元素“生成”的置换群。
    X： 是魔方的 54 个面的集合，
    Sx：是一个排列的集合，让 R、L、U、D、F、B ∈ Sx 表示魔方的基本动作， R、L、U、D、F、B都是一个个排列
    置换群G = <R、L、U、D、F、B> ⊂ Sx 就称作魔方群（每一个状态，是由某一组操作来代表的）
12.对于群G，群G的order，符号|G|表示： 群元素的数量。 魔方群的|G| = 2^27*3^14*5^3*7^2*11
13.对于群的元素g，g的order，符号ord(g)表示：使得g^m=1 的最小的m（如果m存在的话）.
    魔方群中最大order为元素m = RU2D−1BD−1，其order为1260
14.柯西定理，用来判断元素g，g满足order是某个数，这样的g，是否存在。
    因此可以判断魔方群中某个元素g,g符合order为某个值，能判断这样的g是否能存在。
15.对于群G，群G由一个元素生成的，称为循环的群。
16.对于群G，和G的子群H，这样的数|G|/|H|， 称为index ，符号记为[G:H]。
17.对于群G，G的center，中心：center是一个G的子群，里面的元素z，对于任意的群G里面的元素g，z ∗ g = g ∗ z，换句话说可以左乘+右乘相等的
    具体集合定义为Z（G） = {z ∈ G | z ∗ g = g ∗ z，对于所有 g ∈ G}。
    trivial center：当子群Z（G）只有一个元素时，这个元素也就是最普通的单位元时，就称作平凡的。
    借此机会，对于群G，可以定义commutative：群G，如果G = Z（G），即G等于G的这个子群，则G称作交换的。
18.对于魔方群G，G是S₄₈（一个由48元素的任意排列，这样的排列为元素组成的群）的一个子群。
19.对于魔方群G，G的center就是集合Z(G) = {1, superflip}
    superflip已被人们所知道的一个是：
    superflip = R · L · F · B · U · D · R · L · F · B · U · F 2 · M R ·
    ·F 2 · U −1 · MR 2
    R · B2 · MR −1
    R · B2 · U · MR 2
    R · D
    = R · L · F · B · U · D · R · L · F · B · U · F 2 · R−1 ·
    ·L · D2 · F −1 · R2 · L2 · D2 · R · L−1 ·
    ·F 2 · D · R2 · L2 · D (34 quarter turns)（它是34次转动的一组操作）
    （这里MR 指的是右中间切片顺时针旋转 90 度（从右边的面来看））
    而且已被证明，最小转动次数的superflip是一下这个：
    R, R−1 , L, L−1 , U, U −1 , D, D−1 , B, B−1 , F, F −1
20.由魔方的两个2次操作组成的群H：H = 〈R^2, U^2〉,
    这个群的所有12个元素是：
    H = {1, R2 , R2 · U2 , R2 · U2 · R2 ,(R2 · U2 )^2 ,(R2 · U2 )^2 · R2 ,(R2 · U2 )^3 ,
        (R2 · U2 )^3 · R2 ,(R2 · U2 )4 ,(R2 · U2 )^4 · R2 ,(R2 · U2 )^5 ,(R2 · U2 )^5 · R2 }
    单位元满足：1 = （R2 · U2 )^6
21.对于群G，g、h是G中的元素，commutator of g,h：是一个G中的元素，记为[g,h]，[g,h] = g ∗ h ∗ g−1 ∗ h−1
    讲一个常识：先穿袜子再穿鞋，和，先穿鞋再穿袜子，不一样！！！
22.对于魔方群，Y commutator：[F, R−1 ] = F · R−1 · F−1 · R
    Z commutator：[F, R] = F · R · F−1 · R−1
23.关于魔方群的只改变魔方本身有限块的位置的定理：如果 x、y 是魔方的基本移动，与共享边的面相关联，则
    1.[x， y]^2 正好置换 3 个边块，不改变任何角块;
    2.[x， y]^3 正好置换 2 个角块，不置换任何边块。
24.对于群G，commutator subgroup of G:是一个G的子群，里面的元素是所有的commutator [g,h]，这样的commutator由G中的任意两个元素g,h生成。
    具体定义是：{[g, h] | g, h belong to G}
    有趣的事实：当commutator subgroup足够大时，基本上和魔方群是相差无几的。也就是说，任意魔方状态基本都通过一组commutator可以达到。
25.对于群G，derived series：是一个序列的子群：... ⊂ (G‘)‘ ⊂ G’ ⊂ G
    以此前提，对于群G，可以定义solvable 可解群：derived series代表的序列中，有一个群是只有一个元素的，该元素是恒等变换。
26.对于群G，g、h是G中的元素，conjugate of g by h 共轭:是一个G中的元素，记为g^h, g^h = h−1 ∗ g ∗ h
27.对于群G，g1、g2是G中的元素, two elements g1,g2 are conjugate: 是一种关系，
    需要满足：如果存在一个元素 h ∈ G，使得 g2= g1^h
    判断是否共轭也有一个柯西定理
28.对于群G，在等价关系“conjugation”下的 等价类的集合 G∗：是一个由等价类组成的集合，元素是一个个等价类???, 记为G∗。
    以此前提，对于群G，可以定义一个多项式generating polynomial  of the order function on  G  ：
     是一个多项式，变量是t，p G (t) = ∑c∈G∗ t^order(c)
29.对于群G，g是G中的一个元素，the conjugacy class of g in G :是一个集合，里面的元素由任意h通过conjugate运算得到，
    因为conjugate这个关系是等价关系来的，等价关系可以理解成等价类，由于某种原因???可以把群G分成若干个类，所以每一个conjugate的计算结果可以代表一个等价类。
    具体定义为：记为 Cl(g) 或 ClG (g)，Cl(g) = ClG (g)  = {h−1 ∗ g ∗ h | h ∈ G}
30.对于群G，X是一个群G的子集，G acts on X on the right:G和X的一个关系，需要满足：(这个定义的实际例子我觉得是G的元素分别作用在边块X1和角块X2上，所以要研究这样的作用在子集上的映射)
    1.属于 G 的每个 g元素，对应产生一个函数φ：X → X
    2.群 G 的恒等式 1 定义了 X → X 上的恒等式函数。
    3. 如果 g、h 属于 G，则复合φgh：X → X满足：φgh(x) = φh(φg(x))
  同样类似可以定义G acts on X on the left，唯一不同之处是第3点：
    3.如果 g、h 属于 G，则复合φgh：X → X满足：φgh(x) = φg(φh(x))
  以此为前提，可以定义某个action is transitive：action φ的一个可选性质。
    需要满足：如果对于属于 X 的每对 x、y 都有一个 g ∈ G，该g对应的动作φ满足 y = φ（x），称该g对应的动作φ为transitive的。
31.对于群G，设满足G acts on X的关系,  the orbit of x∈X under G
    :是一个X的子集，其中元素这样生成的，对于某个特定的X中的元素x，
    任意取一个G中的元素g，g对应的action φ作用在x上得到的所有结果，这个结果组成的集合就是orbit。
    具体定义：G ∗ x = {φg(x) | g ∈ G} ， 记为G ∗ x
    对于魔方群G，X指的是魔方上的绝对位置，位置当作元素，这样的集合orbit其实可以分成两个集合V，E，两个块的绝对位置的集合
        这两个集合V，E仍然分别满足定义G ∗ x = {φg(x) | g ∈ G}，
        也就是仍然满足V，E中的元素经过φg映射后，仍然分别在V,E集合里面。
32.对于群G，集合X，设满足G acts on X的关系，x是X中的一个元素，stablizer：是一个G中元素的集合G2，G2里面的任意元素g，
    g需要满足条件是：φg作用在x后，结果仍然是x。
    具体定义：stabG (x) = Gx = {g ∈ G | φg (x) = x} ， 记为stabG (x) 或 Gx
33.对于群G，集合X这时取为G本身，即X=G，假设满足G acts on X的关系，G acts on X的关系中函数φ给出了固定的定义是 g ∗ x ∗ g−1
     ，centralizer of x in G：是一个G中元素的集合G2，首先我们知道stabG (x) = {g ∈ G | g ∗ x = x ∗ g}，这个集合
     stabG (x)就是我们的结果G2，记为CG(x)，CG(x)=stabG (x)。
34.对于魔方群G，g是G的元素，H集合={1,D,D^2,D^3} left coset of H:是一个作用左乘结果的集合，g左乘H中全体元素的结果，
    这些结果的集合就是left coset of H。
35.subset ： 子集合
36.对于群G，H是G的子群，g是G的元素， left coset of H in G: 是一个G的子集， 形式是这样的g * H，换句话说，就是
    选定g元素后，g左乘H中全体元素得到的结果，这些结果的集合就是 left coset of H in G。
    全体的 left coset of H in G集合（每个不同之处在于g的选取），再拼成的一个大集合，记为G/H。
    类似的，全体的 left coset of H in G集合（每个不同之处在于g的选取），再拼成的一个大集合，记为G\H。左右斜杠不同
37.对于群G，H是G的子群，拉格朗日定理：描述left coset of H in G集合的元素数量，直接可以用G的数量，H的数量计算出来。
38.对于群G，H是G的子群，C是一个G的子集a left coset of H in G, g是G中的元素
     coset representative of C：是群G中的一个元素g，g满足：C= g * H。 其实就是left coset of H in G定义中选取的某个g元素。
    全体 coset representatives，也可以称作全体coset representatives of G/H ：是一个G的子集，里面的元素比如有m个的话：x1,x2,...,xm , 这m个元素需要满足：
        G/H = {x1*H,x2*H,...,xm*H} , 还需要满足：x1*H , x2*H ,..., xm*H 这m个G的子集是互不相交的。
39.定理5.11.2: 全体coset representatives of G/H 可以构造出完整的群G。G = U(s∈S) s*H , 即一个并集，“每一个集合”是
    全体 coset representatives 某一项xk，xk右乘集合H得到的所有结果，这些所有结果的集合就是上面并集里的“每一个集合”。
40.对于群G1,群G2,映射f:G1→G2,*₁是群G1的运算，*₂是群G2的运算，f是  homomorphism 同态:映射f的一种可选性质，
    描述是G1和G2之间的一种关系，
    对于任意a,b∈ G1 , G1和G2需要满足：f(a *₁ b) = f(a) *₂ F(b) 。 注意：记号·和“并列写法”也可以代表* 。
41.对于群G1,群G2,映射f:G1→G2，f满足homomorphism， image of f:是群G2的一个子群 ,
    具体定义：f (G1 ) = {g ∈ G2 | g = f (x), for some x ∈ G1 }，换句话说，元素形式是g∈ G2,
    需要满足：能找到至少一个x ∈ G1 ，x通过映射f映射后是g。
    , 记为im(f) 。
42.对于群G1，群G2 , G1 embeds(or injects) into G2：是G1和G2之间的一种关系，需要满足：能找到一个映射f:G1→ G2, 映射f是单射的。
    也就是相同结果推相同原像。
43.对于群G1,群G2,映射f:G1→G2，f满足homomorphism，  isomorphism 同构:f的一种可选性质，f需要满足：映射f是双射的。
    以此为前提，ismorphic:G1和G2的一种关系，满足f是isomorphism的， 记为G1≃G2。
    以此为前提，如果G1=G2，automorphism 自同构：G1和G2的一种关系。
44.引理9.2.1:描述了G acts on X ↔ 存在同态的映射f， f满足：是一个这样类型的映射G→S×(这个集合指的是X中的元素的所有排列的集合，
    每一个排列可以用一个向量来表示)， 然后具体定义是将G中的任意元素g，映射到φg
    (这个φg是一个X→X类型的映射，作用到X里元素结果封闭在X里)
45.

进度：P172/329 下一个里程碑218开始研究可解的魔方状态 224魔方第二基本定理已经可以开始做lean了 后面还有平方群的定理 跳过14章太难了 多种魔方解法



看完一二基本定理的证明后就看TW算法，书里面只有一页介绍，所以要看北师大老师的视频
然后再看这里项目的内容看看如何形式化，有哪些相关的
看看能否形式化出更多书里已看的定理，还有视频看到的算法
